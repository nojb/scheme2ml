open Datum

module M = Map.Make (String)

(* mangle : string -> string
 * 
 * This function comes up with new names for the
 * Scheme variables, since the naming rules for Ocaml
 * are more stringent. It looks at each char in turn.
 * If it is an alphabetic or numeric character, it
 * is left alone. Otherwise, it is replaced by the
 * string "__C", where C is the ascii code of the
 * character in question. Finally we prepend the
 * string "__" at the beginning (This takes care for
 * example of the Scheme identifiers that start with
 * uppercase, something forbidden in Ocaml) *)

let mangle_count = ref 0

let mangle s =
  let count = !mangle_count in
  mangle_count := !mangle_count + 1;
  let alphanumeric c =
    c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
  in
  let string_to_list s =
    let l = String.length s in
    let rec loop i = if i >= l then [] else s.[i] :: loop (i + 1) in loop 0
  in
  let mangle_char c =
    if alphanumeric c then String.make 1 c
    else "_" ^ string_of_int (Char.code c)
  in
  String.concat ""
    (("_" ^ string_of_int count ^ "_") ::
     List.map mangle_char (string_to_list s))

let new_var name =
  {Emit.name = mangle name; Emit.mut = false; Emit.referenced = false;
   Emit.closure = false; Emit.varargs = false; Emit.arity = 0}

let new_var_no_mangle name clos arity =
  {Emit.name = name; Emit.mut = false; Emit.referenced = false;
   Emit.closure = clos; Emit.varargs = false; Emit.arity = arity}

(* analyze_program : Emit.binding M.t -> Scheme.t -> Emit.t
 *
 * This is the entry to the syntax analysis phase of the compiler.
 * We want to leave as much work as possible to the Ocaml compiler,
 * so we take the sequence of top-level declarations and commands
 * and we make them into one big (begin ...) form. The only tricky
 * point is how do we deal with (define ...) forms. Here is an
 * example:
 *   
 *   (define x (lambda () 3))
 *   (display (x))
 *
 * should be translated into
 *
 *   (begin
 *     (letrec ((x (lambda () 3)))
 *        (display (x))))
 *
 * (the letrec is necessary in case the definitions contain recursive
 * functions).
 *
 * When detecting (define ...) forms, there are two cases:
 *    
 *    (define x ...)
 *    (define (x ...) ...)
 *
 * otherwise, we just take the corresponding scheme expression and tack
 * it in at the end of the sequence. *)

let parse_define = function
  | Dlist ((Dsym "define") :: (Dsym _ as a) :: e :: []) ->
      Some (a, e)
  | Dlist ((Dsym "define") :: (Dlist (Dsym _ as a :: args)) :: body) ->
      Some (a, Dlist (Dsym "lambda" :: Dlist args :: body))
  | Dlist ((Dsym "define") :: _) ->
      failwith "bad syntax in (define)"
  | _ -> None

type d =
  | Def of (datum * datum) list
  | Oth of datum

let rec analyze_program x =
  (* returns (defines, rest) *)
  let loop x =
    let rec extract_defines found = function
      | [] -> found
      | a :: b ->
          match parse_define a with
          | None -> extract_defines (Oth a :: found) b
          | Some z ->
              let rec loop zs = function
                (* zs is reversed *)
                | [] -> Def zs :: found
                | a :: b ->
                    match parse_define a with
                    | None -> extract_defines (Oth a :: Def zs :: found) b
                    | Some z' -> loop (z' :: zs) b
              in
              loop [z] b
    in
    let defs = extract_defines [] x in
    (* reversed *)
    let create_letrec zs rest =
      let bindings =
        List.fold_left
          (fun rest (n, e) ->
            (* bindings + body *)
            Dlist (n :: e :: []) :: rest)
          [] zs
      in
      [Dlist (Dsym "letrec" :: Dlist bindings :: rest)]
    in
    List.fold_left
      (fun rest def ->
         match def with
         | Def zs -> create_letrec zs rest
         | Oth z -> z :: rest) [] defs
  in
  let x' = Dlist (Dsym "begin" :: loop x) in
  let syntax_forms =
    [ "begin", analyze_begin;
      "lambda", analyze_lambda;
      (* ("define", analyze_define); *)
      "set!", analyze_set;
      "quote", analyze_quote;
      (* "quasiquote", analyze_quasiquote;*)
      "if", analyze_alternative;
      "let", analyze_let;
      "let*", analyze_let_star;
      "letrec", analyze_letrec;
      (*"cond", analyze_cond;*)
      "and", analyze_and;
      "or", analyze_or;
      (*"case", analyze_case;*)
      "delay", analyze_delay;
      (*"do", analyze_do; *)
      "time", analyze_time ]
  in
  let env =
    List.fold_left
      (fun env (name, varargs, impls) ->
         M.add name (Emit.Builtin (varargs, impls, name)) env)
      M.empty Builtins.builtins
  in
  let env =
    List.fold_left (fun env (name, impl) -> M.add name (Emit.Syntax impl) env)
      env syntax_forms
  in
  Printf.eprintf "DEBUG:\n%a\n%!" pp_datum x';
  analyze 0 env x'

and analyze qq env x =
  match x with
  | Dint _ | Dbool _ | Dchar _ | Dstring _
  | Dlist [] | Dvec _ -> Emit.Quote x
  | Dsym s ->
      begin try
        match M.find s env with
        | Emit.Variable var as v ->
            var.Emit.referenced <- true; Emit.Reference v
        | _ as v -> Emit.Reference v
      with Not_found -> failwith ("unknown identifier: " ^ s) end
  | Dlist (x :: xs) -> analyze_cons qq env x xs
  | Ddot _ -> failwith "bad syntax"

and analyze_cons qq env x xs =
  match x with
  | Dsym s ->
      begin try
        match M.find s env with
        | Emit.Syntax syn -> syn qq env xs
        | _ as v ->
            Emit.Application
              (Emit.Reference v, List.map (analyze qq env) xs)
      with Not_found -> failwith ("unknown identifier: " ^ s)
      end
  | _ ->
      Emit.Application (analyze qq env x, List.map (analyze qq env) xs)

and analyze_begin qq env xs =
  Emit.Begin (List.map (analyze qq env) xs)

and analyze_quote qq env = function
  | a :: [] -> Emit.Quote a
  | _ -> failwith "bad syntax in (quote)"

and analyze_body qq env xs =
  let rec loop = function
    | Dlist (Dsym "define" :: a :: b) :: xs ->
        begin match a with
        | Dlist (Dsym _ as name :: args) ->
            let x', xs' = loop xs in
            (Dlist
              (name :: Dlist
                (Dsym "lambda" :: Dlist args :: b) :: [])) :: x', xs'
        | Dsym _ as name ->
            let x', xs' = loop xs in
            Dlist (name :: b) :: x', xs'
        | _ -> failwith "bad syntax in (define)"
        end
    | Dlist (Dsym "begin" :: defs) :: xs ->
        begin match loop defs with
        | x', [] ->
            let x'', xs'' = loop xs in
            List.append x' x'', xs''
        | [], xs' ->
            [], List.append xs' xs
        | _ -> failwith "bad syntax in (begin)"
        end
    | _ as x -> [], x
  in
  let x, xs = loop xs in
  match x with
  | [] -> Emit.Begin (List.map (analyze qq env) xs)
  | _ ->
      analyze qq env (Dlist (Dsym "letrec" :: Dlist x :: xs))

and analyze_let_star qq env = function
  | Dlist bindings :: body ->
      analyze_let qq env (List.fold_right
        (fun binding body ->
          Dlist [binding] :: Dlist (Dsym "let" :: body) :: [] )
        bindings (Dlist [] :: body))
  | _ -> failwith "bad syntax in (let*)"

and analyze_letrec qq env = function
  | Dlist bindings :: body ->
      let variables, inits = List.split
        (List.map
          (function
            | Dlist [Dsym variable1; init1] -> (variable1, init1)
            | _ -> failwith "bad syntax in (letrec)") bindings) in
      let variables' = List.map new_var variables in
      let env' =
        List.fold_left2
          (fun env variable variable' ->
            M.add variable (Emit.Variable variable') env)
          env variables variables' in
      let inits' = List.map (analyze qq env') inits in
      List.iter2
        (fun var' init ->
           match init with
             Emit.Lambda (varargs, args, _) ->
               var'.Emit.closure <- true;
               var'.Emit.varargs <- varargs;
               var'.Emit.arity <- List.length args
           | _ -> ())
        variables' inits';
      Emit.Let (variables', inits', analyze_body qq env' body)
  | _ -> failwith "bad syntax in (letrec)"

and analyze_let qq env = function
  | (Dsym _ as v) :: Dlist bindings :: body -> (* named let *)
      let binding_names, binding_values =
        List.fold_right
          (fun binding (names, values) ->
            match binding with
            | Dlist [Dsym _ as v; e] -> v :: names, e :: values
            | _ -> failwith "bad syntax in (let)")
          bindings ([], []) in
      analyze_letrec qq env
        [Dlist
          [Dlist
            [v; Dlist (Dsym "lambda" :: Dlist binding_names :: body)]];
            Dlist (v :: binding_values)]
  | Dlist bindings :: body ->
      let variables, inits =
        List.split
          (List.map
            (function
              | Dlist [Dsym variable1; init1] -> (variable1, analyze qq env init1)
              | _ -> failwith "bad syntax in (let)") bindings) in
      let variables' = List.map new_var variables in
      let env' =
        List.fold_left2
          (fun env variable variable' ->
             M.add variable (Emit.Variable variable') env)
          env variables variables'
      in
      Emit.Let (variables', inits, analyze_body qq env' body)
  | _ -> failwith "bad syntax in (let)"

and analyze_set qq env = function
  | Dsym name :: exp :: [] ->
      begin try
        match M.find name env with
        | Emit.Variable var ->
            var.Emit.mut <- true; Emit.Set (var, analyze qq env exp)
        | Emit.Syntax _ -> failwith "cannot! a syntax"
        | Emit.Builtin (_, _, _) -> failwith "cannot set! a builtin"
      with Not_found -> failwith "cannot set! an undefined variable" end
  | _ -> failwith "bad syntax in set!"

and analyze_lambda qq env = function
  | Dlist args :: body ->

      let args = List.map
        (function Dsym arg -> arg | _ -> failwith "bad syntax in (lambda)")
        args in
      let args' = List.map new_var args in
      let env' =
        List.fold_left2
          (fun env arg arg' ->
            M.add arg (Emit.Variable arg') env) env args args' in
      Emit.Lambda (false, args', analyze_body qq env' body)

  | Ddot (args, Dsym a) :: body ->
      let args = List.map
        (function Dsym arg -> arg | _ -> failwith "bad syntax in (lambda)") args in
      let args = List.append args [a] in
      let args' = List.map new_var args in
      let env' =
        List.fold_left2
          (fun env arg arg' -> M.add arg (Emit.Variable arg') env)
            env args args' in
      Emit.Lambda (true, args', analyze_body qq env' body)

  | Dsym name :: body ->
      let arg' = new_var name in
      let env' = M.add name (Emit.Variable arg') env in
      Emit.Lambda (true, [arg'], analyze_body qq env' body)

  | _ -> failwith "bad syntax in (lambda)"

and analyze_alternative qq env = function
  | condition :: iftrue :: [] ->
      Emit.If
        (analyze qq env condition, analyze qq env iftrue,
          Emit.Quote (Dlist [])) (* Should be Svoid? *)
  | condition :: iftrue :: iffalse :: [] ->
      Emit.If
        (analyze qq env condition, analyze qq env iftrue,
         analyze qq env iffalse)
  | _ -> failwith "analyze_alternative: bad syntax in (if)"

  (*
and analyze_cond qq env cdr =
  let rec loop clauses =
    match clauses with
      Scheme.Scons
        {Scheme.car =
           Scheme.Scons
             {Scheme.car = Scheme.Symbol "else"; Scheme.cdr = expressions};
         Scheme.cdr = Scheme.Snil} ->
        Emit.Begin (map_to_list (analyze qq env) expressions)
    | Scheme.Scons {Scheme.car = clause1; Scheme.cdr = clauses} ->
        analyze_clause clause1 clauses
    | Scheme.Snil -> Emit.Quote Scheme.Void
    | _ -> failwith "bad syntax in (cond)"
  and analyze_clause clause1 clauses =
    match clause1 with
      Scheme.Scons {Scheme.car = test; Scheme.cdr = Scheme.Snil} ->
        let v = new_var_no_mangle "test" false 0 in
        let v' = Emit.Variable v in
        Emit.Let
          ([v], [analyze qq env test],
           Emit.If (Emit.Reference v', Emit.Reference v', loop clauses))
    | Scheme.Scons
        {Scheme.car = test;
         Scheme.cdr =
           Scheme.Scons
             {Scheme.car = Scheme.Symbol "=>";
              Scheme.cdr =
                Scheme.Scons
                  {Scheme.car = expression; Scheme.cdr = Scheme.Snil}}} ->
        let v = new_var_no_mangle "test" false 0 in
        let v' = Emit.Variable v in
        Emit.Let
          ([v], [analyze qq env test],
           Emit.If
             (Emit.Reference v',
              Emit.Application
                (analyze qq env expression, [Emit.Reference v']),
              loop clauses))
    | Scheme.Scons {Scheme.car = test; Scheme.cdr = expressions} ->
        Emit.If
          (analyze qq env test,
           Emit.Begin (map_to_list (analyze qq env) expressions),
           loop clauses)
    | _ -> failwith "bad syntax in (cond)"
  in
  loop cdr
  *)

and analyze_and qq env = function
  | [] -> Emit.Quote (Dbool true)
  | [x] -> analyze qq env x
  | x :: xs ->
      let v = new_var_no_mangle "test" false 0 in
      let v' = Emit.Variable v in
      Emit.Let ([v], [analyze qq env x],
        Emit.If (Emit.Reference v', analyze_and qq env xs,
          Emit.Reference v'))

and analyze_or qq env = function
  | [] -> Emit.Quote (Dbool false)
  | [x] -> analyze qq env x
  | x :: xs ->
      let v = new_var_no_mangle "test" false 0 in
      let v' = Emit.Variable v in
      Emit.Let ([v], [analyze qq env x],
        Emit.If (Emit.Reference v', Emit.Reference v',
          analyze_or qq env xs))

  (*
and analyze_quasiquote qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil} ->
      analyze_quasiquote_aux (qq + 1) env x
  | _ -> failwith "bad syntax in (quasiquote)"

and analyze_quasiquote_aux qq env cdr =
  let append =
    Emit.Reference
      (Emit.Builtin
         (Some (0, "Scheme.append"), [2, "Scheme.append2"], "append"))
  in
  let cons =
    Emit.Reference (Emit.Builtin (None, [2, "Scheme.cons"], "cons"))
  in
  match cdr with
    Scheme.Scons
      {Scheme.car = Scheme.Symbol "unquote";
       Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil}} ->
      if qq = 1 then analyze (qq - 1) env x
      else
        Emit.Application
          (cons,
           [Emit.Quote (Scheme.Symbol "unquote");
            analyze_quasiquote_list (qq - 1) env x])
  | Scheme.Scons
      {Scheme.car = Scheme.Symbol "unquote-splicing"; Scheme.cdr = _} ->
      failwith "(unquote-splicing) not allowed here"
  | Scheme.Scons
      {Scheme.car = Scheme.Symbol "quasiquote";
       Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil}} ->
      Emit.Application
        (cons,
         [Emit.Quote (Scheme.Symbol "quasiquote");
          analyze_quasiquote_list (qq + 1) env x])
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} ->
      Emit.Application
        (append,
         [analyze_quasiquote_list qq env a; analyze_quasiquote_aux qq env b])
  | _ -> Emit.Quote cdr

and analyze_quasiquote_list qq env car =
  let append =
    Emit.Reference
      (Emit.Builtin
         (Some (0, "Scheme.append"), [2, "Scheme.append2"], "append"))
  in
  let list =
    Emit.Reference (Emit.Builtin (Some (0, "Scheme.list"), [], "list"))
  in
  let cons =
    Emit.Reference (Emit.Builtin (None, [2, "Scheme.cons"], "cons"))
  in
  match car with
    Scheme.Scons
      {Scheme.car = Scheme.Symbol "unquote";
       Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil}} ->
      if qq = 1 then Emit.Application (list, [analyze (qq - 1) env x])
      else
        Emit.Application
          (list,
           [Emit.Application
              (cons,
               [Emit.Quote (Scheme.Symbol "unquote");
                analyze_quasiquote_list (qq - 1) env x])])
  | Scheme.Scons
      {Scheme.car = Scheme.Symbol "unquote-splicing";
       Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil}} ->
      if qq = 1 then analyze (qq - 1) env x
      else
        Emit.Application
          (list,
           [Emit.Application
              (cons,
               [Emit.Quote (Scheme.Symbol "unquote-splicing");
                analyze_quasiquote_list (qq - 1) env x])])
  | Scheme.Scons
      {Scheme.car = Scheme.Symbol "quasiquote";
       Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = Scheme.Snil}} ->
      Emit.Application
        (list,
         [Emit.Application
            (cons,
             [Emit.Quote (Scheme.Symbol "quasiquote");
              analyze_quasiquote_list (qq + 1) env x])])
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} ->
      Emit.Application
        (list,
         [Emit.Application
            (append,
             [analyze_quasiquote_list qq env a;
              analyze_quasiquote_aux qq env b])])
  | _ -> Emit.Quote (Scheme.Scons {Scheme.car = car; Scheme.cdr = Scheme.Snil})

and analyze_case qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = key; Scheme.cdr = clauses} ->
      let help_last emitted clause =
        match clause with
          Scheme.Scons
            {Scheme.car = Scheme.Symbol "else"; Scheme.cdr = body} ->
            begin try
              Emit.Case
                (analyze qq env key, List.rev emitted,
                 Emit.Begin (map_to_list (analyze qq env) body))
            with NotAList -> failwith "bad syntax in (case)"
            end
        | Scheme.Scons {Scheme.car = cond; Scheme.cdr = body} ->
            begin try
              let emitted =
                (map_to_list (fun x -> x) cond,
                 Emit.Begin (map_to_list (analyze qq env) body)) ::
                emitted
              in
              Emit.Case
                (analyze qq env key, List.rev emitted, Emit.Quote Scheme.Void)
            with NotAList -> failwith "bad syntax in (case)"
            end
        | _ -> failwith "bad syntax in (case)"
      in
      let help emitted clause =
        match clause with
          Scheme.Scons {Scheme.car = cond; Scheme.cdr = body} ->
            begin try
              (map_to_list (fun x -> x) cond,
               Emit.Begin (map_to_list (analyze qq env) body)) ::
              emitted
            with NotAList -> failwith "bad syntax in (case)"
            end
        | _ -> failwith "bad syntax in (case)"
      in
      fold_last_cons help help_last (Emit.Quote Scheme.Void) [] clauses
  | Scheme.Snil -> Emit.Quote Scheme.Void
  | _ -> failwith "bad syntax in (case)"
  *)

and analyze_delay qq env = function
  | e :: [] -> Emit.Delay (analyze qq env e)
  | _ -> failwith "bad syntax in (delay)"

  (*
and analyze_do qq env cdr =
  match cdr with
    Scheme.Scons
      {Scheme.car = variables;
       Scheme.cdr = Scheme.Scons {Scheme.car = test; Scheme.cdr = body}} ->
      let parse_var variable =
        match variable with
          Scheme.Scons
            {Scheme.car = Scheme.Symbol var as v;
             Scheme.cdr =
               Scheme.Scons {Scheme.car = init; Scheme.cdr = Scheme.Snil}} ->
            var, init, v
        | Scheme.Scons
            {Scheme.car = Scheme.Symbol var;
             Scheme.cdr =
               Scheme.Scons
                 {Scheme.car = init;
                  Scheme.cdr =
                    Scheme.Scons
                      {Scheme.car = step; Scheme.cdr = Scheme.Snil}}} ->
            var, init, step
        | _ -> failwith "bad syntax in (do)"
      in
      let head = map_to_list parse_var variables in
      let vars = List.map (fun (var, _, _) -> var) head in
      let vars' = List.map new_var vars in
      let env' =
        List.fold_left2
          (fun env var var' -> M.add var (Emit.Variable var') env) env vars
          vars'
      in
      let inits = List.map (fun (_, init, _) -> analyze qq env init) head in
      let steps = List.map (fun (_, _, step) -> analyze qq env' step) head in
      let body = map_to_list (analyze qq env') body in
      begin match test with
        Scheme.Scons {Scheme.car = test; Scheme.cdr = iftrue} ->
          let test = analyze qq env' test in
          let iftrue = map_to_list (analyze qq env') iftrue in
          let loop = new_var_no_mangle "loop" true (List.length vars) in
          let loop' = Emit.Variable loop in
          Emit.Let
            ([loop],
             [Emit.Lambda
                (false, vars',
                 Emit.If
                   (test, Emit.Begin iftrue,
                    Emit.Begin
                      [Emit.Begin body;
                       Emit.Application (Emit.Reference loop', steps)]))],
             Emit.Application (Emit.Reference loop', inits))
      | Scheme.Snil ->
          let loop = new_var_no_mangle "loop" true (List.length vars) in
          let loop' = Emit.Variable loop in
          Emit.Let
            ([loop],
             [Emit.Lambda
                (false, vars',
                 Emit.Begin
                   [Emit.Begin body;
                    Emit.Application (Emit.Reference loop', steps)])],
             Emit.Application (Emit.Reference loop', inits))
      | _ -> failwith "bad syntax in (do)"
      end
  | _ -> failwith "bad syntax in (do)"
  *)

and analyze_time qq env = function
  | e :: [] ->
      Emit.Time (analyze qq env e)
  | _ -> failwith "bad syntax in (time)"
