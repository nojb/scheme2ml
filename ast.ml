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

exception NotAList

let rec iter_cons f cons =
  match cons with
    Scheme.Scons {Scheme.car = a; Scheme.cdr = b} -> f a; iter_cons f b
  | Scheme.Snil -> ()
  | _ -> raise NotAList

let rec fold_left_cons f z cons =
  match cons with
    Scheme.Snil -> z
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} -> fold_left_cons f (f z a) b
  | _ -> raise NotAList

let rec fold_last_cons f f_last f_nil z cons =
  match cons with
    Scheme.Scons {Scheme.car = a; Scheme.cdr = Scheme.Snil} -> f_last z a
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} ->
      fold_last_cons f f_last f_nil (f z a) b
  | Scheme.Snil -> f_nil
  | _ -> raise NotAList

let rec fold_right_cons f cons z =
  match cons with
    Scheme.Snil -> z
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = Scheme.Snil} -> f a z
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} ->
      f a (fold_right_cons f b z)
  | _ -> raise NotAList

let rec cons_append cons1 cons2 =
  match cons1 with
    Scheme.Scons {Scheme.car = a; Scheme.cdr = Scheme.Snil} ->
      Scheme.Scons {Scheme.car = a; Scheme.cdr = cons2}
  | Scheme.Snil -> cons2
  | Scheme.Scons {Scheme.car = a; Scheme.cdr = b} ->
      Scheme.Scons {Scheme.car = a; Scheme.cdr = cons_append b cons2}
  | _ -> invalid_arg "cons_append"

let rec map_to_list f cons =
  match cons with
    Scheme.Snil -> []
  | Scheme.Scons cons -> f cons.Scheme.car :: map_to_list f cons.Scheme.cdr
  | _ -> raise NotAList

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

(* type d =
    Def of (Scheme.t * Scheme.t) list
  | Oth of Scheme.t *)

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
        (* List.fold_left
          (fun rest (n, e) ->
             (* bindings + body *)
             Scheme.Scons
               {Scheme.car =
                 Scheme.Scons
                   {Scheme.car = n;
                    Scheme.cdr =
                      Scheme.Scons {Scheme.car = e; Scheme.cdr = Scheme.Snil}};
                Scheme.cdr = rest})
          Scheme.Snil zs*)
      in
      [Dlist (Dsym "letrec" :: Dlist bindings :: rest)]
      (* Scheme.Scons
        {Scheme.car =
          Scheme.Scons
            {Scheme.car = Scheme.Symbol "letrec";
             Scheme.cdr =
               Scheme.Scons {Scheme.car = bindings; Scheme.cdr = rest}};
         Scheme.cdr = Scheme.Snil} *)
    in
    List.fold_left
      (fun rest def ->
         match def with
         | Def zs -> create_letrec zs rest
         | Oth z -> z :: rest) [] defs
  in
  let x' = Dlist (Dsym "begin" :: loop x) in
  let syntax_forms =
    ["begin", analyze_begin; "lambda", analyze_lambda;
     (*  ("define", analyze_define); *)
     "set!", analyze_set;
     "quote", analyze_quote; "quasiquote", analyze_quasiquote;
     "if", analyze_alternative; "let", analyze_let; "let*", analyze_let_star;
     "letrec", analyze_letrec; "cond", analyze_cond; "and", analyze_and;
     "or", analyze_or; "case", analyze_case; "delay", analyze_delay;
     "do", analyze_do; "time", analyze_time]
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
  Emit.Quote Scheme.Snil
  (* analyze 0 env x' *)

and analyze qq env x =
  match x with
  | Scheme.Snum _ | Scheme.Strue | Scheme.Sfalse
  | Scheme.Snil | Scheme.Char _ | Scheme.String _ | Scheme.Vector _ ->
      Emit.Quote x
  | Scheme.Symbol s ->
      begin try
        let v = M.find s env in
        match v with
          Emit.Variable var as v ->
            var.Emit.referenced <- true; Emit.Reference v
        | _ -> Emit.Reference v
      with Not_found -> failwith ("unknown identifier: " ^ s)
      end
  | Scheme.Scons cons -> analyze_cons qq env cons.Scheme.car cons.Scheme.cdr
  | _ -> failwith "Ast.analyze: unhandled scheme datum"

and analyze_cons qq env car cdr =
  match car with
    Scheme.Symbol s ->
      begin try
        match M.find s env with
          Emit.Syntax syn -> syn qq env cdr
        | v ->
            Emit.Application
              (Emit.Reference v, map_to_list (analyze qq env) cdr)
      with Not_found -> failwith ("unknown identifier: " ^ s)
      end
  | _ ->
      Emit.Application (analyze qq env car, map_to_list (analyze qq env) cdr)
and analyze_begin qq env cdr =
  try Emit.Begin (map_to_list (analyze qq env) cdr) with
    NotAList -> failwith "bad syntax in (begin)"
and analyze_quote qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = a; Scheme.cdr = Scheme.Snil} -> Emit.Quote a
  | _ -> failwith "bad syntax in (quote)"
and analyze_body qq env cdr =
  let rec loop cdr =
    match cdr with
      Scheme.Scons
        {Scheme.car =
           Scheme.Scons
             {Scheme.car = Scheme.Symbol "define";
              Scheme.cdr = Scheme.Scons {Scheme.car = a; Scheme.cdr = b}};
         cdr = xs} ->
        begin match a with
          Scheme.Scons
            {Scheme.car = Scheme.Symbol _ as name; Scheme.cdr = args} ->
            let (x', xs') = loop xs in
            Scheme.Scons
              {Scheme.car =
                Scheme.Scons
                  {Scheme.car = name;
                   Scheme.cdr =
                     Scheme.Scons
                       {Scheme.car =
                         Scheme.Scons
                           {Scheme.car = Scheme.Symbol "lambda";
                            Scheme.cdr =
                              Scheme.Scons
                                {Scheme.car = args; Scheme.cdr = b}};
                        Scheme.cdr = Scheme.Snil}};
               Scheme.cdr = x'},
            xs'
        | Scheme.Symbol _ as name ->
            let (x', xs') = loop xs in
            Scheme.Scons
              {Scheme.car = Scheme.Scons {Scheme.car = name; Scheme.cdr = b};
               Scheme.cdr = x'},
            xs'
        | _ -> failwith "bad syntax in (define)"
        end
    | Scheme.Scons
        {Scheme.car =
           Scheme.Scons
             {Scheme.car = Scheme.Symbol "begin"; Scheme.cdr = defs};
         Scheme.cdr = xs} ->
        begin match loop defs with
          x', Scheme.Snil ->
            let (x'', xs'') = loop xs in
            cons_append x' x'', xs''
        | Scheme.Snil, xs' -> Scheme.Snil, cons_append xs' xs
        | _ -> failwith "bad syntax in (begin)"
        end
    | x -> Scheme.Snil, x
  in
  let (x, xs) = loop cdr in
  match x with
    Scheme.Snil -> Emit.Begin (map_to_list (analyze qq env) xs)
  | _ ->
      analyze qq env
        (Scheme.Scons
           {Scheme.car = Scheme.Symbol "letrec";
            Scheme.cdr = Scheme.Scons {Scheme.car = x; Scheme.cdr = xs}})
and analyze_let_star qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = bindings; Scheme.cdr = body} ->
      let rec loop bindings =
        match bindings with
          Scheme.Snil ->
            Scheme.Scons {Scheme.car = Scheme.Snil; Scheme.cdr = body}
        | Scheme.Scons {Scheme.car = binding1; Scheme.cdr = bindings} ->
            Scheme.Scons
              {Scheme.car =
                Scheme.Scons {Scheme.car = binding1; Scheme.cdr = Scheme.Snil};
               Scheme.cdr =
                 Scheme.Scons
                   {Scheme.car =
                     Scheme.Scons
                       {Scheme.car = Scheme.Symbol "let";
                        Scheme.cdr = loop bindings};
                    Scheme.cdr = Scheme.Snil}}
        | _ -> failwith "bad syntax in (let*)"
      in
      analyze_let qq env (loop bindings)
  | _ -> failwith "bad syntax in (let*)"
and analyze_letrec qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = bindings; Scheme.cdr = body} ->
      let rec loop bindings =
        match bindings with
          Scheme.Snil -> []
        | Scheme.Scons {Scheme.car = binding1; Scheme.cdr = bindings} ->
            begin match binding1 with
              Scheme.Scons
                {Scheme.car = Scheme.Symbol variable1;
                 Scheme.cdr =
                   Scheme.Scons
                     {Scheme.car = init1; Scheme.cdr = Scheme.Snil}} ->
                (variable1, init1) :: loop bindings
            | _ -> failwith "bad syntax in (letrec)"
            end
        | _ -> failwith "bad syntax in (letrec)"
      in
      let (variables, inits) = List.split (loop bindings) in
      let variables' = List.map new_var variables in
      let env' =
        List.fold_left2
          (fun env variable variable' ->
             M.add variable (Emit.Variable variable') env)
          env variables variables'
      in
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
and analyze_let qq env cdr =
  match cdr with
    Scheme.Scons
      {Scheme.car = Scheme.Symbol _ as v;
       Scheme.cdr = Scheme.Scons {Scheme.car = bindings; Scheme.cdr = body}} ->
      let help binding (names, values) =
        match binding with
          Scheme.Scons
            {Scheme.car = Scheme.Symbol _ as v;
             Scheme.cdr =
               Scheme.Scons {Scheme.car = e; Scheme.cdr = Scheme.Snil}} ->
            Scheme.Scons {Scheme.car = v; Scheme.cdr = names},
            Scheme.Scons {Scheme.car = e; Scheme.cdr = values}
        | _ -> failwith "bad syntax in (let)"
      in
      let (binding_names, binding_values) =
        fold_right_cons help bindings (Scheme.Snil, Scheme.Snil)
      in
      analyze_letrec qq env
        (Scheme.Scons
           {Scheme.car =
             Scheme.Scons
               {Scheme.car =
                 Scheme.Scons
                   {Scheme.car = v;
                    Scheme.cdr =
                      Scheme.Scons
                        {Scheme.car =
                          Scheme.Scons
                            {Scheme.car = Scheme.Symbol "lambda";
                             Scheme.cdr =
                               Scheme.Scons
                                 {Scheme.car = binding_names;
                                  Scheme.cdr = body}};
                         Scheme.cdr = Scheme.Snil}};
                Scheme.cdr = Scheme.Snil};
            Scheme.cdr =
              Scheme.Scons
                {Scheme.car =
                  Scheme.Scons
                    {Scheme.car = Scheme.Symbol "loop";
                     Scheme.cdr = binding_values};
                 Scheme.cdr = Scheme.Snil}})
  | Scheme.Scons {Scheme.car = bindings; Scheme.cdr = body} ->
      (* bindings : list (string * Emit.t) *)
      let rec loop bindings =
        match bindings with
          Scheme.Snil -> []
        | Scheme.Scons {Scheme.car = binding1; Scheme.cdr = bindings} ->
            begin match binding1 with
              Scheme.Scons
                {Scheme.car = Scheme.Symbol variable1;
                 Scheme.cdr =
                   Scheme.Scons
                     {Scheme.car = init1; Scheme.cdr = Scheme.Snil}} ->
                (variable1, analyze qq env init1) :: loop bindings
            | _ -> failwith "bad syntax in (let)"
            end
        | _ -> failwith "bad syntax in (let)"
      in
      let (variables, inits) = List.split (loop bindings) in
      let variables' = List.map new_var variables in
      let env' =
        List.fold_left2
          (fun env variable variable' ->
             M.add variable (Emit.Variable variable') env)
          env variables variables'
      in
      Emit.Let (variables', inits, analyze_body qq env' body)
  | _ -> failwith "bad syntax in (let)"
and analyze_set qq env cdr =
  match cdr with
    Scheme.Scons
      {Scheme.car = Scheme.Symbol name;
       Scheme.cdr =
         Scheme.Scons {Scheme.car = exp; Scheme.cdr = Scheme.Snil}} ->
      begin try
        match M.find name env with
          Emit.Variable var ->
            var.Emit.mut <- true; Emit.Set (var, analyze qq env exp)
        | Emit.Syntax _ -> failwith "cannot! a syntax"
        | Emit.Builtin (_, _, _) -> failwith "cannot set! a builtin"
      with Not_found -> failwith "cannot set! an undefined variable"
      end
  | _ -> failwith "bad syntax in set!"
and analyze_lambda qq env cdr =
  match cdr with
    Scheme.Scons cons ->
      begin match cons.Scheme.car with
        Scheme.Scons cons' ->
          (* have argument list *)
          let rec loop cons' =
            match cons'.Scheme.car, cons'.Scheme.cdr with
              Scheme.Symbol arg, Scheme.Snil -> false, [arg]
            | Scheme.Symbol arg, Scheme.Scons cons' ->
                let (varargs, args) = loop cons' in varargs, arg :: args
            | Scheme.Symbol arg, Scheme.Symbol a -> true, [arg; a]
            | _ -> failwith "bad syntax in (lambda)"
          in
          let (varargs, args) = loop cons' in
          let args' = List.map new_var args in
          let env' =
            List.fold_left2
              (fun env arg arg' -> M.add arg (Emit.Variable arg') env) env
              args args'
          in
          Emit.Lambda (varargs, args', analyze_body qq env' cons.Scheme.cdr)
      | Scheme.Symbol name ->
          let arg' = new_var name in
          let env' = M.add name (Emit.Variable arg') env in
          Emit.Lambda (true, [arg'], analyze_body qq env' cons.Scheme.cdr)
      | Scheme.Snil ->
          (* zero-arity *)
          Emit.Lambda (false, [], analyze_body qq env cons.Scheme.cdr)
      | _ -> failwith "bad syntax in (lambda)"
      end
  | _ -> failwith "bad syntax in (lambda)"
and analyze_alternative qq env cdr =
  match cdr with
    Scheme.Scons
      {Scheme.car = condition;
       Scheme.cdr =
         Scheme.Scons {Scheme.car = iftrue; Scheme.cdr = Scheme.Snil}} ->
      Emit.If
        (analyze qq env condition, analyze qq env iftrue,
         Emit.Quote Scheme.Void)
  | Scheme.Scons
      {Scheme.car = condition;
       Scheme.cdr =
         Scheme.Scons
           {Scheme.car = iftrue;
            Scheme.cdr =
              Scheme.Scons {Scheme.car = iffalse; Scheme.cdr = Scheme.Snil}}} ->
      Emit.If
        (analyze qq env condition, analyze qq env iftrue,
         analyze qq env iffalse)
  | _ -> failwith "Ast.analyze_alternative: bad syntax in (if)"
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

and analyze_and qq env cdr =
  let rec loop cdr =
    match cdr with
      Scheme.Snil -> Emit.Quote Scheme.Strue
    | Scheme.Scons {Scheme.car = test; Scheme.cdr = Scheme.Snil} ->
        analyze qq env test
    | Scheme.Scons {Scheme.car = test; Scheme.cdr = tests} ->
        let v = new_var_no_mangle "test" false 0 in
        let v' = Emit.Variable v in
        Emit.Let
          ([v], [analyze qq env test],
           Emit.If (Emit.Reference v', loop tests, Emit.Reference v'))
    | _ -> failwith "bad syntax in (and)"
  in
  loop cdr

and analyze_or qq env cdr =
  let rec loop cdr =
    match cdr with
      Scheme.Snil -> Emit.Quote Scheme.Sfalse
    | Scheme.Scons {Scheme.car = test; Scheme.cdr = Scheme.Snil} ->
        analyze qq env test
    | Scheme.Scons {Scheme.car = test; Scheme.cdr = tests} ->
        let v = new_var_no_mangle "test" false 0 in
        let v' = Emit.Variable v in
        Emit.Let
          ([v], [analyze qq env test],
           Emit.If (Emit.Reference v', Emit.Reference v', loop tests))
    | _ -> failwith "bad syntax in (or)"
  in
  loop cdr
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
and analyze_delay qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = e; Scheme.cdr = Scheme.Snil} ->
      Emit.Delay (analyze qq env e)
  | _ -> failwith "bad syntax in (delay)"
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
and analyze_time qq env cdr =
  match cdr with
    Scheme.Scons {Scheme.car = e; Scheme.cdr = Scheme.Snil} ->
      Emit.Time (analyze qq env e)
  | _ -> failwith "bad syntax in (time)"
