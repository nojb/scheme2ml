open Types
open Datum

module M = Map.Make (String)

type binding =
  | Tmacro of binding M.t * (binding M.t -> datum list -> datum)
  | Tspecial of (binding M.t -> datum list -> pexp)
  | Tfree
  | Tother

let find x env =
  try M.find x env
  with Not_found -> Tfree

let rec analyze_program x =
  let syntax_forms =
    [ "begin", analyze_begin;
      "lambda", analyze_lambda;
      (* ("define", analyze_define); *)
      "set!", analyze_set;
      "let-syntax", analyze_let_syntax;
      "quote", analyze_quote;
      (* "quasiquote", analyze_quasiquote;*)
      "if", analyze_alternative;
      (* "let", analyze_let; *)
      (* "let*", analyze_let_star; *)
      (* "letrec", analyze_letrec; *)
      (* "cond", analyze_cond; *)
      (* "and", analyze_and; *)
      (* "or", analyze_or; *)
      (* "case", analyze_case;*)
      (* "delay", analyze_delay; *)
      (* "do", analyze_do; *)
      (* "time", analyze_time *) ] in
  let env = List.fold_left
    (fun env (name, impl) -> M.add name (Tspecial impl) env) M.empty syntax_forms in
  analyze env x

and analyze env x =
  match x with
  | Dint _
  | Dbool _
  | Dchar _
  | Dstring _
  | Dlist []
  | Dvec _ -> Pquote x
  | Dsym s ->
      begin match find s env with
        | Tfree
        | Tother -> Pvar s
        | Tspecial _ -> failwith "can't reference a syntax object"
        | Tmacro _ -> failwith "can't reference a macro object"
      end
  | Dlist (x :: xs) -> analyze_cons env x xs
  | Ddot _ -> failwith "bad syntax"
  | Dunspec -> assert false

and analyze_cons env x xs =
  match x with
  | Dsym x ->
      begin match find x env with
      | Tspecial syn -> syn env xs
      | Tmacro _ -> assert false
      | Tfree
      | Tother -> Papp (Pvar x, List.map (analyze env) xs)
      end
  | _ -> Papp (analyze env x, List.map (analyze env) xs)

and analyze_begin env xs =
  Pbegin (List.map (analyze env) xs)

and analyze_quote env = function
  | a :: [] -> Pquote a
  | _ -> failwith "bad syntax in (quote)"

and analyze_body env xs =
  (* let rec loop = function
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
  | [] -> Pbegin (List.map (analyze qq env) xs)
  | _ -> analyze qq env (Dlist (Dsym "letrec" :: Dlist x :: xs)) *)
  Pbegin (List.map (analyze env) xs)

(* and analyze_let_star qq env = function
  | Dlist bindings :: body ->
      analyze_let qq env (List.fold_right
        (fun binding body ->
          Dlist [binding] :: Dlist (Dsym "let" :: body) :: [] )
        bindings (Dlist [] :: body))
  | _ -> failwith "bad syntax in (let\*\)"

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
  *)

(* and analyze_let qq env = function
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
  *)

and analyze_set env = function
  | Dsym name :: exp :: [] ->
      begin match find name env with
        | Tfree
        | Tother -> Passign (name, analyze env exp)
        | Tspecial _ -> failwith "cannot set! a syntax"
        | Tmacro _ -> failwith "cannot set! a macro"
      end
  | _ -> failwith "bad syntax in set!"

and analyze_lambda env = function
  | Dlist args :: body ->
      let args =
        List.map
          (function
            | Dsym arg -> arg
            | _ -> failwith "bad syntax in (lambda)") args in
      let env = List.fold_left (fun env x -> M.remove x env) env args in
      Plambda (args, analyze_body env body)
  | Ddot (args, Dsym a) :: body ->
      let args =
        List.map
          (function
            | Dsym arg -> arg
            | _ -> failwith "bad syntax in (lambda)") args in
      let env =
        M.remove a
          (List.fold_left
            (fun env x -> M.remove x env) env args) in
      PlambdaVar (args, a, analyze_body env body)
  | Dsym name :: body ->
      PlambdaVar ([], name, analyze_body (M.remove name env) body)
  | _ -> failwith "bad syntax in (lambda)"

and analyze_alternative env = function
  | cond :: t :: [] ->
      Pif (analyze env cond, analyze env t, Pquote Dunspec)
  | cond :: t :: f :: [] ->
      Pif (analyze env cond, analyze env t, analyze env f)
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

(* and analyze_and qq env = function
  | [] -> Pquote (Dbool true)
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
          *)

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

  (*
and analyze_delay qq env = function
  | e :: [] -> Emit.Delay (analyze qq env e)
  | _ -> failwith "bad syntax in (delay)"
  *)

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

  (*
and analyze_time qq env = function
  | e :: [] ->
      Emit.Time (analyze qq env e)
  | _ -> failwith "bad syntax in (time)"
  *)

(* and analyze_macro qq env = function
  | Dlist [Dsym keyword; Dlist (Dsym "syntax-rules" :: Dlist literals :: rules)] ->
      ...
  | _ -> failwith "bad syntax in (let-syntax)"
  *)

and analyze_let_syntax env = function
  | Dlist bindings :: body -> assert false
      (* let macros = List.map (analyze_macro qq env) bindings in
      ...*)
  | _ -> failwith "bad syntax in (let-syntax)"
