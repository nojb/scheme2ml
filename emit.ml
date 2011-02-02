open Printf
open Datum

module M = Map.Make (String)

type variable =
  { name : string;
    mutable mut : bool;
    mutable referenced : bool;
    mutable closure : bool;
    mutable varargs : bool;
    mutable arity : int }

type t =
  | Quote of datum
  | Reference of binding
  | Begin of t list
  | Lambda of bool * variable list * t
  | If of t * t * t
  | Set of variable * t
  | Let of variable list * t list * t
  | Application of t * t list
  | Case of t * (Scheme.t list * t) list * t
  | Delay of t
  | Time of t

and binding =
  | Variable of variable
  | Builtin of (int * string) option * (int * string) list * string
  | Syntax of (int -> binding M.t -> datum list -> t)

let binding_name = function
  | Variable var -> var.name
  | Builtin (_, _, name) -> name
  | _ -> failwith "binding_name"

let binding_mutable = function
  | Variable var -> var.mut
  | Syntax _ | Builtin (_, _, _) -> false

let emit_lit ppf x =
  fprintf ppf "%s" x

let rec emit_cons pp ppf = function
  | [] -> fprintf ppf "Scheme.Snil"
  | a :: b ->
      fprintf ppf "(Scheme.Scons {Scheme.car=%a;Scheme.cdr=%a})"
        pp a (emit_cons pp) b

let rec emit_separated sep f ppf x =
  match x with
  | [] -> ()
  | [a] -> f ppf a
  | a :: b ->
      fprintf ppf "%a%s%a" f a sep (emit_separated sep f) b

let emit_alt pp x y ppf b =
  if b then pp ppf x else pp ppf y

let rec emit ppf = function
  | Quote q -> emit_quote ppf q
  | Reference binding -> emit_reference ppf binding
  | Application (f, args) -> emit_application ppf f args
  | Begin [] -> fprintf ppf "Scheme.Void"
  | Begin [x] -> emit ppf x
  | Begin xs -> emit_begin ppf xs
  | Set (var, exp) ->
      fprintf ppf "(%s := %a; Scheme.Void)" var.name emit exp
  | Let ([], [], body) -> emit ppf body
  | Let (variables, inits, body) -> emit_let ppf variables inits body
  | Lambda (varargs, args, body) -> emit_lambda ppf varargs args body
  | If (cond, iftrue, iffalse) -> emit_if ppf cond iftrue iffalse
  | Case (key, clause, elseclause) -> emit_case ppf key clause elseclause
  | Delay promise ->
      fprintf ppf "(Scheme.Spromise (lazy %a))" emit promise
  | Time e -> emit_time ppf e

and emit_quote ppf = function
  | Dint n -> fprintf ppf "(Scheme.Snum (Num.Int %d))" n
  | Dbool true -> fprintf ppf "Scheme.Strue"
  | Dbool false -> fprintf ppf "Scheme.Sfalse"
  | Dchar c -> fprintf ppf "(Scheme.Schar %C)" c
  | Dstring s -> fprintf ppf "(Scheme.String %S)" s
  | Dlist xs ->
      let rec loop ppf = function
        | [] -> fprintf ppf "Scheme.Snil"
        | x :: xs ->
            fprintf ppf "(Scheme.Scons {Scheme.car=%a; Scheme.cdr=%a})"
              emit_quote x loop xs
      in loop ppf xs
  | Ddot (xs, x) ->
      let rec loop ppf = function
        | [] -> emit_quote ppf x
        | x :: xs ->
            fprintf ppf "(Scheme.Scons {Scheme.car=%a; Scheme.cdr=%a})"
              emit_quote x loop xs
      in loop ppf xs
  | Dvec v ->
      fprintf ppf "(Scheme.Vector [|%a|])"
        (emit_separated "; " emit_quote) v
  | Dsym s -> fprintf ppf "(Scheme.intern %S)" s

and emit_begin ppf ls =
  let rec loop ppf = function
    | [] -> fprintf ppf "Scheme.Void"
    | [a] -> emit ppf a
    | a :: b -> fprintf ppf "ignore %a; %a" emit a loop b
  in fprintf ppf "(%a)" loop ls

and emit_if ppf cond iftrue iffalse =
  fprintf ppf "(if not (Scheme.Sfalse = %a) then %a else %a)"
    emit cond emit iftrue emit iffalse

and emit_case ppf key clauses elseclause =
  assert false
  (* match clauses with
  | [] ->
      fprintf ppf "(let _ = %a in %a)"
        emit key emit elseclause
  | clauses ->
      let emit_pattern ppf = function
        | Scheme.Symbol s ->
            fprintf ppf
              "Scheme.Symbol _ as s when (Scheme.intern \"%s\" == s)" s
        | Scheme.Snum n ->
            fprintf ppf
              "Scheme.Snum n when Num.eq_num n (Num.num_of_string \"%s\")"
                (Num.string_of_num n)
        | _ as d -> emit_quote ppf d
      in
      fprintf ppf "(match %a with | %a | _ -> %a)"
        emit key
        (emit_separated "|"
          (fun ppf (ds, e) ->
            emit_separated " | "
              (fun ppf d -> fprintf ppf "%a -> %a" emit_pattern d emit e) ppf
              ds))
        clauses emit elseclause*)

and emit_reference ppf = function
  | Syntax _ -> failwith "emit: cannot reference syntax"
  | Variable var ->
      if var.mut then fprintf ppf "!%s" var.name
      else fprintf ppf "%s" var.name
  | Builtin (Some (0, varargs), _, _) ->
      fprintf ppf "(Scheme.Lambda %s)" varargs
  | Builtin (Some (fixed, varargs), _, name) ->
      fprintf ppf "(Scheme.Lambda (fun args -> match args with |";
      let rec loop count ppf =
        if count > fixed then fprintf ppf "rest"
        else
          fprintf ppf "(Scheme.Scons {Scheme.car = arg%d; Scheme.cdr = %t})" count
            (loop (count+1))
      in
      fprintf ppf "%t -> %s" (loop 1) varargs;
      for i = 1 to fixed do fprintf ppf " arg%d " i done;
      fprintf ppf " rest | _ -> failwith \"%s: bad arity\"))" name
  | Builtin (None, [arity, mlname], name) ->
      if arity < 5 then fprintf ppf "(Scheme.Lambda%d %s)" arity mlname
      else assert false
  | Builtin (None, impls, name) ->
      fprintf ppf "(Scheme.Lambda (fun args -> match args with |";
      let rec help ppf (arity, name) =
        let rec loop count ppf =
          if count > arity then fprintf ppf "Scheme.Snil"
          else
            fprintf ppf "(Scheme.Scons {Scheme.car = arg%d; Scheme.cdr = %t})"
              count (loop (count+1))
        in
        fprintf ppf "%t -> %s" (loop 1) name;
        for i = 1 to arity do fprintf ppf " arg%d " i done;
        fprintf ppf " | "
      in
      List.iter (help ppf) impls;
      fprintf ppf "_ -> failwith \"%s: bad arity\"))" name

and emit_application ppf f args =
  match f with
  | Reference (Syntax _) -> failwith "emit: cannot emit for syntax"
  | Reference (Builtin (Some (0, "Scheme.vector"), [], "vector")) ->
      fprintf ppf "(Scheme.Vector [|%a|])"
        (emit_separated "; " emit) args
  | Reference (Builtin (Some (fixed, varargs), impls, name)) ->
      let arity = List.length args in
      begin try
        let impl = List.assoc arity impls in
        fprintf ppf "(%s " impl;
        if arity = 0 then fprintf ppf "()"
        else emit_separated " " emit ppf args;
        fprintf ppf ")"
      with Not_found ->
        let rec loop count ppf args =
          if count > fixed then
            emit_cons emit ppf args
          else
            match args with
            | [] -> failwith (name ^ ": bad arity")
            | a :: b -> fprintf ppf "%a %a" emit a (loop (count+1)) b
        in
        fprintf ppf "(%s %a)" varargs (loop 1) args
      end
  | Reference (Builtin (None, impls, name)) ->
      let arity = List.length args in
      let impl =
        try List.assoc arity impls with
          Not_found -> failwith (name ^ ": bad arity")
      in
      fprintf ppf "(%s " impl;
      if arity = 0 then fprintf ppf "()" else emit_separated " " emit ppf args;
      fprintf ppf ")"
  | Reference (Variable var) when not var.mut && var.closure ->
      fprintf ppf "(imp_%s " var.name;
      if var.varargs && var.arity - 1 > List.length args then
        failwith (var.name ^ ": arity error")
      else if List.length args > 0 then
        let rec loop i ppf args =
          if i >= var.arity - 1 && var.varargs then
            emit_cons emit ppf args
          else if i < var.arity then
            match args with
              [] -> failwith (var.name ^ ": arity error")
            | a :: b -> fprintf ppf "%a %a" emit a (loop (i+1)) b
        in
        loop 0 ppf args
      else if var.varargs then fprintf ppf "Scheme.Snil"
      else fprintf ppf "()";
      fprintf ppf ")"
  | _ ->
      if List.length args < 5 then
        fprintf ppf "(Scheme.apply%d %a %a)"
          (List.length args)
          emit f (emit_separated " " emit) args
      else
        fprintf ppf "(Scheme.apply %a %a)"
          emit f (emit_cons emit) args

and emit_let ppf variables inits body =
  let emit_var ppf var init =
    match init with
    | Lambda (_, [], body) when not var.mut ->
        fprintf ppf "imp_%s () = %a" var.name
          emit body;
        if var.referenced then
          fprintf ppf " and %s = Scheme.Lambda0 imp_%s" var.name var.name;
        fprintf ppf " and "
    | Lambda (varargs, args, body) when not var.mut ->
        fprintf ppf "imp_%s %s = " var.name
          (String.concat " " (List.map (fun arg -> arg.name) args));
        List.iter
          (fun arg ->
             if arg.mut then
               fprintf ppf "let %s = ref %s in " arg.name arg.name)
          args;
        emit ppf body;
        if var.referenced then
          begin
            fprintf ppf " and %s = " var.name;
            if List.length args < 5 then
              fprintf ppf "Scheme.Lambda%d imp_%s" (List.length args)
                var.name
            else
              emit_lambda_body varargs args
                (fun ppf ->
                   fprintf ppf "imp_%s %s" var.name
                     (String.concat " " (List.map (fun a -> a.name) args)))
                ppf
          end;
        fprintf ppf " and "
    | _ ->
        fprintf ppf "%s = %s %a and " var.name
          (if var.mut then "ref" else "") emit init
  in
  let emit_last_var ppf var init =
    match init with
    | Lambda (_, [], body) when not var.mut ->
        fprintf ppf "imp_%s () = %a" var.name
          emit body;
        if var.referenced then
          fprintf ppf " and %s = Scheme.Lambda0 imp_%s" var.name var.name;
        fprintf ppf " in "
    | Lambda (varargs, args, body) when not var.mut ->
        fprintf ppf "imp_%s %a = " var.name
          (emit_separated " " emit_lit) (List.map (fun arg -> arg.name) args);
        List.iter
          (fun arg ->
             if arg.mut then
               fprintf ppf "let %s = ref %s in " arg.name arg.name)
          args;
        emit ppf body;
        if var.referenced then
          begin
            fprintf ppf " and %s = " var.name;
            if List.length args < 5 then
              fprintf ppf "Scheme.Lambda%d imp_%s" (List.length args)
                var.name
            else
              emit_lambda_body varargs args
                (fun ppf ->
                   fprintf ppf "imp_%s %s" var.name
                     (String.concat " " (List.map (fun a -> a.name) args)))
                ppf
          end;
        fprintf ppf " in "
    | _ ->
        fprintf ppf "%s = %s %a in" var.name
          (if var.mut then "ref" else "")
          emit init
  in
  let rec loop variables inits ppf =
    match variables, inits with
    | [], [] -> assert false
    | [a], [b] -> emit_last_var ppf a b
    | a :: a', b :: b' -> emit_var ppf a b; loop a' b' ppf
    | _ -> assert false
  in
  fprintf ppf "(let rec %t %a)" (loop variables inits) emit body

and emit_lambda_body varargs args f ppf =
  let rec loop ppf = function
    | [] -> fprintf ppf "Scheme.Snil"
    | a :: b ->
        if varargs then emit_lit ppf a.name
        else
          fprintf ppf "(Scheme.Scons {Scheme.car=%s; Scheme.cdr=%a})"
            a.name loop b
  in
  fprintf ppf "(Scheme.Lambda (fun args -> ";
  fprintf ppf "match args with | %a -> %t | _ -> failwith \"incorrect arity\"))"
    loop args f

and emit_lambda ppf varargs args body =
  if List.length args >= 5 then
    let rec loop ppf = function
      | [] -> fprintf ppf "Scheme.Snil"
      | a :: b ->
          if varargs then emit_lit ppf a.name
          else
            fprintf ppf "(Scheme.Scons {Scheme.car=%s; Scheme.cdr=%a})"
              a.name loop b
    in
    fprintf ppf "(Scheme.Lambda (fun args ->
      match args with | %a -> %a %a
      | _ -> failwith \"incorrect arity\"))"
      loop args 
      (emit_separated "\n" (fun ppf s -> fprintf ppf "let %s = ref %s in "
        s.name s.name))
        (List.filter (fun arg -> arg.mut) args)
      emit body
  else
    fprintf ppf "(Scheme.Lambda%d (fun %t -> %a %a))"
      (List.length args)
      (fun ppf ->
        if List.length args = 0 then fprintf ppf "()"
        else emit_separated " "
          (fun ppf s -> fprintf ppf "%s" s) ppf
          (List.map (fun a -> a.name) args))
      (emit_separated "\n" (fun ppf s -> fprintf ppf "let %s = ref %s in " s.name
      s.name))
      (List.filter (fun arg -> arg.mut) args)
      emit body

and emit_time ppf e =
  fprintf ppf
    "(let t = Sys.time () in let e = %a in let t' = Sys.time () in
      Printf.printf \"time: %%f\\n\" (t'-.t); e)"
    emit e

let pp ppf x =
  fprintf ppf "%a\n%!" emit x
