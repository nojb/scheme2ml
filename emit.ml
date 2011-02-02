module M = Map.Make (String)

type variable =
  { name : string;
    mutable mut : bool;
    mutable referenced : bool;
    mutable closure : bool;
    mutable varargs : bool;
    mutable arity : int }

type t =
    Quote of Scheme.t
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
    Variable of variable
  | Builtin of (int * string) option * (int * string) list * string
  | Syntax of (int -> binding M.t -> Scheme.t -> t)

let binding_name =
  function
    Variable var -> var.name
  | Builtin (_, _, name) -> name
  | _ -> failwith "binding_name"

let binding_mutable =
  function
    Variable var -> var.mut
  | Syntax _ | Builtin (_, _, _) -> false

let rec emit_separated_last sep f last x =
  match x with
    [] -> ()
  | [a] -> last a
  | a :: b -> f a; Printf.printf "%s" sep; emit_separated_last sep f last b

let rec emit_separated sep f x =
  match x with
    [] -> ()
  | [a] -> f a
  | a :: b -> f a; Printf.printf "%s" sep; emit_separated sep f b

let rec emit x =
  match x with
    Quote q -> emit_quote q
  | Reference binding -> emit_reference binding
  | Application (f, args) -> emit_application f args
  | Begin [] -> Printf.printf "Scheme.Void"
  | Begin [l] -> emit l
  | Begin ls -> emit_begin ls
  | Set (var, exp) ->
      Printf.printf "(%s.val := " var.name;
      emit exp;
      Printf.printf " ; Scheme.Void)"
  | Let ([], [], body) -> emit body
  | Let (variables, inits, body) -> emit_let variables inits body
  | Lambda (varargs, args, body) -> emit_lambda varargs args body
  | If (cond, iftrue, iffalse) -> emit_if cond iftrue iffalse
  | Case (key, clause, elseclause) -> emit_case key clause elseclause
  | Delay promise ->
      Printf.printf "(Scheme.Promise (lazy "; emit promise; Printf.printf "))"
  | Time e -> emit_time e

and emit_quote = function
  | Scheme.Snum n -> Printf.printf "(Scheme.Snum (Num.Int %s))" (Num.string_of_num n)
  | Scheme.Char char -> Printf.printf "(Scheme.Char '%c')" char
  | Scheme.String string -> Printf.printf "(Scheme.String \"%s\")" string
  | Scheme.Scons cons ->
      Printf.printf "(Scheme.Scons { Scheme.car = ";
      emit_quote cons.Scheme.car;
      Printf.printf "; Scheme.cdr = ";
      emit_quote cons.Scheme.cdr;
      Printf.printf "})"
  | Scheme.Vector vector ->
      Printf.printf "(Scheme.Vector [|";
      let len = Array.length vector in
      for i = 0 to len - 1 do
        if i = len - 1 then
          begin emit_quote vector.(i); Printf.printf "|])" end
        else if i >= len then Printf.printf "|])"
        else begin emit_quote vector.(i); Printf.printf "; " end
      done
  | Scheme.Symbol s -> Printf.printf "(Scheme.intern \"%s\")" s
  | Scheme.Snil -> Printf.printf "Scheme.Snil"
  | Scheme.Strue -> Printf.printf "Scheme.Strue"
  | Scheme.Sfalse -> Printf.printf "Scheme.Sfalse"
  | Scheme.Void -> Printf.printf "Scheme.Void"
  | Scheme.In _ | Scheme.Out _ | Scheme.Promise _ | Scheme.Lambda _ |
    Scheme.Lambda0 _ | Scheme.Lambda1 _ | Scheme.Lambda2 _ |
    Scheme.Lambda3 _ | Scheme.Lambda4 _ ->
      failwith "Emit.emit_quote"

and emit_begin ls =
  Printf.printf "(";
  let rec loop ls =
    match ls with
      [] -> Printf.printf "Scheme.Void"
    | [a] -> emit a
    | a :: b -> Printf.printf "ignore ("; emit a; Printf.printf "); "; loop b
  in
  loop ls; Printf.printf ")"
and emit_if cond iftrue iffalse =
  Printf.printf "(if (Scheme.Strue == ";
  emit cond;
  Printf.printf ") then ";
  emit iftrue;
  Printf.printf " else ";
  emit iffalse;
  Printf.printf ")"
and emit_case key clauses elseclause =
  match clauses with
    [] ->
      Printf.printf "(let _ = ";
      emit key;
      Printf.printf " in ";
      emit elseclause;
      Printf.printf ")"
  | clauses ->
      let emit_pattern d =
        match d with
          Scheme.Symbol s ->
            Printf.printf
              "Scheme.Symbol _ as s when (Scheme.intern \"%s\" == s)" s
        | _ -> emit_quote d
      in
      Printf.printf "(match ";
      emit key;
      Printf.printf " with [ ";
      emit_separated "|"
        (fun (ds, e) ->
           (* do { *)
           emit_separated " | "
             (fun d -> emit_pattern d; Printf.printf " -> "; emit e) ds)
        clauses;
      Printf.printf " | _ -> ";
      emit elseclause;
      Printf.printf "])"
and emit_reference binding =
  match binding with
    Syntax _ -> failwith "emit: cannot reference syntax"
  | Variable var ->
      if var.mut then Printf.printf "%s.val" var.name
      else Printf.printf "%s" var.name
  | Builtin (Some (0, varargs), _, _) ->
      Printf.printf "(Scheme.Lambda %s)" varargs
  | Builtin (Some (fixed, varargs), _, name) ->
      Printf.printf "(Scheme.Lambda (fun args -> match args with [";
      let rec loop count =
        if count > fixed then "rest " ^ String.make (count - 1) '}'
        else
          "Scheme.Cons { Scheme.car = arg" ^ string_of_int count ^
          "; Scheme.cdr = " ^ loop (count + 1)
      in
      Printf.printf "%s -> %s" (loop 1) varargs;
      for i = 1 to fixed do Printf.printf " arg%d " i done;
      Printf.printf " rest | _ -> failwith \"%s: bad arity\" ]))" name
  | Builtin (None, [arity, mlname], name) ->
      if arity < 5 then Printf.printf "(Scheme.Lambda%d %s)" arity mlname
      else assert false
  | Builtin (None, impls, name) ->
      Printf.printf "(Scheme.Lambda (fun args -> match args with [";
      let rec help (arity, name) =
        let rec loop count =
          if count > arity then "Scheme.Nil" ^ String.make (count - 1) '}'
          else
            "Scheme.Cons { Scheme.car = arg" ^ string_of_int count ^
            "; Scheme.cdr = " ^ loop (count + 1)
        in
        Printf.printf "%s -> %s" (loop 1) name;
        for i = 1 to arity do Printf.printf " arg%d " i done;
        Printf.printf " | "
      in
      List.iter help impls;
      Printf.printf "_ -> failwith \"%s: bad arity\" ]))" name
and emit_application f args =
  match f with
    Reference (Syntax _) -> failwith "emit: cannot emit for syntax"
  | Reference (Builtin (Some (0, "Scheme.vector"), [], "vector")) ->
      Printf.printf "(Scheme.Vector [|";
      emit_separated ";" emit args;
      Printf.printf "|])"
  | Reference (Builtin (Some (fixed, varargs), impls, name)) ->
      let arity = List.length args in
      begin try
        let impl = List.assoc arity impls in
        Printf.printf "(%s " impl;
        if arity = 0 then Printf.printf "()"
        else emit_separated " " emit args;
        Printf.printf ")"
      with Not_found ->
        Printf.printf "(%s " varargs;
        let rec loop count args =
          if count > fixed then
            let rec loop2 args =
              match args with
                [] -> Printf.printf "Scheme.Nil"
              | a :: b ->
                  Printf.printf "Scheme.Cons { Scheme.car = ";
                  emit a;
                  Printf.printf "; Scheme.cdr = ";
                  loop2 b;
                  Printf.printf "}"
            in
            Printf.printf "("; loop2 args; Printf.printf ")"
          else
            match args with
              [] -> failwith (name ^ ": bad arity")
            | a :: b -> emit a; Printf.printf " "; loop (count + 1) b
        in
        loop 1 args; Printf.printf ")"
      end
  | Reference (Builtin (None, impls, name)) ->
      let arity = List.length args in
      let impl =
        try List.assoc arity impls with
          Not_found -> failwith (name ^ ": bad arity")
      in
      Printf.printf "(%s " impl;
      if arity = 0 then Printf.printf "()" else emit_separated " " emit args;
      Printf.printf ")"
  | Reference (Variable var) when not var.mut && var.closure ->
      Printf.printf "(imp_%s " var.name;
      if var.varargs && var.arity - 1 > List.length args then
        failwith (var.name ^ ": arity error")
      else if List.length args > 0 then
        let rec loop args i =
          if i >= var.arity - 1 && var.varargs then
            let rec loop2 args =
              match args with
                [] -> Printf.printf " Scheme.Nil "
              | a :: b ->
                  Printf.printf " (Scheme.Cons { Scheme.car = ";
                  emit a;
                  Printf.printf " ; Scheme.cdr = ";
                  loop2 b;
                  Printf.printf " }) "
            in
            loop2 args
          else if i < var.arity then
            match args with
              [] -> failwith (var.name ^ ": arity error")
            | a :: b -> emit a; Printf.printf " "; loop b (i + 1)
        in
        loop args 0
      else if var.varargs then Printf.printf "Scheme.Nil"
      else Printf.printf "()";
      Printf.printf ")"
  | _ ->
      if List.length args < 5 then
        begin
          Printf.printf "(Scheme.apply%d " (List.length args);
          emit f;
          Printf.printf " ";
          emit_separated " " emit args;
          Printf.printf ")"
        end
      else
        begin
          Printf.printf "(Scheme.apply ";
          emit f;
          Printf.printf "(";
          let rec loop args =
            match args with
              [] -> Printf.printf "Scheme.Nil"
            | a :: b ->
                Printf.printf "Scheme.Cons { Scheme.car = ";
                emit a;
                Printf.printf "; Scheme.cdr = ";
                loop b;
                Printf.printf "}"
          in
          loop args; Printf.printf "))"
        end
and emit_let variables inits body =
  let emit_var var init =
    match init with
      Lambda (_, [], body) when not var.mut ->
        Printf.printf "imp_%s = fun () -> " var.name;
        emit body;
        if var.referenced then
          Printf.printf " and %s = (Scheme.Lambda0 imp_%s)" var.name var.name;
        Printf.printf " and "
    | Lambda (varargs, args, body) when not var.mut ->
        Printf.printf "imp_%s = fun %s -> " var.name
          (String.concat " " (List.map (fun arg -> arg.name) args));
        List.iter
          (fun arg ->
             if arg.mut then
               Printf.printf "let %s = ref %s in " arg.name arg.name)
          args;
        emit body;
        if var.referenced then
          begin
            Printf.printf " and %s = " var.name;
            if List.length args < 5 then
              Printf.printf "(Scheme.Lambda%d imp_%s)" (List.length args)
                var.name
            else
              emit_lambda_body varargs args
                (fun () ->
                   Printf.printf "imp_%s %s" var.name
                     (String.concat " " (List.map (fun a -> a.name) args)))
          end;
        Printf.printf " and "
    | _ ->
        Printf.printf "%s = " var.name;
        if var.mut then Printf.printf "ref (";
        emit init;
        if var.mut then Printf.printf ")";
        Printf.printf " and "
  in
  let emit_last_var var init =
    match init with
      Lambda (_, [], body) when not var.mut ->
        Printf.printf "imp_%s = fun () -> " var.name;
        emit body;
        if var.referenced then
          Printf.printf " and %s = (Scheme.Lambda0 imp_%s)" var.name var.name;
        Printf.printf " in "
    | Lambda (varargs, args, body) when not var.mut ->
        Printf.printf "imp_%s = fun %s -> " var.name
          (String.concat " " (List.map (fun arg -> arg.name) args));
        List.iter
          (fun arg ->
             if arg.mut then
               Printf.printf "let %s = ref %s in " arg.name arg.name)
          args;
        emit body;
        if var.referenced then
          begin
            Printf.printf " and %s = " var.name;
            if List.length args < 5 then
              Printf.printf "(Scheme.Lambda%d imp_%s)" (List.length args)
                var.name
            else
              emit_lambda_body varargs args
                (fun () ->
                   Printf.printf "imp_%s %s" var.name
                     (String.concat " " (List.map (fun a -> a.name) args)))
          end;
        Printf.printf " in "
    | _ ->
        Printf.printf "%s = " var.name;
        if var.mut then Printf.printf "ref (";
        emit init;
        if var.mut then Printf.printf ")";
        Printf.printf " in "
  in
  Printf.printf "(let rec ";
  let rec loop variables inits =
    match variables, inits with
      [], [] -> assert false
    | [a], [b] -> emit_last_var a b
    | a :: a', b :: b' -> emit_var a b; loop a' b'
    | _ -> assert false
  in
  loop variables inits; emit body; Printf.printf ")"
and emit_lambda_body varargs args f =
  Printf.printf "(Scheme.Lambda (fun args -> ";
  Printf.printf "match args with [";
  let rec loop acc args =
    match args with
      [] -> "Scheme.Nil " ^ String.make acc '}'
    | [a] ->
        if varargs then a.name ^ String.make acc '}'
        else
          "Scheme.Cons { Scheme.car = " ^ a.name ^
          "; Scheme.cdr = Scheme.Nil " ^ String.make (acc + 1) '}'
    | a :: b ->
        "Scheme.Cons {Scheme.car = " ^ a.name ^ "; Scheme.cdr = " ^
        loop (acc + 1) b
  in
  Printf.printf "%s -> " (loop 0 args);
  f ();
  Printf.printf "| _ -> failwith \"incorrect arity\" ]))"
and emit_lambda varargs args body =
  if List.length args >= 5 then
    begin
      Printf.printf "(Scheme.Lambda (fun args -> ";
      Printf.printf "match args with [";
      let rec loop acc args =
        match args with
          [] -> "Scheme.Nil " ^ String.make acc '}'
        | [a] ->
            if varargs then a.name ^ String.make acc '}'
            else
              "Scheme.Cons { Scheme.car = " ^ a.name ^
              "; Scheme.cdr = Scheme.Nil " ^ String.make (acc + 1) '}'
        | a :: b ->
            "Scheme.Cons {Scheme.car = " ^ a.name ^ "; Scheme.cdr = " ^
            loop (acc + 1) b
      in
      Printf.printf "%s -> " (loop 0 args);
      List.iter
        (fun arg ->
           if arg.mut then
             Printf.printf "let %s = ref %s in " arg.name arg.name)
        args;
      emit body;
      Printf.printf "| _ -> failwith \"incorrect arity\" ]))"
    end
  else
    begin
      Printf.printf "(Scheme.Lambda%d (fun %s -> " (List.length args)
        (if List.length args = 0 then "()"
         else String.concat " " (List.map (fun a -> a.name) args));
      List.iter
        (fun arg ->
           if arg.mut then
             Printf.printf "let %s = ref %s in " arg.name arg.name)
        args;
      emit body;
      Printf.printf "))"
    end
and emit_time e =
  Printf.printf "(let t = Sys.time () in let e = ";
  emit e;
  Printf.printf " in let t' = Sys.time () in ";
  Printf.printf "do{Printf.printf \"time: %%f\\n\" (t' -. t);e})"
