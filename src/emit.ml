module M = Map.Make String;

type variable = {
  name : string;
  mut : mutable bool;
  closure : mutable bool
};

type t =
  [ Quote of Scheme.t
  | Reference of binding
  | Begin of list t
  | Lambda of bool and list variable and t (* bool indicates varargs *)
  | If of t and t and t
  (*| Define of binding and t*)
  | Set of variable and t
  | Let of list variable and list t and t (* (letrec ...) *)
  | Application of t and list t
  | Case of t and list (list Scheme.t * t) and t
  | Delay of t ]

and binding =
  [ Variable of variable
  | Builtin of option (int * string) and list (int * string) and string
  (* int is arity, string is Ocaml name *)
  | Syntax of int -> M.t binding -> Scheme.t -> t ];

value binding_name = fun
  [ Variable var -> var.name
  | Builtin _ _ name -> name
  | _ -> failwith "binding_name" ];

value binding_mutable = fun
  [ Variable var -> var.mut
  | Syntax _
  | Builtin _ _ _ -> False ];

value rec emit_separated sep f = fun
  [ [] -> ()
  | [a] -> f a
  | [a :: b] -> do {
      f a;
      Printf.printf "%s" sep;
      emit_separated sep f b
    } ];

value rec emit x =
  match x with
  [ Quote q -> emit_quote q
  | Reference binding -> emit_reference binding
  | Application f args -> emit_application f args
  | Begin ls -> do {
      Printf.printf "(do { ";
      let rec loop ls =
        match ls with
        [ [] -> Printf.printf "Scheme.Void"
        | [a] -> emit a
        | [a :: b] -> do {
          Printf.printf "ignore (";
          emit a;
          Printf.printf "); ";
          loop b
        } ]
      in loop ls;
      Printf.printf "})"
    }
  (*| Define b exp -> do {
      Printf.printf "value rec %s = " (binding_name b);
      if binding_mutable b then do {
        Printf.printf "(ref (";
        emit exp;
        Printf.printf "))"
      } else emit exp
    }*)
  | Set var exp -> do {
      Printf.printf "(do { %s.val := " var.name;
      emit exp;
      Printf.printf " ; Scheme.Void })"
    }
  | Let [] [] body -> emit body
  | Let variables inits body -> emit_let variables inits body
  | Lambda varargs args body -> emit_lambda varargs args body
  | If cond iftrue iffalse -> do {
      Printf.printf "(if (Scheme.is_true ";
      emit cond;
      Printf.printf ") then ";
      emit iftrue;
      Printf.printf " else ";
      emit iffalse;
      Printf.printf ")"
    }
  | Case key [] elseclause -> do {
      Printf.printf "(let _ = ";
      emit key;
      Printf.printf " in ";
      emit elseclause;
      Printf.printf ")"
    }
  | Case key clauses elseclause -> do {
      Printf.printf "(match ";
      emit key;
      Printf.printf " with [ ";
      emit_separated "|"
        (fun (ds, e) -> do {
          emit_separated " | " emit_quote ds;
          Printf.printf " -> ";
          emit e })
        clauses;
      Printf.printf " | _ -> ";
      emit elseclause;
      Printf.printf "])"
    }
  | Delay promise -> do {
      Printf.printf "(Scheme.Promise (lazy ";
      emit promise;
      Printf.printf "))"
    } ]

and emit_quote = fun
  [ Scheme.Num n ->
    if Num.eq_num n (Num.num_of_int (Num.int_of_num n)) then
      Printf.printf "(Scheme.Num (Num.num_of_int (%d)))" (Num.int_of_num n)
    else
      Printf.printf "(Scheme.Num (Num.num_of_string \"%s\"))"
        (Num.string_of_num n)
  | Scheme.Char char ->
      Printf.printf "(Scheme.Char '%c')" char
  | Scheme.String string ->
      Printf.printf "(Scheme.String \"%s\")" string
  | Scheme.Cons cons -> do {
      Printf.printf "(Scheme.Cons { Scheme.car = ";
      emit_quote cons.Scheme.car;
      Printf.printf "; Scheme.cdr = ";
      emit_quote cons.Scheme.cdr;
      Printf.printf "})"
    }
  | Scheme.Vector vector -> do {
      Printf.printf "(Scheme.Vector [|";
      let len = (Array.length vector) in
      for i = 0 to len-1 do {
        if i = len-1 then do {
          emit_quote vector.(i);
          Printf.printf "|])"
        } else if i >= len then
          Printf.printf "|])"
        else do {
          emit_quote vector.(i);
          Printf.printf "; "
        }
      }
    }
  | Scheme.Symbol s -> Printf.printf "(Scheme.intern \"%s\")" s
  | Scheme.Nil -> Printf.printf "Scheme.Nil"
  | Scheme.Boolean True -> Printf.printf "Scheme.t"
  | Scheme.Boolean False -> Printf.printf "Scheme.f"
  | Scheme.Void -> Printf.printf "Scheme.Void"
  | Scheme.In _
  | Scheme.Out _
  | Scheme.Promise _
  | Scheme.Lambda _
  | Scheme.Lambda0 _
  | Scheme.Lambda1 _
  | Scheme.Lambda2 _
  | Scheme.Lambda3 _
  | Scheme.Lambda4 _ -> failwith "Emit.emit_quote" ]

and emit_reference binding =
  match binding with
  [ Syntax _ -> failwith "emit: cannot reference syntax"
  | Variable var ->
      if var.mut then
        Printf.printf "%s.val" var.name
      else
        Printf.printf "%s" var.name
  | Builtin (Some (0, varargs)) _ _ ->
    Printf.printf "(Scheme.Lambda %s)" varargs
  | Builtin (Some (fixed, varargs)) _ name -> do {
      Printf.printf "(Scheme.Lambda (fun args -> match args with [";
      let rec loop count =
        if count > fixed then "rest " ^ (String.make (count-1) '}')
        else
          "Scheme.Cons { Scheme.car = arg" ^ (string_of_int count) ^
          "; Scheme.cdr = " ^ (loop (count+1))
      in
      Printf.printf "%s -> %s" (loop 1) varargs;
      for i = 1 to fixed do {
        Printf.printf " arg%d " i
      };
      Printf.printf " rest | _ -> failwith \"%s: bad arity\" ]))" name
    }
  | Builtin None [(arity,mlname)] name ->

      if arity < 5 then

        Printf.printf "(Scheme.Lambda%d %s)" arity mlname

      else do {

        assert False (* really, handle as below, but there are no builtins of
        fixed arity with >= 5 args! *)

      }

  | Builtin None impls name -> do {
      Printf.printf "(Scheme.Lambda (fun args -> match args with [";
      let rec help (arity, name) =
        let rec loop count =
          if count > arity then "Scheme.Nil" ^ (String.make (count-1) '}')
          else
            "Scheme.Cons { Scheme.car = arg" ^ (string_of_int count) ^
            "; Scheme.cdr = " ^ (loop (count+1))
        in do {
          Printf.printf "%s -> %s" (loop 1) name;
          for i = 1 to arity do {
            Printf.printf " arg%d " i
          };
          Printf.printf " | "
        }
      in
      List.iter help impls;
      Printf.printf "_ -> failwith \"%s: bad arity\" ]))" name
    } ]

and emit_application f args =
  match f with
  [ Reference (Syntax _) -> failwith "emit: cannot emit for syntax"
  | Reference (Builtin (Some (0, "Scheme.vector")) [] "vector") -> do {
      Printf.printf "(Scheme.Vector [|";
      emit_separated ";" emit args;
      Printf.printf "|])"
    }
  | Reference (Builtin (Some (fixed, varargs)) impls name) -> do {
      let arity = List.length args in
      try let impl = List.assoc arity impls in do {
        Printf.printf "(%s " impl;
        if arity = 0 then Printf.printf "()"
        else emit_separated " " emit args;
        Printf.printf ")"
      } with [ Not_found -> do {
        Printf.printf "(%s " varargs;
        let rec loop count args =
          if count > fixed then
            let rec loop2 args =
              match args with
              [ [] -> Printf.printf "Scheme.Nil"
              | [a :: b] -> do {
                  Printf.printf "Scheme.Cons { Scheme.car = ";
                  emit a;
                  Printf.printf "; Scheme.cdr = ";
                  loop2 b;
                  Printf.printf "}"
                } ]
            in do {
              Printf.printf "(";
              loop2 args;
              Printf.printf ")"
            }
          else match args with
          [ [] -> failwith (name ^ ": bad arity")
          | [a :: b] -> do {
              emit a;
              Printf.printf " ";
              loop (count+1) b
            } ]
        in do {
          loop 1 args;
          Printf.printf ")"
        }
      } ]
    }
  | Reference (Builtin None impls name) -> do {
      let arity = List.length args in
      let impl =
        try List.assoc arity impls
        with [ Not_found -> failwith (name ^ ": bad arity") ]
      in do {
        Printf.printf "(%s " impl;
        if arity = 0 then Printf.printf "()"
        else emit_separated " " emit args;
        Printf.printf ")"
      }
    }
  | _ ->
    if List.length args < 5 then do {
      Printf.printf "(Scheme.apply%d " (List.length args);
      emit f;
      Printf.printf " ";
      emit_separated " " emit args;
      Printf.printf ")"
    } else do {
      Printf.printf "(Scheme.apply ";
      emit f;
      Printf.printf "(";
      let rec loop args =
        match args with
        [ [] -> Printf.printf "Scheme.Nil"
        | [a :: b] -> do {
            Printf.printf "Scheme.Cons { Scheme.car = ";
            (emit a);
            Printf.printf "; Scheme.cdr = ";
            (loop b);
            Printf.printf "}"
          } ]
      in loop args; Printf.printf "))"
    } ]

and emit_let variables inits body = do {
  Printf.printf "(let rec ";
  let rec loop variables inits =
    match (variables, inits) with
    [ ([], []) -> assert False
    | ([a], [b]) -> do {
        Printf.printf "%s = " a.name;
        if a.mut then
          Printf.printf "ref ("
        else ();
        emit b;
        if a.mut then
          Printf.printf ")"
        else ();
        Printf.printf " in "
      }
    | ([a :: a'], [b :: b']) -> do {
        Printf.printf "%s = " a.name;
        if a.mut then
          Printf.printf "ref ("
        else ();
        emit b;
        if a.mut then
          Printf.printf ")"
        else ();
        Printf.printf " and ";
        loop a' b'
      }
    | _ -> assert False ]
  in
  loop variables inits;
  emit body;
  Printf.printf ")"
}

and emit_lambda varargs args body =
  if List.length args >= 5 then do {
    Printf.printf "(Scheme.Lambda (fun args -> ";
    Printf.printf "match args with [";
    let rec loop acc args =
      match args with
      [ [] -> "Scheme.Nil " ^ String.make acc '}'
      | [a] ->
          if varargs then a.name ^ (String.make acc '}')
          else "Scheme.Cons { Scheme.car = " ^ a.name ^
            "; Scheme.cdr = Scheme.Nil " ^ (String.make (acc+1) '}')
      | [a :: b] ->
          "Scheme.Cons {Scheme.car = " ^ a.name ^
          "; Scheme.cdr = " ^ (loop (acc+1) b) ]
    in do {
      Printf.printf "%s -> " (loop 0 args);
      List.iter (fun arg ->
        if arg.mut then
          Printf.printf "let %s = ref %s in "
            arg.name arg.name else ())
        args;
      emit body;
      Printf.printf "| _ -> failwith \"incorrect arity\" ]))"
    }
  } else do {
    Printf.printf "(Scheme.Lambda%d (fun %s -> " (List.length args)
      (if List.length args = 0 then "()" else String.concat " " (List.map
      (fun a -> a.name) args));
    List.iter (fun arg ->
      if arg.mut then
        Printf.printf "let %s = ref %s in " arg.name arg.name
      else ()) args;
    emit body;
    Printf.printf "))"
  };
