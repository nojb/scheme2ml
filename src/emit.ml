type binding =
  [ Variable of ref bool and string
  (* bool is mutable flag, string is Ocaml name *)
  | Builtin of option (int * string) and list (int * string) and string ];
  (* int is arity, string is Ocaml name *)

value binding_name = fun
  [ Variable _ name
  | Builtin _ _ name -> name ];

value binding_mutable = fun
  [ Variable mut _ -> mut.val
  | Builtin _ _ _ -> False ];

type t =
  [ Quote of Scheme.t
  | Reference of binding
  | Begin of list t
  | Lambda of bool and list binding and t (* bool indicates varargs *)
  | If of t and t and t
  (*| Define of binding and t*)
  | Set of binding and t
  | Let of list binding and list t and t (* (let ...) and (let* ...) *)
  | LetRec of list binding and list t and t (* (letrec ...) *)
  | Application of t and list t ];

value rec emit_quote = fun
  [ Scheme.Num n ->
    if Num.eq_num n (Num.num_of_int (Num.int_of_num n)) then
      Printf.printf "(Scheme.Num (Num.num_of_int (%d)))" (Num.int_of_num n)
    else
      Printf.printf "(Scheme.Num (Num.num_of_string \"%s\"))"
        (Num.string_of_num n)
  | Scheme.Char char ->
      Printf.printf "(Scheme.Char '%s')" (Char.escaped char)
  | Scheme.String string ->
      Printf.printf "(Scheme.String \"%s\")" (String.escaped string)
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
  | Scheme.Lambda _ -> failwith "Emit.emit_quote" ]

and emit_separated sep = fun
  [ [] -> ()
  | [a] -> emit a
  | [a :: b] -> do {
      emit a;
      Printf.printf "%s" sep;
      emit_separated sep b
    } ]

and emit = fun
  [ Quote q -> emit_quote q
  | Reference (Variable mut name) ->
      if mut.val then
        Printf.printf "%s.val" name
      else
        Printf.printf "%s" name
  | Reference (Builtin (Some (0, varargs)) _ _) ->
    Printf.printf "(Scheme.Lambda %s)" varargs
  | Reference (Builtin (Some (fixed, varargs)) _ name) -> do {
      Printf.printf "(Lambda (fun args -> match args with [";
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
  | Reference (Builtin None impls name) -> do {
      Printf.printf "(Lambda (fun args -> match args with [";
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
    }
  | Begin ls -> do {
      Printf.printf "do { ";
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
      Printf.printf "}"
    }
  (*| Define b exp -> do {
      Printf.printf "value rec %s = " (binding_name b);
      if binding_mutable b then do {
        Printf.printf "(ref (";
        emit exp;
        Printf.printf "))"
      } else emit exp
    }*)
  | Set b exp -> do {
      Printf.printf "(do { %s.val := " (binding_name b);
      emit exp;
      Printf.printf " ; Scheme.Void })"
    }
  | LetRec variables inits body -> do {
      Printf.printf "(let rec ";
      let rec loop variables inits =
        match (variables, inits) with
        [ ([], []) -> Printf.printf "() = () in "
        | ([a], [b]) -> do {
            Printf.printf "%s = " (binding_name a);
            if binding_mutable a then
              Printf.printf "ref ("
            else ();
            emit b;
            if binding_mutable a then
              Printf.printf ")"
            else ();
            Printf.printf " in "
          }
        | ([a :: a'], [b :: b']) -> do {
            Printf.printf "%s = " (binding_name a);
            if binding_mutable a then
              Printf.printf "ref ("
            else ();
            emit b;
            if binding_mutable a then
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
  | Let variables inits body -> do {
    (* FIXME If one of the variables is
     * marked mutable, then the corresponding
     * init must be preceded by a `ref', like
     * above *)
      Printf.printf "(let (";
      let rec loop variables =
        match variables with
        [ [] -> Printf.printf ") = ("
        | [a] -> Printf.printf "%s) = (" (binding_name a)
        | [a :: b] -> do {
            Printf.printf "%s, " (binding_name a);
            loop b
        } ]
      in
      loop variables;
      let rec loop inits =
        match inits with
        [ [] -> Printf.printf ") in "
        | [a] -> do {
            emit a;
            Printf.printf ") in "
          }
        | [a :: b] -> do {
            emit a;
            Printf.printf ", ";
            loop b
        } ]
      in loop inits;
      emit body;
      Printf.printf ")"
    }
  | Lambda varargs args body -> do {
      Printf.printf "(Scheme.Lambda (fun args -> ";
      Printf.printf "match args with [";
      let rec loop acc args =
        match args with
        [ [] -> "Scheme.Nil " ^ String.make acc '}'
        | [a] ->
            if varargs then (binding_name a) ^ (String.make acc '}')
            else "Scheme.Cons { Scheme.car = " ^ (binding_name a) ^
              "; Scheme.cdr = Scheme.Nil " ^ (String.make (acc+1) '}')
        | [a :: b] ->
            "Scheme.Cons {Scheme.car = " ^ (binding_name a) ^
            "; Scheme.cdr = " ^ (loop (acc+1) b) ]
      in do {
        Printf.printf "%s -> " (loop 0 args);
        List.iter (fun arg ->
          if (binding_mutable arg) then
            Printf.printf "let %s = ref %s in "
              (binding_name arg) (binding_name arg) else ())
          args;
        emit body;
        Printf.printf "| _ -> failwith \"incorrect arity\" ]))"
      }
    }
  | If cond iftrue iffalse -> do {
      Printf.printf "(if (Scheme.is_true ";
      emit cond;
      Printf.printf ") then ";
      emit iftrue;
      Printf.printf " else ";
      emit iffalse;
      Printf.printf ")"
    }
  | Application (Reference (Builtin (Some (0, "Scheme.vector"))
      [] "vector")) args -> do {
      Printf.printf "(Scheme.Vector [|";
      emit_separated ";" args;
      Printf.printf "|])"
    }
  | Application (Reference (Builtin (Some (fixed, varargs)) impls name)) args -> do {
      let arity = List.length args in
      try let impl = List.assoc arity impls in do {
        Printf.printf "(%s " impl;
        if arity = 0 then Printf.printf "()"
        else List.iter emit args;
        Printf.printf ")"
      } with [ Not_found -> do {
        Printf.printf "(%s " varargs;
        let rec loop count args =
          if count > fixed then
            let rec loop2 count args =
              match args with
              [ [] -> Printf.printf "Scheme.Nil %s" (String.make count '}')
              | [a :: b] -> do {
                  Printf.printf "(Scheme.Cons { Scheme.car = ";
                  emit a;
                  Printf.printf "; Scheme.cdr = ";
                  loop (count+1) b;
                  Printf.printf ")"
                } ]
            in loop2 0 args
          else match args with
          [ [] -> failwith (name ^ ": bad arity")
          | [a :: b] -> do {
              emit a;
              loop (count+1) b
            } ]
        in do {
          loop 1 args;
          Printf.printf ")"
        }
      } ]
    }
  | Application (Reference (Builtin None impls name)) args -> do {
      let arity = List.length args in
      let impl =
        try List.assoc arity impls
        with [ Not_found -> failwith (name ^ ": bad arity") ]
      in do {
        Printf.printf "(%s " impl;
        if arity = 0 then Printf.printf "()"
        else emit_separated " " args;
        Printf.printf ")"
      }
    }

    (*let rec loop rem rest =
      if rem = 0 then
        if arity < 0 then do {
          Printf.printf "(";
          let rec loop acc rest =
            match rest with
            [ [] -> Printf.printf "Scheme.Nil %s" (String.make acc '}')
            | [a :: b] -> do {
                Printf.printf "Scheme.Cons { Scheme.car = ";
                (emit a);
                Printf.printf "; Scheme.cdr = ";
                (loop (acc+1) b)
              } ]
          in loop 0 rest;
          Printf.printf ")"
        } else if List.length rest > 0 then
          failwith (name ^ ": bad arity")
        else ()
      else match rest with
      [ [a :: b] -> do {
          emit a;
          Printf.printf " ";
          loop (rem-1) b
        }
      | [] -> failwith (name ^ ": bad arity") ]
    in do {
      Printf.printf "(%s " name;
      loop (if arity >= 0 then arity else -arity-1) args;
      if (arity = 0) then Printf.printf "()"
      else ();
      Printf.printf ")"
    }*)
  | Application f args -> do {
      Printf.printf "(Scheme.apply ";
      emit f;
      Printf.printf "(";
      let rec loop acc args =
        match args with
        [ [] -> Printf.printf "Scheme.Nil %s" (String.make acc '}')
        | [a :: b] -> do {
            Printf.printf "Scheme.Cons { Scheme.car = ";
            (emit a);
            Printf.printf "; Scheme.cdr = ";
            (loop (acc+1) b)
          } ]
      in loop 0 args; Printf.printf "))"
    } ];
