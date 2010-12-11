module M = Map.Make (struct
  type t = string;
  value compare x y =
    String.compare (String.lowercase x) (String.lowercase y);
  end);

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

value mangle s =
  let alphanumeric c =
    (c >= 'a' && c <= 'z') ||
    (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9')
  in
  let string_to_list s =
    let l = String.length s in
    let rec loop i =
      if i >= l then []
      else [s.[i] :: loop (i+1)]
    in loop 0
  in
  let mangle_char c =
    if alphanumeric c then (String.make 1 c)
    else ("_" ^ (string_of_int (Char.code c)))
  in
  String.concat "" ["__" :: List.map mangle_char (string_to_list s)];

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

value rec analyze_program env x =
  let rec loop x =
    match x with
    [ [] -> Scheme.Nil
    | [a :: b] ->
      match a with
      [ Scheme.Cons {
          Scheme.car = Scheme.Symbol "define";
          Scheme.cdr = define_cdr
        } ->
          match define_cdr with
          [ Scheme.Cons ({
            Scheme.car = Scheme.Symbol _;
            Scheme.cdr = init
          } as cons) ->
        Scheme.Cons {
          Scheme.car =
        Scheme.Cons {
          Scheme.car = Scheme.Symbol "letrec";
          Scheme.cdr = Scheme.Cons {
            Scheme.car = Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = cons.Scheme.car;
                Scheme.cdr = init
              };
              Scheme.cdr = Scheme.Nil
            };
            Scheme.cdr = loop b
          }
        };
        Scheme.cdr = Scheme.Nil
        }
      | Scheme.Cons {
            Scheme.car = Scheme.Cons ({
              Scheme.car = Scheme.Symbol _;
              Scheme.cdr = arguments
            } as cons);
            Scheme.cdr = body
        } ->
        Scheme.Cons {
          Scheme.car = Scheme.Cons {
          Scheme.car = Scheme.Symbol "letrec";
          Scheme.cdr = Scheme.Cons {
            Scheme.car = Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = cons.Scheme.car;
                Scheme.cdr = Scheme.Cons {
                  Scheme.car = Scheme.Cons {
                    Scheme.car = Scheme.Symbol "lambda";
                    Scheme.cdr = Scheme.Cons {
                      Scheme.car = arguments;
                      Scheme.cdr = body
                    }
                  };
                  Scheme.cdr = Scheme.Nil
                }
              };
              Scheme.cdr = Scheme.Nil
            };
            Scheme.cdr = loop b
          }
          };
          Scheme.cdr = Scheme.Nil
        }
      | _ -> failwith "bad syntax in (define)" ]
      | x ->
        Scheme.Cons {
          Scheme.car = x;
          Scheme.cdr = loop b
        } ] ]
  in
  let x' = Scheme.Cons {
    Scheme.car = Scheme.Symbol "begin";
    Scheme.cdr = loop x
  } in do {
    (*Printf.eprintf "DEBUG:\n%s\n%!" (Scheme.to_string x');*)
    analyze 0 env x'
  }

and analyze qq env x =
  match x with
  [ Scheme.Num _
  | Scheme.Boolean _
  | Scheme.Nil
  | Scheme.Char _
  | Scheme.String _
  | Scheme.Vector _ -> Emit.Quote x
  | Scheme.Symbol s ->
    try Emit.Reference (M.find s env)
    with [ Not_found -> failwith ("unknown identifier: " ^ s) ]
  | Scheme.Cons cons -> analyze_cons qq env cons.Scheme.car cons.Scheme.cdr
  | _ -> failwith "Ast.analyze: unhandled scheme datum" ]

and map_to_list f = fun
  [ Scheme.Nil -> []
  | Scheme.Cons cons ->
    [f cons.Scheme.car :: map_to_list f cons.Scheme.cdr]
  | _ -> failwith "Ast.to_list: not a list" ]

and analyze_cons qq env car cdr =
  match car with
  [ Scheme.Symbol s ->
    match String.lowercase s with
    [ "begin" -> Emit.Begin (map_to_list (analyze qq env) cdr)
    | "lambda" -> analyze_lambda qq env cdr
    | "define" -> analyze_define qq env cdr
    | "set!" -> analyze_set qq env cdr
    | "quote" ->
      match cdr with
      [ Scheme.Cons {
          Scheme.car = a;
          Scheme.cdr = Scheme.Nil
        } -> Emit.Quote a
      | _ -> failwith "bad syntax in (quote)" ]
    | "quasiquote" ->
      match cdr with
      [ Scheme.Cons {
          Scheme.car = a;
          Scheme.cdr = Scheme.Nil
        } -> analyze_quasiquote (qq+1) env a None
      | _ -> failwith "bad syntax in (quasiquote)" ]
    | "if" -> analyze_alternative qq env cdr
    | "let" -> analyze_let qq env cdr 
    | "let*" -> analyze_let_star qq env cdr
    | "letrec" -> analyze_letrec qq env cdr
    | "cond" -> analyze_cond qq env cdr
    | "and" -> analyze_and qq env cdr
    | "or" -> analyze_or qq env cdr
    | _ -> Emit.Application (analyze qq env car) (map_to_list (analyze qq env) cdr) ]
  | _ -> Emit.Application (analyze qq env car) (map_to_list (analyze qq env) cdr) ]

and analyze_let_star qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = bindings;
      Scheme.cdr = body
    } ->
      let rec loop bindings =
        match bindings with
        [ Scheme.Nil -> Scheme.Cons {
            Scheme.car = Scheme.Nil;
            Scheme.cdr = body
          }
        | Scheme.Cons {
            Scheme.car = binding1;
            Scheme.cdr = bindings
          } -> Scheme.Cons {
            Scheme.car = Scheme.Cons {
              Scheme.car = binding1;
              Scheme.cdr = Scheme.Nil
            };
            Scheme.cdr = Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = Scheme.Symbol "let";
                Scheme.cdr = loop bindings
              };
              Scheme.cdr = Scheme.Nil
            }
          }
        | _ -> failwith "bad syntax in (let*)" ]
      in analyze_let qq env (loop bindings)
  | _ -> failwith "bad syntax in (let*)" ]

and analyze_letrec qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = bindings;
      Scheme.cdr = body
    } ->
      let rec loop bindings =
        match bindings with
        [ Scheme.Nil -> []
        | Scheme.Cons {
            Scheme.car = binding1;
            Scheme.cdr = bindings
          } ->
            match binding1 with
            [ Scheme.Cons {
                Scheme.car = Scheme.Symbol variable1;
                Scheme.cdr = Scheme.Cons {
                  Scheme.car = init1;
                  Scheme.cdr = Scheme.Nil
                }
              } -> [(variable1, init1) :: loop bindings]
            | _ -> failwith "bad syntax in (letrec)" ]
        | _ -> failwith "bad syntax in (letrec)" ]
      in
      let (variables, inits) = List.split (loop bindings) in
      let variables' = List.map (fun variable ->
        Emit.Variable (ref False) (mangle variable)) variables in
      let env' = List.fold_left2
        (fun env variable variable' -> M.add variable variable' env)
        env variables variables' in
      let inits' = List.map (analyze qq env') inits in
      Emit.LetRec variables' inits'
        (Emit.Begin (map_to_list (analyze qq env') body))
  | _ -> failwith "bad syntax in (letrec)" ]

and analyze_let qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = bindings;
      Scheme.cdr = body
    } ->
      (* bindings : list (string * Emit.t) *)
      let rec loop bindings =
        match bindings with
        [ Scheme.Nil -> []
        | Scheme.Cons {
            Scheme.car = binding1;
            Scheme.cdr = bindings
          } ->
            match binding1 with
            [ Scheme.Cons {
                Scheme.car = Scheme.Symbol variable1;
                Scheme.cdr = Scheme.Cons {
                  Scheme.car = init1;
                  Scheme.cdr = Scheme.Nil
                }
              } -> [(variable1, analyze qq env init1) :: loop bindings]
            | _ -> failwith "bad syntax in (let)" ]
        | _ -> failwith "bad syntax in (let)" ]
      in let (variables, inits) = List.split (loop bindings)
      in let variables' = List.map (fun variable ->
        Emit.Variable (ref False) (mangle variable)) variables
      in let env' = List.fold_left2
        (fun env variable variable' -> M.add variable variable' env) env variables variables'
      in Emit.Let variables' inits
        (Emit.Begin (map_to_list (analyze qq env') body))
  | _ -> failwith "analyze_let: malformed (let)" ]

and analyze_set qq env cdr =
  match cdr with
  [ Scheme.Cons
      {Scheme.car = Scheme.Symbol name; Scheme.cdr = Scheme.Cons
        {Scheme.car = exp; Scheme.cdr = Scheme.Nil}} ->
      try match M.find name env with
      [ Emit.Variable mut name as v -> do {
        mut.val := True;
        Emit.Set v (analyze qq env exp)
      }
      | Emit.Builtin _ _ _ -> failwith "cannot set! a builtin" ]
      with [ Not_found -> failwith "cannot set! an undefined variable" ]
  | _ -> failwith "bad syntax in set!" ]

and analyze_define qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = Scheme.Cons { (* (define (f arg1 ...) ...) *)
        Scheme.car = Scheme.Symbol name;
        Scheme.cdr = args
      };
      Scheme.cdr = body
    } ->
    let lam = Scheme.Cons {
      Scheme.car = Scheme.Symbol name;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = Scheme.Cons {
          Scheme.car = Scheme.Symbol "lambda";
          Scheme.cdr = Scheme.Cons {
            Scheme.car = args;
            Scheme.cdr = body
          }
        };
        Scheme.cdr = Scheme.Nil
      }
    }
    in analyze_define qq env lam
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol name;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = exp;
        Scheme.cdr = Scheme.Nil
      }
    } ->
    try match M.find name env with
    [ Emit.Builtin _ _ _ ->
      failwith ("Ast.analyze_define: cannot modify builtin: " ^ name)
    | (Emit.Variable mut name') as v -> do {
        mut.val := True;
        Emit.Set v (analyze qq (M.add name v env) exp)
    } ]
    with [ Not_found -> assert False ]
      (*let v = Emit.Variable (ref False) (mangle name) in
      let env' = M.add name v env in
      Emit.Define v (analyze env' exp) ] FIXME *)
  | _ -> failwith "define: bad syntax" ]

and analyze_lambda qq env cdr =
  match cdr with
  [ Scheme.Cons cons ->
    match cons.Scheme.car with
    [ Scheme.Cons cons' -> (* have argument list *)
      let rec loop cons' =
      match (cons'.Scheme.car, cons'.Scheme.cdr) with
      [ (Scheme.Symbol arg, Scheme.Nil) -> (False, [arg])
      | (Scheme.Symbol arg, Scheme.Cons cons') ->
        let (varargs, args) = loop cons' in
        (varargs, [arg :: args])
      | (Scheme.Symbol arg, Scheme.Symbol a) -> (True, [arg; a])
      | _ -> failwith "Ast.analyze_lambda: bad syntax in (lambda)" ]
      in let (varargs, args) = loop cons' in
      let args' = List.map (fun arg -> Emit.Variable (ref False) (mangle arg)) args in
      let env' = List.fold_left2
        (fun start rest rest' -> M.add rest rest' start) env args args' in
      Emit.Lambda varargs args'
        (Emit.Begin (map_to_list (analyze qq env') cons.Scheme.cdr))
    | Scheme.Symbol name ->
      let arg' = Emit.Variable (ref False) (mangle name) in
      let env' = M.add name arg' env in
      Emit.Lambda True [arg']
        (Emit.Begin (map_to_list (analyze qq env') cons.Scheme.cdr))
    | Scheme.Nil -> (* zero-arity *)
      Emit.Lambda False []
        (Emit.Begin (map_to_list (analyze qq env) cons.Scheme.cdr))
    | _ -> failwith "Ast.analyze_lambda: bad syntax in (lambda)" ]
  | _ -> failwith "Ast.analyze_lambda: bad syntax in (lambda)" ]

and analyze_alternative qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = condition;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = iftrue;
        Scheme.cdr = Scheme.Nil
      }
    } -> Emit.If (analyze qq env condition) (analyze qq env iftrue)
      (Emit.Quote Scheme.Void)
  | Scheme.Cons {
      Scheme.car = condition;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = iftrue;
        Scheme.cdr = Scheme.Cons {
          Scheme.car = iffalse;
          Scheme.cdr = Scheme.Nil
        }
      }
    } -> Emit.If (analyze qq env condition) (analyze qq env iftrue)
      (analyze qq env iffalse)
  | _ -> failwith "Ast.analyze_alternative: bad syntax in (if)" ]

and analyze_cond qq env cdr =
  let rec loop clauses =
    match clauses with
    [ Scheme.Cons { (* last clause *)
        Scheme.car = Scheme.Cons {
          Scheme.car = Scheme.Symbol s;
          Scheme.cdr = expressions
        };
        Scheme.cdr = Scheme.Nil
      } when String.lowercase s = "else" ->
        Emit.Begin (map_to_list (analyze qq env) expressions)
    | Scheme.Cons {
        Scheme.car = clause1;
        Scheme.cdr = clauses
      } -> analyze_clause clause1 clauses
    | Scheme.Nil -> Emit.Quote Scheme.Void
    | _ -> failwith "bad syntax in (cond)" ]
  and analyze_clause clause1 clauses =
    match clause1 with
    [ Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = Scheme.Nil
      } ->
        let v = Emit.Variable (ref False) "test" in
        Emit.Let [v] [analyze qq env test]
          (Emit.If (Emit.Reference v) (Emit.Reference v)
            (loop clauses))
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = Scheme.Cons {
          Scheme.car = Scheme.Symbol "=>";
          Scheme.cdr = Scheme.Cons {
            Scheme.car = expression;
            Scheme.cdr = Scheme.Nil
          }
        }
      } ->
        let v = Emit.Variable (ref False) "test" in
        Emit.Let [v] [analyze qq env test]
          (Emit.If (Emit.Reference v)
            (Emit.Application (analyze qq env expression) [Emit.Reference v])
            (loop clauses))
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = expressions
      } ->
        Emit.If (analyze qq env test)
          (Emit.Begin (map_to_list (analyze qq env) expressions))
          (loop clauses)
    | _ -> failwith "bad syntax in (cond)" ]
  in loop cdr

and analyze_and qq env cdr =
  let rec loop cdr =
    match cdr with
    [ Scheme.Nil -> Emit.Quote Scheme.t
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = Scheme.Nil
      } ->
        analyze qq env test
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = tests
      } ->
        let v = Emit.Variable (ref False) "test" in
        Emit.Let [v] [analyze qq env test]
          (Emit.If (Emit.Reference v) (loop tests)
            (Emit.Reference v))
    | _ -> failwith "bad syntax in (and)" ]
  in loop cdr

and analyze_or qq env cdr =
  let rec loop cdr =
    match cdr with
    [ Scheme.Nil -> Emit.Quote Scheme.f
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = Scheme.Nil
      } ->
        analyze qq env test
    | Scheme.Cons {
        Scheme.car = test;
        Scheme.cdr = tests
      } ->
        let v = Emit.Variable (ref False) "test" in
        Emit.Let [v] [analyze qq env test]
          (Emit.If (Emit.Reference v) (Emit.Reference v)
            (loop tests))
    | _ -> failwith "bad syntax in (or)" ]
  in loop cdr

and analyze_quasiquote qq env car splice =
  let splic = Emit.Builtin None [(2, "Scheme.splice")] "splice" in
  let cons = Emit.Builtin None [(2, "Scheme.cons")] "cons" in
  let vector = Emit.Builtin (Some (0, "Scheme.vector")) [] "vector" in
  match car with
  [ Scheme.Nil
  | Scheme.Num _
  | Scheme.Symbol _
  | Scheme.Boolean _
  | Scheme.Char _
  | Scheme.String _ ->
      match splice with
      [ None -> Emit.Quote car
      | Some z ->
          Emit.Application (Emit.Reference cons)
            [Emit.Quote car; z] ]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol s;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } when String.lowercase s = "unquote" ->
      if qq = 1 then
        match splice with
        [ None -> analyze (qq-1) env x
        | Some z ->
            Emit.Application (Emit.Reference cons)
              [analyze (qq-1) env x; z] ]
      else
        Emit.Application (Emit.Reference cons)
          [Emit.Quote (Scheme.Symbol "unquote");
            Emit.Application (Emit.Reference cons)
              [analyze_quasiquote (qq-1) env x (Some (Emit.Quote Scheme.Nil));
              Emit.Quote Scheme.Nil]]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol s;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } when String.lowercase s = "unquote-splicing" -> 
      if qq = 1 then
        match splice with
        [ None -> failwith "bad syntax in (unquote-splicing)"
        | Some (Emit.Quote Scheme.Nil) ->
            analyze (qq-1) env x
        | Some z ->
            Emit.Application (Emit.Reference splic)
              [analyze (qq-1) env x; z] ]
      else
        Emit.Application (Emit.Reference cons)
          [Emit.Quote (Scheme.Symbol "unquote-splicing");
            Emit.Application (Emit.Reference cons)
              [analyze_quasiquote (qq-1) env x (Some (Emit.Quote Scheme.Nil));
              Emit.Quote Scheme.Nil]]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol s;
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } when String.lowercase s = "quasiquote" ->
      if qq = 0 then
        assert False (* this can't happen! *)
        (* analyze_quasiquote (qq+1) env x *)
      else
        Emit.Application (Emit.Reference cons)
          [Emit.Quote (Scheme.Symbol "quasiquote");
            Emit.Application (Emit.Reference cons)
              [analyze_quasiquote (qq+1) env x (Some (Emit.Quote Scheme.Nil));
              Emit.Quote Scheme.Nil]]
  | Scheme.Cons {Scheme.car=a;Scheme.cdr=b} ->
      match splice with
      [ None -> analyze_quasiquote qq env a (Some (analyze_quasiquote qq env b None))
      | Some z ->
          Emit.Application (Emit.Reference cons)
            [analyze_quasiquote qq env a (Some (analyze_quasiquote qq env b None)); z]]
  | Scheme.Vector vec ->
      failwith "unquote-splicing in vectors not (yet) supported"
  (*| Scheme.Vector vec ->
      Emit.Application (Emit.Reference vector)
        (List.map (analyze_quasiquote qq env) (Array.to_list vec))*)
  | _ -> assert False ];
