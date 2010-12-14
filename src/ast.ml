module M = Emit.M; (* Map.Make String; *)

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

value mangle_count = ref 0;

value mangle s =
  let count = mangle_count.val in do {
    mangle_count.val := mangle_count.val + 1;
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
  String.concat "" ["_" ^ (string_of_int count) ^ "_" ::
    List.map mangle_char (string_to_list s)]};

exception NotAList;

value rec iter_cons f cons =
  match cons with
  [ Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = b
    } -> do {
      f a;
      iter_cons f b
    }
  | Scheme.Nil -> ()
  | _ -> raise NotAList ];

value rec fold_cons f f_last f_nil z cons =
  match cons with
  [ Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = Scheme.Nil
    } -> f_last z a
  | Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = b
    } -> fold_cons f f_last f_nil (f z a) b
  | Scheme.Nil -> f_nil
  | _ -> raise NotAList ];

value rec fold_right_cons f cons z =
  match cons with
  [ Scheme.Nil -> z
  | Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = Scheme.Nil
    } -> f a z
  | Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = b
    } ->
      f a (fold_right_cons f b z)
  | _ -> raise NotAList ];

value rec map_to_list f cons =
  match cons with
  [ Scheme.Nil -> []
  | Scheme.Cons cons ->
    [f cons.Scheme.car :: map_to_list f cons.Scheme.cdr]
  | _ -> raise NotAList ];

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

value rec analyze_program x =
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
    let syntax_forms = [
      ("begin", analyze_begin);
      ("lambda", analyze_lambda);
    (*  ("define", analyze_define); *)
      ("set!", analyze_set);
      ("quote", analyze_quote);
      ("quasiquote", analyze_quasiquote);
      ("if", analyze_alternative);
      ("let", analyze_let);
      ("let*", analyze_let_star);
      ("letrec", analyze_letrec);
      ("cond", analyze_cond);
      ("and", analyze_and);
      ("or", analyze_or);
      ("case", analyze_case) ]
    in
    let env = List.fold_left (fun env (name, varargs, impls) ->
      M.add name (Emit.Builtin varargs impls name) env) M.empty Builtins.builtins
    in
    let env = List.fold_left (fun env (name, impl) ->
      M.add name (Emit.Syntax impl) env) env syntax_forms
    in
    (* Printf.eprintf "DEBUG:\n%s\n%!" (Scheme.to_string x'); *)
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

and analyze_cons qq env car cdr =
  match car with
  [ Scheme.Symbol s ->
      try match M.find s env with
      [ Emit.Syntax syn -> syn qq env cdr
      | _ ->
          Emit.Application (analyze qq env car) (map_to_list (analyze qq env) cdr) ]
      with [ Not_found -> failwith ("unknown identifier: " ^ s) ]
  | _ -> Emit.Application (analyze qq env car) (map_to_list (analyze qq env) cdr) ]

and analyze_begin qq env cdr =
  try Emit.Begin (map_to_list (analyze qq env) cdr)
  with [ NotAList -> failwith "bad syntax in (begin)" ]

and analyze_quote qq env cdr =
  match cdr with
  [ Scheme.Cons {Scheme.car=a;Scheme.cdr=Scheme.Nil} -> Emit.Quote a
  | _ -> failwith "bad syntax in (quote)" ]

and analyze_body qq env cdr =
  let rec loop cdr =
    match cdr with
    [ Scheme.Cons {
        Scheme.car = Scheme.Cons {
          Scheme.car = Scheme.Symbol "define";
          Scheme.cdr = Scheme.Cons {
            Scheme.car = a;
            Scheme.cdr = b
          }
        };
        cdr = rest
      } ->
        match a with
        [ Scheme.Cons {
            Scheme.car = (Scheme.Symbol _ as name);
            Scheme.cdr = args
          } ->
            let (begin', rest') = loop rest in
            (Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = name;
                Scheme.cdr = Scheme.Cons {
                  Scheme.car = Scheme.Cons {
                    Scheme.car = Scheme.Symbol "lambda";
                    Scheme.cdr = Scheme.Cons {
                      Scheme.car = args;
                      Scheme.cdr = b
                    }
                  };
                  Scheme.cdr = Scheme.Nil
                }
              };
              Scheme.cdr = begin'
            }, rest')
        | Scheme.Symbol _ as name ->
            let (begin', rest') = loop rest in
            (Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = name;
                Scheme.cdr = b
              };
              Scheme.cdr = begin'
            }, rest')
        | _ -> failwith "bad syntax in (define)" ]
    | Scheme.Cons {
        Scheme.car = Scheme.Cons {
          Scheme.car = Scheme.Symbol "begin";
          Scheme.cdr = defs
        };
        Scheme.cdr = rest
      } -> assert False
        (* let (begin', rest') = loop rest in
        match rest' with
        [ Nil -> Scheme.append begin' (loop rest)
        | _ -> failwith "bad syntax in (begin)" ] *)
        (* let (begin', rest') = loop rest in
        let rec help defs =
          match defs with
          [ Scheme.Cons {
              Scheme.car = Scheme.Cons {
                Scheme.car = Scheme.Symbol "define";
                Scheme.cdr = def
              };
              Scheme.cdr = rest
            } ->
*)
    | x -> (Scheme.Nil, x) ]
  in
  let (begin, rest) = loop cdr in
  match begin with
  [ Scheme.Nil -> Emit.Begin (map_to_list (analyze qq env) rest)
  | _ ->
    analyze qq env (Scheme.Cons {
      Scheme.car = Scheme.Symbol "letrec";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = begin;
        Scheme.cdr = rest
      }
    }) ]

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
      Emit.Let variables' inits' (analyze_body qq env' body)
  | _ -> failwith "bad syntax in (letrec)" ]

and analyze_let qq env cdr =
  match cdr with
  [ Scheme.Cons { (* named let *)
      Scheme.car = (Scheme.Symbol _ as v);
      Scheme.cdr = Scheme.Cons {
        Scheme.car = bindings;
        Scheme.cdr = body
      }
    } ->
      let help binding (names, values) =
        match binding with
        [ Scheme.Cons {
            Scheme.car = (Scheme.Symbol _ as v);
            Scheme.cdr = Scheme.Cons {
              Scheme.car = e;
              Scheme.cdr = Scheme.Nil
            }
        } -> (Scheme.Cons {Scheme.car = v; Scheme.cdr = names},
              Scheme.Cons {Scheme.car = e; Scheme.cdr = values})
        | _ -> failwith "bad syntax in (let)" ]
      in
      let (binding_names, binding_values) =
        fold_right_cons help bindings (Scheme.Nil, Scheme.Nil)
      in
      analyze_letrec qq env (
        Scheme.Cons {
          Scheme.car = Scheme.Cons {
            Scheme.car = Scheme.Cons {
              Scheme.car = v;
              Scheme.cdr = Scheme.Cons {
                Scheme.car = Scheme.Cons {
                  Scheme.car = Scheme.Symbol "lambda";
                  Scheme.cdr = Scheme.Cons {
                    Scheme.car = binding_names;
                    Scheme.cdr = body
                  }
                };
                Scheme.cdr = Scheme.Nil
              }
            };
            Scheme.cdr = Scheme.Nil
          };
          Scheme.cdr = Scheme.Cons {
            Scheme.car = Scheme.Cons {
              Scheme.car = Scheme.Symbol "loop";
              Scheme.cdr = binding_values
            };
            Scheme.cdr = Scheme.Nil
          }
        })
  | Scheme.Cons {
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
      in Emit.Let variables' inits (analyze_body qq env' body)
  | _ -> failwith "bad syntax in (let)" ]

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
      | Emit.Syntax _ -> failwith "cannot! a syntax"
      | Emit.Builtin _ _ _ -> failwith "cannot set! a builtin" ]
      with [ Not_found -> failwith "cannot set! an undefined variable" ]
  | _ -> failwith "bad syntax in set!" ]

  (*
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

  *)

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
        | _ -> failwith "bad syntax in (lambda)" ]
          in let (varargs, args) = loop cons' in
          let args' = List.map (fun arg -> Emit.Variable (ref False) (mangle arg)) args in
          let env' = List.fold_left2
            (fun start rest rest' -> M.add rest rest' start) env args args' in
          Emit.Lambda varargs args' (analyze_body qq env' cons.Scheme.cdr)
    | Scheme.Symbol name ->
        let arg' = Emit.Variable (ref False) (mangle name) in
        let env' = M.add name arg' env in
        Emit.Lambda True [arg'] (analyze_body qq env' cons.Scheme.cdr)
    | Scheme.Nil -> (* zero-arity *)
        Emit.Lambda False [] (analyze_body qq env cons.Scheme.cdr)
    | _ -> failwith "bad syntax in (lambda)" ]
  | _ -> failwith "bad syntax in (lambda)" ]

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
          Scheme.car = Scheme.Symbol "else";
          Scheme.cdr = expressions
        };
        Scheme.cdr = Scheme.Nil
      } ->
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

(* quasiquote expander -- not optimizing
 *
 * Taken from Bawden, Quasiquotations in Lips *)

and analyze_quasiquote qq env cdr =
  match cdr with
  [ Scheme.Cons{Scheme.car=a;Scheme.cdr=Scheme.Nil}->
  let append = Emit.Reference
    (Emit.Builtin (Some (0, "Scheme.append")) [] "append") in
  let cons = Emit.Reference (Emit.Builtin None [(2, "Scheme.cons")] "cons") in
  match a with
  [ Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } ->
      if qq = 1 then
        analyze (qq-1) env x
      else
        Emit.Application cons
          [Emit.Quote (Scheme.Symbol "unquote");
          analyze_quasiquote_list (qq-1) env x]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote-splicing";
      Scheme.cdr = _
    } -> failwith "(unquote-splicing) not allowed here"
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol "quasiquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } -> Emit.Application cons
          [Emit.Quote (Scheme.Symbol "quasiquote");
          analyze_quasiquote_list (qq+1) env x]
  | Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = b
    } ->
      Emit.Application append
        [analyze_quasiquote_list qq env a;
          analyze_quasiquote qq env b]
  | _ -> Emit.Quote a ]
  | _ -> failwith "bad syntax in (quasiquote)" ]

and analyze_quasiquote_list qq env car =
  let append = Emit.Reference (Emit.Builtin (Some (0, "Scheme.append")) []
  "append") in
  let list = Emit.Reference (Emit.Builtin (Some (0, "Scheme.list")) [] "list") in
  let cons = Emit.Reference (Emit.Builtin None [(2, "Scheme.cons")] "cons") in
  match car with
  [ Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } ->
      if qq = 1 then
        Emit.Application list [analyze (qq-1) env x]
      else
        Emit.Application list
        [Emit.Application cons
          [Emit.Quote (Scheme.Symbol "unquote");
          analyze_quasiquote_list (qq-1) env x]]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote-splicing";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } ->
      if qq = 1 then
        analyze (qq-1) env x
      else
        Emit.Application list
          [Emit.Application cons
            [Emit.Quote (Scheme.Symbol "unquote-splicing");
            analyze_quasiquote_list (qq-1) env x]]
  | Scheme.Cons {
      Scheme.car = Scheme.Symbol "quasiquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = x;
        Scheme.cdr = Scheme.Nil
      }
    } ->
      Emit.Application list
        [Emit.Application cons
          [Emit.Quote (Scheme.Symbol "quasiquote");
          analyze_quasiquote_list (qq+1) env x]]
  | Scheme.Cons {
      Scheme.car = a;
      Scheme.cdr = b
    } ->
      Emit.Application list [Emit.Application append
        [analyze_quasiquote_list qq env a;
        analyze_quasiquote qq env b]]
  | _ -> Emit.Quote
    (Scheme.Cons {Scheme.car = car; Scheme.cdr = Scheme.Nil}) ]

and analyze_case qq env cdr =
  match cdr with
  [ Scheme.Cons {
      Scheme.car = key;
      Scheme.cdr = clauses
    } ->
      let help_last emitted clause =
        match clause with
        [ Scheme.Cons {
            Scheme.car = Scheme.Symbol "else";
            Scheme.cdr = body
          } ->
            try
              Emit.Case (analyze qq env key)
                (List.rev emitted) (Emit.Begin
                  (map_to_list (analyze qq env) body))
            with [ NotAList -> failwith "bad syntax in (case)" ]
        | Scheme.Cons {
            Scheme.car = cond;
            Scheme.cdr = body
          } ->
            try let emitted =
              [(map_to_list (fun x -> x) cond,
                  Emit.Begin
                    (map_to_list (analyze qq env) body)) :: emitted]
            in
            Emit.Case (analyze qq env key)
              (List.rev emitted) (Emit.Quote Scheme.Void)
            with [ NotAList -> failwith "bad syntax in (case)" ]
        | _ -> failwith "bad syntax in (case)" ]
      in
      let help emitted clause =
        match clause with
        [ Scheme.Cons {
            Scheme.car = cond;
            Scheme.cdr = body
          } ->
            try
              [(map_to_list (fun x -> x) cond,
                  Emit.Begin
                    (map_to_list (analyze qq env) body)) :: emitted]
            with [ NotAList -> failwith "bad syntax in (case)" ]
        | _ -> failwith "bad syntax in (case)" ]
      in
      fold_cons help help_last (Emit.Quote Scheme.Void) [] clauses
  | Scheme.Nil -> Emit.Quote Scheme.Void
  | _ -> failwith "bad syntax in (case)" ];

