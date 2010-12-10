value builtins = [
  ("+", Some (0, "Scheme.add"), [(2, "Scheme.add2")]);
  ("*", Some (0, "Scheme.mul"), [(2, "Scheme.mul2")]);
  ("-", Some (0, "Scheme.sub"), [(2, "Scheme.sub2")]);
  ("car", None, [(1, "Scheme.car")]);
  ("cdr", None, [(1, "Scheme.cdr")]);
  ("display", None, [(1, "Scheme.display")]);
  ("zero?", None, [(1, "Scheme.is_zero")]);
  ("newline", None, [(0, "Scheme.newline")]);
  ("read", None, [(0, "Scheme.read")])
];

value populate env =
  List.fold_left (fun env (name, varargs, impls) ->
    Ast.M.add name (Emit.Builtin varargs impls name) env) env builtins;
