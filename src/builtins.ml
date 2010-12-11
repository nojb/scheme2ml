value builtins = [
  ("+", Some (0, "Scheme.add"), [(2, "Scheme.add2")]);
  ("*", Some (0, "Scheme.mul"), [(2, "Scheme.mul2")]);
  ("-", Some (0, "Scheme.sub"), [(2, "Scheme.sub2")]);
  ("eq?", None, [(2, "Scheme.is_eq")]);
  ("car", None, [(1, "Scheme.car")]);
  ("cdr", None, [(1, "Scheme.cdr")]);
  ("display", None, [(1, "Scheme.display")]);
  ("zero?", None, [(1, "Scheme.is_zero")]);
  ("newline", None, [(0, "Scheme.newline")]);
  ("read", None, [(0, "Scheme_read.read")]);
  ("number->string", None, [(1, "Scheme.number_to_string")]);
  ("boolean?", None, [(1, "Scheme.is_boolean")]);
  ("not", None, [(1, "Scheme._not")]);
  ("pair?", None, [(1, "Scheme.is_pair")]);
  ("cons", None, [(2, "Scheme.cons")]);
  ("set-car!", None, [(2, "Scheme.set_car_bang")]);
  ("set-cdr!", None, [(2, "Scheme.set_cdr_bang")]);
  ("null?", None, [(1, "Scheme.is_null")]);
  ("list?", None, [(1, "Scheme.is_list")]);
  ("append", Some (0, "Scheme.append"), []);
  ("reverse", None, [(1, "Scheme.reverse")]);
  ("list-tail", None, [(2, "Scheme.list_tail")]);
  ("list-ref", None, [(2, "Scheme.list_ref")]);
  ("symbol?", None, [(1, "Scheme.is_symbol")]);
  ("symbol->string", None, [(1, "Scheme.symbol_to_string")]);
  ("string->symbol", None, [(1, "Scheme.string_to_symbol")]);
  ("vector?", None, [(1, "Scheme.is_vector")]);
  ("vector", Some (0, "Scheme.vector"), []);
  ("vector-length", None, [(1, "Scheme.vector_length")]);
  ("vector-ref", None, [(2, "Scheme.vector_ref")]);
  ("char?", None, [(1, "Scheme.is_char")]);
  ("char=?", None, [(1, "Scheme.is_char_eq")]);
  ("char->integer", None, [(1, "Scheme.char_to_integer")]);
  ("integer->char", None, [(1, "Scheme.integer_to_char")]);
  ("string-length", None, [(1, "Scheme.string_length")]);
  ("string-ref", None, [(1, "Scheme.string_ref")]);
  ("string-set!", None, [(3, "Scheme.string_set")]);
  ("substring", None, [(3, "Scheme.substring")]);
  ("string->list", None, [(1, "Scheme.string_to_list")]);
  ("list->string", None, [(1, "Scheme.list_to_string")]);
  ("string-copy", None, [(1, "Scheme.string_copy")]);
  ("string-fill!", None, [(1, "Scheme.string_fill")]);
  ("input-port?", None, [(1, "Scheme.is_input_port")]);
  ("output-port?", None, [(1, "Scheme.is_output_port")]);
  ("current-input-port", None, [(0, "Scheme.current_input_port")]);
  ("current-output-port", None, [(0, "Scheme.current_output_port")]);
  ("with-input-from-file", None, [(2, "Scheme.with_input_from_file")]);
  ("open-input-file", None, [(1, "Scheme.open_input_file")]);
  ("open-output-file", None, [(1, "Scheme.open_output_file")]);
  ("close-input-port", None, [(1, "Scheme.close_input_port")]);
  ("close-output-port", None, [(1, "Scheme.close_output_port")])
];

value populate env =
  List.fold_left (fun env (name, varargs, impls) ->
    Ast.M.add name (Emit.Builtin varargs impls name) env) env builtins;
