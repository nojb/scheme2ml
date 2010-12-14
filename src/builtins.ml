value builtins = [
  ("+", Some (0, "Scheme.add"), [(2, "Scheme.add2")]);
  ("*", Some (0, "Scheme.mul"), [(2, "Scheme.mul2")]);
  ("-", Some (0, "Scheme.sub"), [(2, "Scheme.sub2")]);
  ("eq?", None, [(2, "Scheme.is_eq")]);
  ("eqv?", None, [(2, "Scheme.is_eqv")]);
  ("equal?", None, [(2, "Scheme.is_equal")]);
  ("car", None, [(1, "Scheme.car")]);
  ("cdr", None, [(1, "Scheme.cdr")]);
  ("caar", None, [(1, "Scheme.caar")]);
  ("cadr", None, [(1, "Scheme.cadr")]);
  ("cddr", None, [(1, "Scheme.cddr")]);
  ("caaar", None, [(1, "Scheme.caaar")]);
  ("caddr", None, [(1, "Scheme.caddr")]);
  ("caadr", None, [(1, "Scheme.caadr")]);
  ("cadddr", None, [(1, "Scheme.cadddr")]);
  ("display", None, [(1, "Scheme.display")]);
  ("zero?", None, [(1, "Scheme.is_zero")]);
  ("integer?", None, [(1, "Scheme.is_integer")]);
  ("=", Some (2, "Scheme.eq"), []);
  ("<", Some (2, "Scheme.lt"), []);
  (">", Some (2, "Scheme.gt"), []);
  ("<=", Some (2, "Scheme.le"), []);
  (">=", Some (2, "Scheme.ge"), []);
  ("newline", None,
    [(0, "Scheme.newline");(1, "Scheme.newline_to_port")]);
  ("write-char", None,
    [(1, "Scheme.write_char"); (2, "Scheme.write_char_to_port")]);
  ("read", None, [(0, "Scheme_read.read")]);
  ("number->string", None, [(1, "Scheme.number_to_string")]);
  ("boolean?", None, [(1, "Scheme.is_boolean")]);
  ("not", None, [(1, "Scheme._not")]);
  ("pair?", None, [(1, "Scheme.is_pair")]);
  ("cons", None, [(2, "Scheme.cons")]);
  ("set-car!", None, [(2, "Scheme.set_car_bang")]);
  ("set-cdr!", None, [(2, "Scheme.set_cdr_bang")]);
  ("null?", None, [(1, "Scheme.is_null")]);
  ("map", Some (1, "Scheme.map"), []);
  ("for-each", Some (1, "Scheme.for_each"), []);
  ("list?", None, [(1, "Scheme.is_list")]);
  ("list", Some (0, "Scheme.list"), []);
  ("length", None, [(1, "Scheme.length")]);
  ("append", Some (0, "Scheme.append"), [(2,"Scheme.append2")]);
  ("reverse", None, [(1, "Scheme.reverse")]);
  ("list-tail", None, [(2, "Scheme.list_tail")]);
  ("list-ref", None, [(2, "Scheme.list_ref")]);
  ("memq", None, [(2, "Scheme.memq")]);
  ("memv", None, [(2, "Scheme.memv")]);
  ("member", None, [(2, "Scheme.member")]);
  ("assq", None, [(2, "Scheme.assq")]);
  ("assv", None, [(2, "Scheme.assv")]);
  ("assoc", None, [(2, "Scheme.assoc")]);
  ("symbol?", None, [(1, "Scheme.is_symbol")]);
  ("symbol->string", None, [(1, "Scheme.symbol_to_string")]);
  ("string->symbol", None, [(1, "Scheme.string_to_symbol")]);
  ("vector?", None, [(1, "Scheme.is_vector")]);
  ("vector", Some (0, "Scheme.vector"), []);
  ("make-vector", None, [(1, "Scheme.make_vector")]);
  ("vector-length", None, [(1, "Scheme.vector_length")]);
  ("vector-ref", None, [(2, "Scheme.vector_ref")]);
  ("vector-set!", None, [(3, "Scheme.vector_set")]);
  ("vector->list", None, [(1, "Scheme.vector_to_list")]);
  ("list->vector", None, [(1, "Scheme.list_to_vector")]);
  ("vector-fill!", None, [(2, "Scheme.vector_fill")]);
  ("char?", None, [(1, "Scheme.is_char")]);
  ("char=?", None, [(2, "Scheme.is_char_eq")]);
  ("char-alphabetic?", None, [(1, "Scheme.is_char_alphabetic")]);
  ("char-numeric?", None, [(1, "Scheme.is_char_numeric")]);
  ("char-whitespace?", None, [(1, "Scheme.is_char_whitespace")]);
  ("char-upper-case?", None, [(1, "Scheme.is_char_upper_case")]);
  ("char-lower-case?", None, [(1, "Scheme.is_char_lower_case")]);
  ("char->integer", None, [(1, "Scheme.char_to_integer")]);
  ("integer->char", None, [(1, "Scheme.integer_to_char")]);
  ("string-length", None, [(1, "Scheme.string_length")]);
  ("string-ref", None, [(1, "Scheme.string_ref")]);
  ("string-set!", None, [(3, "Scheme.string_set")]);
  ("substring", None, [(3, "Scheme.substring")]);
  ("string-append", Some (0, "Scheme.string_append"), []);
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
  ("close-output-port", None, [(1, "Scheme.close_output_port")]);
  ("force", None, [(1, "Scheme.force")]);
  ("error", Some (0, "Scheme.error"), [])
];
