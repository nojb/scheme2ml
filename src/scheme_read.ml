open Scheme;

value read_from_port port =
  match port with
  [ In port ->
    match port.peek with
    [ None ->
      let lexbuf = Lexing.from_channel port.ch in
      Parser.ast Lexer.token lexbuf
    | Some c ->
      let lexbuf = Lexing.from_function (fun s n ->
        if n > 0 then do {
          s.[0] := c;
          port.peek := None;
          input port.ch s 1 (n-1)
        } else 0) in
      Parser.ast Lexer.token lexbuf ]
  | _ -> failwith "read: not a port" ];

value read () =
  read_from_port (In current_in.val);

value read_char_from_port port =
  match port with
  [ In port ->
    match port.peek with
    [ None -> try Char (input_char port.ch) with [ End_of_file -> Void ]
    | Some c -> do {
      port.peek := None;
      Char c
    } ]
  | _ -> failwith "read-char: not a port" ];

value read_char () =
  read_char_from_port (In current_in.val);

value peek_char_from_port port =
  match port with
  [ In port ->
    match port.peek with
    [ Some c -> Char c
    | None ->
      try do {
        let c = input_char port.ch in
        port.peek := Some c;
        Char c
      } with [ End_of_file -> Void ] ]
  | _ -> failwith "peek-char: not a port" ];

value peek_char () =
  peek_char_from_port (In current_in.val);

value is_eof_object obj =
  match obj with
  [ Void -> t
  | _ -> f ];

(* value is_char_ready_on_port port =
  match port with
  [ In port ->
    match port.peek with
    [ None -> do {
        try 
      }
    | Some _ -> t ]
  | _ -> failwith "char-ready?: not a port" ];

value is_char_ready () =
  is_char_ready_on_port current_in.val;*)
