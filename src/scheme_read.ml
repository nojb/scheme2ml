value read () =
  let lexbuf = Lexing.from_channel stdin in
  Parser.ast Lexer.token lexbuf;
