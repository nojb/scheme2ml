let main () =
  let lexbuf = Lexing.from_channel stdin in
  let prg = Parser.program Lexer.token lexbuf in
  (*let env = Builtins.populate Ast.M.empty in do {*)
  Emit.emit (Ast.analyze_program prg);
  Printf.printf ";%!\n"

let _ = main ()
