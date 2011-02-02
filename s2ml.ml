let compile inch outch =
  Emit.pp outch
    (Ast.analyze_program
      (Parser.program Lexer.token
        (Lexing.from_channel inch)))

let () =
  compile stdin stdout
