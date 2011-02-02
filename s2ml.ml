let compile inch outch =
  Emit.pp (Format.formatter_of_out_channel outch)
    (Ast.analyze_program
      (Parser.program Lexer.token
        (Lexing.from_channel inch)))

let () =
  compile stdin stdout
