{
  open Parser

  let stringbuf = Buffer.create 10
}

let initial = ['a'-'z''A'-'Z''!''$''%''&''*''/'':''<''=''>''?''^''_''~']
let identifier = (initial (initial | ['0'-'9'] | ['+''-''.''@'])*) | '+' | '-' | "..."

rule token = parse
  '-'?['0'-'9']+ as int
  {
    INT (int_of_string int)
  }
  | ';' [^'\n''\r']*['\n''\r']
  {
    token lexbuf
  }
  | "#t" | "#T"
  {
    TRUE
  }
  | "#f" | "#F"
  {
    FALSE
  }
  | "#\\" ['s''S']['p''P']['a''A']['c''C']['e''E']
  {
    CHAR ' '
  }
  | "#\\" ['n''N']['e''E']['w''W']['l''L']['i''I']['n''N']['e''E']
  {
    CHAR '\n'
  }
  | "#\\" (_ as c)
  {
    CHAR c
  }
  | "#("
  {
    SHARP_LP
  }
  | '''
  {
    QUOTE
  }
  | '`'
  {
    QUASIQUOTE
  }
  | ",@"
  {
    UNQUOTE_SPLICING
  }
  | ','
  {
    UNQUOTE
  }
  | '.'
  {
    DOT
  }
  | identifier as name
  {
    NAME name
  }
  | '('
  {
    LP
  }
  | ')'
  {
    RP
  }
  | [' ' '\t' '\n' '\r']+
  {
    token lexbuf
  }
  | '"'
  {
    Buffer.clear stringbuf;
    string lexbuf
  }
  | eof
  {
    EOF
  }

and string = parse
  '"'
  {
    STRING (Buffer.contents stringbuf)
  }
  | "\\\\"
  {
    Buffer.add_char stringbuf '\\';
    string lexbuf
  }
  | "\\\""
  {
    Buffer.add_char stringbuf '"';
    string lexbuf
  }
  | _ as c
  {
    Buffer.add_char stringbuf c;
    string lexbuf
  }
  | eof
  {
    (* should warn that eof was found in
      the middle of a string *)
    STRING (Buffer.contents stringbuf)
  }
