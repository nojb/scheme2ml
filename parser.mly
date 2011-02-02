%{
  open Datum
%}

%token LP RP EOF DOT QUOTE
%token TRUE FALSE SHARP_LP
%token QUASIQUOTE UNQUOTE UNQUOTE_SPLICING
%token <int> INT
%token <string> NAME
%token <char> CHAR
%token <string> STRING

%type <Datum.datum list> program
%type <Datum.datum> ast
%start ast
%start program

%%

program:
  lst = list(ast) EOF
  { lst }
  ;

ast:
  NAME
  { Dsym (String.lowercase $1) }
  | TRUE
  { Dbool true }
  | FALSE
  { Dbool false }
  | CHAR
  { Dchar $1 }
  | STRING
  { Dstring $1 }
  | INT
  { Dint $1 }
  | QUOTE ast
  { Dlist [Dsym "quote"; $2] }
  | QUASIQUOTE ast
  { Dlist [Dsym "quasiquote"; $2] }
  | UNQUOTE ast
  { Dlist [Dsym "unquote"; $2] }
  | UNQUOTE_SPLICING ast
  { Dlist [Dsym "unquote-splicing"; $2] }
  | SHARP_LP lst = list(ast) RP
  { Dvec lst }
  | LP xs = list(ast) RP
  { Dlist xs }
  | LP xs = list(ast) DOT x = ast RP
  { Ddot (xs, x) }
  ;
