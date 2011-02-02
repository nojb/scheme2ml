%{
%}

%token LP RP EOF DOT QUOTE
%token TRUE FALSE SHARP_LP
%token QUASIQUOTE UNQUOTE UNQUOTE_SPLICING
%token <int> INT
%token <string> NAME
%token <char> CHAR
%token <string> STRING

%type <Scheme.t list> program
%type <Scheme.t> ast
%start ast
%start program

%%

program:
  lst = list(ast) EOF
  {
    lst
  }
  ;

ast:
  NAME
  {
    Scheme.Symbol (String.lowercase $1)
  }
  | TRUE
  {
    Scheme.Strue
  }
  | FALSE
  {
    Scheme.Sfalse
  }
  | CHAR
  {
    Scheme.Char $1
  }
  | STRING
  {
    Scheme.String $1
  }
  | INT
  {
    Scheme.Snum (Num.Int $1)
  }
  | QUOTE ast
  {
    Scheme.Scons {
      Scheme.car = Scheme.Symbol "quote";
      Scheme.cdr = Scheme.Scons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Snil
      }
    }
  }
  | QUASIQUOTE ast
  {
    Scheme.Scons {
      Scheme.car = Scheme.Symbol "quasiquote";
      Scheme.cdr = Scheme.Scons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Snil
      }
    }
  }
  | UNQUOTE ast
  {
    Scheme.Scons {
      Scheme.car = Scheme.Symbol "unquote";
      Scheme.cdr = Scheme.Scons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Snil
      }
    }
  }
  | UNQUOTE_SPLICING ast
  {
    Scheme.Scons {
      Scheme.car = Scheme.Symbol "unquote-splicing";
      Scheme.cdr = Scheme.Scons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Snil
      }
    }
  }
  | SHARP_LP lst = list(ast) RP
  {
    Scheme.Vector (Array.of_list lst)
  }
  | LP cons RP
  {
    $2
  }
  ;

cons:
  (* nothing *)
  {
    Scheme.Snil
  }
  | ast cons
  {
    Scheme.Scons { Scheme.car = $1; Scheme.cdr = $2 }
  }
  | DOT ast
  {
    $2
  }
  ;
