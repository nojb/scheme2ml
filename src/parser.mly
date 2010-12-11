%{
%}

%token LP RP EOF DOT QUOTE
%token TRUE FALSE SHARP_LP
%token QUASIQUOTE UNQUOTE UNQUOTE_SPLICING
%token <Num.num> INT
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
    Scheme.Symbol $1
  }
  | TRUE
  {
    Scheme.Boolean true
  }
  | FALSE
  {
    Scheme.Boolean false
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
    Scheme.Num $1
  }
  | QUOTE ast
  {
    Scheme.Cons {
      Scheme.car = Scheme.Symbol "quote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Nil
      }
    }
  }
  | QUASIQUOTE ast
  {
    Scheme.Cons {
      Scheme.car = Scheme.Symbol "quasiquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Nil
      }
    }
  }
  | UNQUOTE ast
  {
    Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Nil
      }
    }
  }
  | UNQUOTE_SPLICING ast
  {
    Scheme.Cons {
      Scheme.car = Scheme.Symbol "unquote-splicing";
      Scheme.cdr = Scheme.Cons {
        Scheme.car = $2;
        Scheme.cdr = Scheme.Nil
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
    Scheme.Nil
  }
  | ast cons
  {
    Scheme.Cons { Scheme.car = $1; Scheme.cdr = $2 }
  }
  | DOT ast
  {
    $2
  }
  ;
