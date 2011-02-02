type t = (* scheme intermediate code *)
  | Quote of Scheme.t
  | Do of list (var * t * t) and (t * t) and t
  | Begin of list t
  | Cond of list (t * t) and t
  | Delay of t
  | Let of list (var * t) and t
  | LetRec of list (var * t) and t
  | LetStar of list (var * t) and t
  | Set of var and t
  | Lambda of bool and list var and t
  | If of t and t and t
  | And of t and t
  | Or of t and t
  | Case of t and list (Scheme.t * t) and t
  | Application of t and list t
  | Reference of var
  | Prim of prim

type prim = {
  name : string;
  arity : int;
  varargs : bool;
}

type var = {
  name : string;
  id : string;
  mutated : mutable bool;
  kind : mutable var_kind
}

and var_kind =
    Local
  | Global
  | Closure
  | Parameter
