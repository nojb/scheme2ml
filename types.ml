
type datum =
  | Dint of int
  | Dbool of bool
  | Dchar of char
  | Dstring of string
  | Dlist of datum list
  | Ddot of datum list * datum
  | Dsym of string
  | Dvec of datum list
  | Dunspec

type pexp =
  | Pquote of datum
  | Pvar of string
  | Passign of string * pexp
  | Papp of pexp * pexp list
  | Pif of pexp * pexp * pexp
  | Plambda of string list * pexp
  | PlambdaVar of string list * string * pexp
  | Plet of (string * pexp) list * pexp
  | Pbegin of pexp list

