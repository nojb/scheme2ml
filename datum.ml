type datum =
  | Dint of int
  | Dbool of bool
  | Dchar of char
  | Dstring of string
  | Dlist of datum list
  | Ddot of datum list * datum
  | Dsym of string
  | Dvec of datum list

open Printf

let rec pp_sep sep pp ppf = function
  | [] -> ()
  | [x] -> pp ppf x
  | x :: xs -> fprintf ppf "%a%s%a" pp x sep (pp_sep sep pp) xs

let rec pp_datum ppf = function
  | Dint n -> fprintf ppf "%d" n
  | Dbool true -> fprintf ppf "#t"
  | Dbool false -> fprintf ppf "#f"
  | Dchar c -> fprintf ppf "%C" c
  | Dstring s -> fprintf ppf "%S" s
  | Dlist xs -> fprintf ppf "(%a)" (pp_sep " " pp_datum) xs
  | Ddot (xs, x) -> fprintf ppf "(%a . %a)" (pp_sep " " pp_datum) xs pp_datum x
  | Dsym s -> fprintf ppf "%s" s
  | Dvec xs -> fprintf ppf "#(%a)" (pp_sep " " pp_datum) xs
