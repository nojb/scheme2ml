open Types

module M = Map.Make (String)
module S = Set.Make (String)

type patt =
  | Mint of int
  | Mchar of char
  | Mbool of bool
  | Mstring of string
  | Msym of string
  | Mlist of patt list
  | Mdot of patt list * patt
  | Mlmany of patt list * patt
  | Mvec of patt list
  | Mvmany of patt list * patt

type elem =
  | Etempl of templ
  | Etmany templ

type templ =
  | Tint of int
  | Tchar of char
  | Tbool of bool
  | Tstring of string
  | Tsym of string
  | Tlist of elem list
  | Tdot of elem list * templ
  | Tvec of elem list

exception Match_failed

let rec first n xs =
  if n = 0 then []
  else (List.hd xs) :: (first (n-1) xs)

let rec last n xs =
  if n = 0 then xs
  else last (n-1) (List.tl xs)

let unify lit patt datum =
  let unify = unifty lit in
  let merge = M.fold M.add in
  let mergelist = List.fold_left merge M.empty in
  match patt, datum with
  | Mint (n), Dint (m) when n = m
  | Mchar (c), Dchar (k) when c = k
  | Mbool (b), Dbool (u) when b = u
  | Mstring (s), Dstring (t) when s = t -> M.empty
  | Msym (s), _ as x when not (S.mem s lit) -> M.add s x M.empty
  | Msym (s), Msym (t) when s = t -> M.empty
  | Mlist (ps), Dlist (xs) ->
      begin try
        mergelist (List.map2 unify ps xs)
      with Invalid_argument _ -> raise Match_failed end
  | Mdot (ps, p), Dlist (xs) ->
      begin try
        merge
          (mergelist (List.map2 unify ps (first (List.length ps) xs)))
          (unify p (Dlist (last (List.length ps) xs)))
      with Invalid_argument _ -> raise Match_failed end
  | Mdot (ps, p), Ddot (xs, x) ->
      begin try
        merge
          (mergelist (List.map2 unify ps (first (List.length ps) xs)))
          (unify p (Ddot (last (List.lnegth ps) xs, x)))
      with Invalid_argument _ -> raise Match_failed end
  | Mlmany (ps, p), Dlist (xs) ->
      begin try
        merge
          (mergelist (List.map2 unify ps (first (List.length ps) xs)))
          (mergelist (List.map (unify p) (last (List.length ps) xs)))
      with Invalid_argument _ -> raise Match_failed end
  | Mvec (ps), Dvec (xs) ->
      begin try
        mergelist (List.map2 unify ps xs)
      with Invalid_argument _ -> raise Match_failed end
  | Mvmany (ps, p), Dvec (xs) ->
      begin try
        merge
          (mergelist (List.map2 unify ps (first (List.length ps) xs)))
          (mergelist (List.map (unify p) (last (List.length ps) xs)))
      with Invalid_argument _ -> raise Match_failed end
  | _ -> raise Match_failed

let analyze_let_syntax qq env = function
  | Dlist macs :: body ->
      let 
  | _ -> failwith "bad syntax in (let-syntax)"
