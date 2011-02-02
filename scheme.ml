type in_port = { ch : in_channel; mutable peek : char option }

type out_port = out_channel

open Num

type t =
    Snum of num
  | Symbol of string
  | Strue
  | Sfalse
  | Char of char
  | Vector of t array
  | String of string
  | Scons of cons
  | Lambda of (t -> t)
  | Lambda0 of (unit -> t)
  | Lambda1 of (t -> t)
  | Lambda2 of (t -> t -> t)
  | Lambda3 of (t -> t -> t -> t)
  | Lambda4 of (t -> t -> t -> t -> t)
  | Promise of t Lazy.t
  | Void
  | In of in_port
  | Out of out_port
  | Snil

and cons = { mutable car : t; mutable cdr : t }

module W =
  Weak.Make
    (struct
       type t2 = t
       type t = t2
       let equal x y =
         match x, y with
           Symbol s, Symbol t -> String.compare s t = 0
         | _ -> false
       let hash = Hashtbl.hash
     end)

let symbols = W.create 10

(* be careful --- this definition (interning
 * the string, instead of the Symbol ..., means
 * that when we want to eq? two symbols we have to
 * pointer-compare the string!, not the symbol. cf.
 * the definition of eqp below *)

let intern s = W.merge symbols (Symbol s)

let is_procedure obj =
  match obj with
  | Lambda _ | Lambda0 _ | Lambda1 _
  | Lambda2 _ | Lambda3 _ | Lambda4 _ -> Strue
  | _ -> Sfalse

let is_eq a b =
  if a == b then Strue else Sfalse

  (* my implementation of eqv? compares strings char by char *)
let is_eqv a b =
  if a == b then Strue
  else
    match a, b with
      Char a, Char b -> if a = b then Strue else Sfalse
    | Vector a, Vector b -> if a == b then Strue else Sfalse
    | String a, String b -> if a = b then Strue else Sfalse
    | Snum a, Snum b -> if a =/ b then Strue else Sfalse
    | _ -> Sfalse

let is_equal a b =
  if a == b then Strue
  else
    let rec is_equal_aux a b =
      match a, b with
        Char a, Char b -> a = b
      | Scons a, Scons b -> is_equal_aux a.car b.car && is_equal_aux a.cdr b.cdr
      | Vector a, Vector b ->
          let la = Array.length a in
          let lb = Array.length b in
          if la <> lb then false
          else
            let rec loop i =
              if i >= la then true
              else if is_equal_aux a.(i) b.(i) then loop (i + 1)
              else false
            in
            loop 0
      | String a, String b -> a = b
      | Snum a, Snum b -> a =/ b
      | _ -> false
    in
    if is_equal_aux a b then Strue else Sfalse

let rec splice lst z =
  match lst with
    Scons {car = a; cdr = b} -> Scons {car = a; cdr = splice b z}
  | Snil -> z
  | _ -> failwith "splice: not a list"

let rec fold_left f start cons =
  match cons with
    Scons cons -> fold_left f (f start cons.car) cons.cdr
  | Snil -> start
  | _ -> failwith "fold-left: not a list"

let add2 obj1 obj2 =
  match obj1 with
    Int n ->
      begin match obj2 with
        Int m -> Int (n + m)
      | _ -> failwith "+: bad arguments"
      end
  | _ -> failwith "+: bad arguments"

let add args =
  Snum
    (fold_left
       (fun start next ->
          match next with
            Snum (n) -> start +/ n
          | _ -> failwith "+: bad arguments")
       (num_of_int 0) args)

let mul2 obj1 obj2 =
  match obj1 with
  | Snum n ->
      begin match obj2 with
        Snum m -> Snum (n */ m)
      | _ -> failwith "*: bad arguments"
      end
  | _ -> failwith "*: bad arguments"

let mul args =
  Snum
    (fold_left
       (fun start next ->
          match next with
          | Snum n -> start */ n
          | _ -> failwith "*: bad arguments")
       (num_of_int 1) args)

let sub2 obj1 obj2 =
  match obj1 with
  | Snum n ->
      begin match obj2 with
      | Snum m -> Snum (n -/ m)
      | _ -> failwith "-: bad arguments"
      end
  | _ -> failwith "-: bad arguments"

let sub args =
  match args with
  | Scons {car = Snum n; cdr = Snil} -> Snum (minus_num n)
  | Scons {car = Snum n; cdr = rest} ->
      Snum
        (fold_left
           (fun start next ->
              match next with
              | Snum n -> start -/ n
              | _ -> failwith "-: bad arguments")
           n rest)
  | Snil -> Snum (num_of_int 0)
  | _ -> failwith "-: bad arguments"

let remainder n1 n2 =
  match n1, n2 with
  | Snum n1, Snum n2 -> Snum (mod_num n1 n2)
  | _ -> failwith "remainder: not a pair of ints"

let cmp_nums name cmp z1 z2 rest =
  match z1, z2 with
  | Snum z1, Snum z2 ->
      let rec loop last rest =
        match rest with
        | Snil -> Strue
        | Scons {car = Snum a; cdr = rest} ->
            if cmp last a then loop a rest else Sfalse
        | _ -> failwith (name ^ ": not numbers")
      in
      if cmp z1 z2 then loop z2 rest else Sfalse
  | _ -> failwith (name ^ ": not numbers")

let lt z1 z2 rest = cmp_nums "<" (</) z1 z2 rest

let gt z1 z2 rest = cmp_nums ">" (>/) z1 z2 rest

let le z1 z2 rest = cmp_nums "<=" (<=/) z1 z2 rest

let ge z1 z2 rest = cmp_nums ">=" (>=/) z1 z2 rest

let eq z1 z2 rest = cmp_nums "=" (=/) z1 z2 rest

let rec to_string =
  function
  | Snum n -> string_of_num n
  | Symbol s -> s
  | Strue -> "#t"
  | Sfalse -> "#f"
  | Char c -> String.make 1 c
  | String s -> s
  | Vector vector ->
      let len = Array.length vector in
      let rec loop i =
        if i >= len then ")"
        else if i = len - 1 then to_string vector.(i) ^ ")"
        else to_string vector.(i) ^ " " ^ loop (i + 1)
      in
      "#(" ^ loop 0
  | In _ -> "#<input-port>"
  | Out _ -> "#<output-port>"
  | Scons cons ->
      let rec loop cons =
        match cons.cdr with
        | Snil -> to_string cons.car
        | Scons cons' -> to_string cons.car ^ " " ^ loop cons'
        | a -> to_string cons.car ^ " . " ^ to_string a
      in
      "(" ^ loop cons ^ ")"
  | Snil -> "()"
  | Void -> ""
  | Promise _ -> "#<promise>"
  | Lambda _ | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      "#<closure>"

let display x = let _ = print_string (to_string x) in Void

let apply f args =
  match f with
  | Lambda f -> f args
  | Lambda0 f ->
      begin match args with
        Snil -> f ()
      | _ -> failwith "apply: arity error"
      end
  | Lambda1 f ->
      begin match args with
        Scons {car = arg1; cdr = Snil} -> f arg1
      | _ -> failwith "apply: arity error"
      end
  | Lambda2 f ->
      begin match args with
        Scons {car = arg1; cdr = Scons {car = arg2; cdr = Snil}} -> f arg1 arg2
      | _ -> failwith "apply: arity error"
      end
  | Lambda3 f ->
      begin match args with
        Scons
          {car = a1;
           cdr = Scons {car = a2; cdr = Scons {car = a3; cdr = Snil}}} ->
          f a1 a2 a3
      | _ -> failwith "apply: arity error"
      end
  | Lambda4 f ->
      begin match args with
        Scons
          {car = a1;
           cdr =
             Scons
               {car = a2;
                cdr = Scons {car = a3; cdr = Scons {car = a4; cdr = Snil}}}} ->
          f a1 a2 a3 a4
      | _ -> failwith "apply: arity error"
      end
  | _ -> failwith "apply: not a function"

let apply0 f =
  match f with
    Lambda f -> f Snil
  | Lambda0 f -> f ()
  | Lambda1 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply1 f a =
  match f with
    Lambda f -> f (Scons {car = a; cdr = Snil})
  | Lambda1 f -> f a
  | Lambda0 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply2 f a b =
  match f with
    Lambda f -> f (Scons {car = a; cdr = Scons {car = b; cdr = Snil}})
  | Lambda2 f -> f a b
  | Lambda0 _ | Lambda1 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply3 f a b c =
  match f with
    Lambda f ->
      f
        (Scons
           {car = a; cdr = Scons {car = b; cdr = Scons {car = c; cdr = Snil}}})
  | Lambda3 f -> f a b c
  | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply4 f a b c d =
  match f with
    Lambda f ->
      f
        (Scons
           {car = a;
            cdr =
              Scons
                {car = b;
                 cdr = Scons {car = c; cdr = Scons {car = d; cdr = Snil}}}})
  | Lambda4 f -> f a b c d
  | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda3 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let is_true x =
  x == Strue

let is_zero number =
  match number with
  | Snum n -> if n =/ (num_of_int 0) then Strue else Sfalse
  | _ -> failwith "zero?: wrong argument type"

let is_integer obj =
  match obj with
  | Snum (Int _)
  | Snum (Big_int _) -> Strue
  | _ -> Sfalse

let is_number obj =
  match obj with
  | Snum _ -> Strue
  | _ -> Sfalse

let car =
  function
  | Scons cons -> cons.car
  | _ -> failwith "car: not a pair"

let cdr =
  function
  | Scons cons -> cons.cdr
  | _ -> failwith "cdr: not a pair"

let cadr =
  function
    Scons {car = _; cdr = Scons {car = a; cdr = _}} -> a
  | _ -> failwith "cadr: bad args"

let cddr =
  function
    Scons {car = _; cdr = Scons {car = _; cdr = a}} -> a
  | _ -> failwith "cddr: bad args"

let cdar =
  function
    Scons {car = Scons {car = _; cdr = a}; cdr = _} -> a
  | _ -> failwith "cdar: bad args"

let caar =
  function
    Scons {car = Scons {car = a; cdr = _}; cdr = _} -> a
  | _ -> failwith "caar: bad args"

let caaar =
  function
    Scons {car = Scons {car = Scons {car = a; cdr = _}; cdr = _}; cdr = _} -> a
  | _ -> failwith "caaar: bad args"

let caddr =
  function
    Scons {car = _; cdr = Scons {car = _; cdr = Scons {car = a; cdr = _}}} -> a
  | _ -> failwith "caddr: bad args"

let caadr =
  function
    Scons {car = _; cdr = Scons {car = Scons {car = a; cdr = _}; cdr = _}} -> a
  | _ -> failwith "caadr: bad args"

let cdddr =
  function
    Scons {car = _; cdr = Scons {car = _; cdr = Scons {car = _; cdr = a}}} -> a
  | _ -> failwith "cdddr: bad args"

let cdadr =
  function
    Scons {car = _; cdr = Scons {car = Scons {car = _; cdr = a}; cdr = _}} -> a
  | _ -> failwith "cdadr: bad args"

let cadddr =
  function
    Scons
      {car = _;
       cdr =
         Scons
           {car = _; cdr = Scons {car = _; cdr = Scons {car = a; cdr = _}}}} ->
      a
  | _ -> failwith "cadddr: bad args"

let number_to_string =
  function
  |  Snum n -> String (string_of_num n)
  | _ -> failwith "number->string: not a number"

let is_boolean =
  function
  | Strue | Sfalse -> Strue
  | _ -> Sfalse

let _not obj =
  if obj == Strue then Sfalse else Strue

let is_pair =
  function
  | Scons _ -> Strue
  | _ -> Sfalse

let cons x y =
  Scons {car = x; cdr = y}

(*value set_car_bang pair obj =
  match pair with
  [ Scons cons -> do { cons.car := obj; Void }
  | _ -> failwith "set-car!: not a pair" ];

value set_cdr_bang pair obj =
  match pair with
  [ Scons cons -> do { cons.cdr := obj; Void }
  | _ -> failwith "set-cdr!: not a pair" ];*)

let is_null =
  function
  | Snil -> Strue
  | _ -> Sfalse

let rec map f lists =
  let rec join1 at_nil lists =
    match lists with
      Snil -> Snil, Snil
    | Scons {car = Scons {car = a; cdr = b}; cdr = b'} ->
        if at_nil < 0 then failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          Scons {car = a; cdr = heads}, Scons {car = b; cdr = tails}
    | Scons {car = Snil; cdr = z} ->
        if at_nil > 0 then failwith "map: lists not of the same length"
        else join1 (-1) z
    | _ -> failwith "map: not a list of lists"
  in
  match join1 0 lists with
    Snil, Snil -> Snil
  | heads, tails -> Scons {car = apply f heads; cdr = map f tails}

let rec for_each f lists =
  let rec join1 at_nil lists =
    match lists with
      Snil -> Snil, Snil
    | Scons {car = Scons {car = a; cdr = b}; cdr = b'} ->
        if at_nil < 0 then failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          Scons {car = a; cdr = heads}, Scons {car = b; cdr = tails}
    | Scons {car = Snil; cdr = z} ->
        if at_nil > 0 then failwith "map: lists not of the same length"
        else join1 (-1) z
    | _ -> failwith "map: not a list of lists"
  in
  match join1 0 lists with
    Snil, Snil -> Void
  | heads, tails -> ignore (apply f heads); for_each f tails

let rec is_list =
  function
  | Scons cons -> is_list cons.cdr
  | Snil -> Strue
  | _ -> Sfalse

let list args = args

let length list =
  let rec loop i list =
    match list with
    | Snil -> i
    | Scons cons -> loop (i + 1) cons.cdr
    | _ -> failwith "length: not a list"
  in
  Snum (Int (loop 0 list))

let rec append lists =
  match lists with
  | Scons {car = first_list; cdr = Snil} -> first_list
  | Scons {car = first_list; cdr = rest} ->
      let rec loop =
        function
          Scons cons -> Scons {car = cons.car; cdr = loop cons.cdr}
        | Snil -> append rest
        | _ -> failwith "append: malformed arguments"
      in
      loop first_list
  | Snil -> Snil
  | _ -> failwith "append: not a list of lists"

let rec append2 list1 list2 =
  match list1 with
  | Snil -> list2
  | Scons {car = a; cdr = b} -> Scons {car = a; cdr = append2 b list2}
  | _ -> failwith "append: not a list"

let reverse list =
  let rec loop list reversed =
    match list with
    | Snil -> reversed
    | Scons cons -> loop cons.cdr (Scons {car = cons.car; cdr = reversed})
    | _ -> failwith "reverse: not a list"
  in
  loop list Snil

let list_tail list k =
  match k with
    Int k ->
      let rec loop list k =
        if k = 0 then list
        else
          match list with
            Scons cons -> loop cons.cdr (k - 1)
          | Snil -> failwith "list-tail: list too short"
          | _ -> failwith "list-tail: not a list"
      in
      loop list k
  | _ -> failwith "list-tail: not an int"

let list_ref list k =
  match k with
    Int k ->
      let rec loop list k =
        match list with
          Scons cons -> if k = 0 then cons.car else loop cons.cdr (k - 1)
        | Snil -> failwith "list-ref: list too short"
        | _ -> failwith "list-ref: not a list"
      in
      loop list k
  | _ -> failwith "list-ref: not an int"

let rec mem name cmp obj list =
  match list with
  | Scons cons ->
      if (cmp obj cons.car) == Strue then list else mem name cmp obj cons.cdr
  | Snil -> Sfalse
  | _ -> failwith (name ^ ": not a list")

let memq = mem "memq" is_eq

let memv = mem "memv" is_eqv

let member = mem "member" is_equal

let rec ass name cmp obj alist =
  match alist with
  | Scons {car = Scons cons as z; cdr = rest} ->
      if (cmp obj cons.car) == Strue then z else ass name cmp obj rest
  | Snil -> Sfalse
  | _ -> failwith (name ^ ": not an alist")

let assq = ass "assq" is_eq

let assv = ass "assv" is_eqv

let assoc = ass "assoc" is_equal

let is_symbol =
  function
  | Symbol _ -> Strue
  | _ -> Sfalse

let symbol_to_string symbol =
  match symbol with
    Symbol symbol -> String (String.copy symbol)
  | _ -> failwith "symbol->string: not a symbol"

let string_to_symbol string =
  match string with
    String string -> intern (String.copy string)
  | _ -> failwith "string->symbol: not a string"

let is_vector =
  function
    Vector _ -> Strue
  | _ -> Sfalse

let vector objs =
  let rec loop len =
    function
      Scons {car = obj; cdr = rest} ->
        let arr = loop (len + 1) rest in arr.(len) <- obj; arr
    | Snil -> Array.make len Void
    | _ -> failwith "vector: bad arglist"
  in
  Vector (loop 0 objs)

let make_vector size =
  match size with
    Int n -> Vector (Array.make n Void)
  | _ -> failwith "make-vector: not an integer"

let vector_length vector =
  match vector with
    Vector vector -> Int (Array.length vector)
  | _ -> failwith "vector-length: not a vector"

let vector_ref vector k =
  match vector with
    Vector vector ->
      begin match k with
        Int n -> vector.(n)
      | _ -> failwith "vector-ref: bad index"
      end
  | _ -> failwith "vector-ref: not a vector"

let vector_set vector k obj =
  match vector with
    Vector vector ->
      begin match k with
        Int n -> vector.(n) <- obj; Void
      | _ -> failwith "vector-set!: bad index"
      end
  | _ -> failwith "vector-set!: not a vector"

let vector_to_list vector =
  match vector with
    Vector vector ->
      let l = Array.length vector in
      let rec loop i cdr =
        if i < 0 then cdr
        else loop (i - 1) (Scons {car = vector.(i); cdr = cdr})
      in
      loop (l - 1) Snil
  | _ -> failwith "vector->list: not a vector"

let list_to_vector list =
  let rec loop l list =
    match list with
      Snil -> Array.create l Snil
    | Scons {car = a; cdr = b} -> let arr = loop (l + 1) b in arr.(l) <- a; arr
    | _ -> failwith "list->vector: not a list"
  in
  Vector (loop 0 list)

let vector_fill vector fill =
  match vector with
    Vector vector -> Array.fill vector 0 (Array.length vector) fill; Void
  | _ -> failwith "vector-fill!: not a vector"

let is_char obj =
  match obj with
  | Char _ -> Strue
  | _ -> Sfalse

let is_char_eq char1 char2 =
  match char1, char2 with
  | Char char1, Char char2 ->
      if char1 = char2 then Strue else Sfalse
  | _ ->
      failwith "char=?: bad arguments"

let is_char_alphabetic char =
  match char with
  | Char c -> if 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' then Strue else Sfalse
  | _ -> failwith "char-alphabetic?: not a char"

let is_char_numeric char =
  match char with
  | Char c -> if '0' <= c && c <= '9' then Strue else Sfalse
  | _ -> failwith "char-numeric?: not a char"

let is_char_whitespace char =
  match char with
  | Char c -> if c = ' ' || c = '\t' || c = '\n' || c = '\r' then Strue else Sfalse
  | _ -> failwith "char-whitespace?: not a char"

let is_char_upper_case = function
  | Char c -> if c <= 'Z' && 'A' <= c then Strue else Sfalse
  | _ -> failwith "char-upper-case?: not a char"

let is_char_lower_case = function
  | Char c -> if 'a' <= c && c <= 'z' then Strue else Sfalse
  | _ -> failwith "char-lower-case?: not a char"

let char_to_integer = function
  | Char char -> Snum (Int (int_of_char char))
  | _ -> failwith "char->integer: not a char"

let integer_to_char = function
  | Snum (Int n) -> Char (char_of_int n)
  | _ -> failwith "integer->char: not an integer"

let is_string = function
  | String _ -> Strue
  | _ -> Sfalse

let string_length = function
  | String string -> Snum (Int (String.length string))
  | _ -> failwith "string-length: not a string"

let string_ref string k =
  match string with
  | String s ->
      begin match k with
      | Snum (Int n) -> Char s.[n]
      | _ -> failwith "string-ref: not an integer"
      end
  | _ -> failwith "string-ref: not a string"

let string_set string k char =
  match string with
  | String s ->
      begin match k with
      | Snum (Int n) ->
          begin match char with
            Char c -> s.[n] <- c; Void
          | _ -> failwith "string-set!: not a char"
          end
      | _ -> failwith "string-set!: not an integer"
      end
  | _ -> failwith "string-set!: not a string"

let substring string start finish =
  match string with
  | String string ->
      begin match start with
      | Snum (Int n) ->
          begin match finish with
          | Snum (Int m) -> String (String.sub string n (m - n + 1))
          | _ -> failwith "substring: end is not an integer"
          end
      | _ -> failwith "substring: start is not an integer"
      end
  | _ -> failwith "substring: string is not a string"

let string_append strings =
  let rec loop strings =
    match strings with
    | Snil -> ""
    | Scons {car = a; cdr = b} ->
        begin match a with
          String string -> string ^ loop b
        | _ -> failwith "string-append: not a list of strings"
        end
    | _ -> failwith "string-append: not a list of strings"
  in
  String (loop strings)

let string_to_list = function
  | String string ->
      let len = String.length string in
      let rec loop i =
        if i >= len then Snil
        else Scons {car = Char string.[i]; cdr = loop (i + 1)}
      in
      loop 0
  | _ -> failwith "string->list: not a string"

let list_to_string cons =
  let rec loop i cons =
    match cons with
    | Snil -> String.make i '\000'
    | Scons {car = Char c; cdr = cons'} ->
        let string = loop (i + 1) cons' in string.[i] <- c; string
    | _ -> failwith "list->string: not a list of chars"
  in
  String (loop 0 cons)

let string_copy = function
  | String string -> String (String.copy string)
  | _ -> failwith "string-copy: not a string"

let string_fill string char =
  match string with
  | String string ->
      begin match char with
        Char char -> String.fill string 0 (String.length string) char; Void
      | _ -> failwith "string-fill!: not a char"
      end
  | _ -> failwith "string-fill!: not a string"

let is_input_port = function
  | In _ -> Strue
  | _ -> Sfalse

let is_output_port = function
  | Out _ -> Strue
  | _ -> Sfalse

let std_in = {ch = stdin; peek = None}
let std_out = stdout

let current_in = ref std_in
let current_out = ref std_out

let current_input_port () = !current_in

let current_output_port () = !current_out

let with_input_from_file string thunk =
  match string with
    String string ->
      let old_in = !current_in in
      let ch = open_in string in
      current_in := {ch = ch; peek = None};
      let result = apply thunk Snil in
      close_in ch; current_in := old_in; result
  | _ -> failwith "with-input-from-file: not a string"

let open_input_file filename =
  match filename with
    String filename -> In {ch = open_in filename; peek = None}
  | _ -> failwith "open-input-file: not a string"

let open_output_file filename =
  match filename with
    String filename -> Out (open_out filename)
  | _ -> failwith "open-output-file: not a string"

let close_input_port port =
  match port with
    In port -> close_in port.ch; Void
  | _ -> failwith "close-input-port: not a port"

let close_output_port port =
  match port with
    Out ch -> close_out ch; Void
  | _ -> failwith "close-output-port: not a port"

let newline () = output_char !current_out '\n'; flush !current_out; Void

let newline_to_port port =
  match port with
    Out port -> output_char port '\n'; flush port; Void
  | _ -> failwith "newline: not a port"

let write_char char =
  match char with
    Char char -> output_char !current_out char; Void
  | _ -> failwith "write-char: not a char"

let write_char_to_port char port =
  match char with
    Char char ->
      begin match port with
        Out port -> output_char port char; Void
      | _ -> failwith "write-char: not a port"
      end
  | _ -> failwith "write-char: not a char"

let error msg objs =
  failwith ("error: " ^ to_string msg ^ ": " ^ to_string objs)

let force obj =
  match obj with
    Promise obj -> Lazy.force obj
  | _ -> failwith "force: not a promise"
