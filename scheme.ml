type in_port = { ch : in_channel; mutable peek : char option }

type out_port = out_channel

type t =
    Int of int
  | Symbol of string
  | Boolean of bool
  | Char of char
  | Vector of t array
  | String of string
  | Cons of cons
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
  | Nil
and cons = { car : t; cdr : t }

let t = Boolean true
let f = Boolean false

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
    Lambda _ | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ -> t
  | _ -> f

let is_eq a b = if a == b then t else f

  (* my implementation of eqv? compares strings char by char *)
let is_eqv a b =
  if a == b then t
  else
    match a, b with
      Char a, Char b -> if a = b then t else f
    | Vector a, Vector b -> if a == b then t else f
    | String a, String b -> if a = b then t else f
    | Int a, Int b -> if a = b then t else f
    | _ -> f

let is_equal a b =
  if a == b then t
  else
    let rec is_equal_aux a b =
      match a, b with
        Char a, Char b -> a = b
      | Cons a, Cons b -> is_equal_aux a.car b.car && is_equal_aux a.cdr b.cdr
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
      | Int a, Int b -> a = b
      | _ -> false
    in
    if is_equal_aux a b then t else f

let rec splice lst z =
  match lst with
    Cons {car = a; cdr = b} -> Cons {car = a; cdr = splice b z}
  | Nil -> z
  | _ -> failwith "splice: not a list"

let rec fold_left f start cons =
  match cons with
    Cons cons -> fold_left f (f start cons.car) cons.cdr
  | Nil -> start
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
  Int
    (fold_left
       (fun start next ->
          match next with
            Int n -> start + n
          | _ -> failwith "+: bad arguments")
       0 args)

let mul2 obj1 obj2 =
  match obj1 with
    Int n ->
      begin match obj2 with
        Int m -> Int (n * m)
      | _ -> failwith "*: bad arguments"
      end
  | _ -> failwith "*: bad arguments"

let mul args =
  Int
    (fold_left
       (fun start next ->
          match next with
            Int n -> start * n
          | _ -> failwith "*: bad arguments")
       1 args)

let sub2 obj1 obj2 =
  match obj1 with
    Int n ->
      begin match obj2 with
        Int m -> Int (n - m)
      | _ -> failwith "-: bad arguments"
      end
  | _ -> failwith "-: bad arguments"

let sub args =
  match args with
    Cons {car = Int n; cdr = Nil} -> Int (-n)
  | Cons {car = Int n; cdr = rest} ->
      Int
        (fold_left
           (fun start next ->
              match next with
                Int n -> start - n
              | _ -> failwith "-: bad arguments")
           n rest)
  | Nil -> Int 0
  | _ -> failwith "-: bad arguments"

let remainder n1 n2 =
  match n1, n2 with
    Int n1, Int n2 -> Int (n1 mod n2)
  | _ -> failwith "remainder: not a pair of ints"

let cmp_nums name cmp z1 z2 rest =
  match z1, z2 with
    Int z1, Int z2 ->
      let rec loop last rest =
        match rest with
          Nil -> t
        | Cons {car = Int a; cdr = rest} ->
            if cmp last a then loop a rest else f
        | _ -> failwith (name ^ ": not numbers")
      in
      if cmp z1 z2 then loop z2 rest else f
  | _ -> failwith (name ^ ": not numbers")

let lt z1 z2 rest = cmp_nums "<" (fun a b -> a < b) z1 z2 rest

let gt z1 z2 rest = cmp_nums ">" (fun a b -> a > b) z1 z2 rest

let le z1 z2 rest = cmp_nums "<=" (fun a b -> a <= b) z1 z2 rest

let ge z1 z2 rest = cmp_nums ">=" (fun a b -> a >= b) z1 z2 rest

let eq z1 z2 rest = cmp_nums "=" (fun a b -> a == b) z1 z2 rest

let rec to_string =
  function
    Int n -> string_of_int n
  | Symbol s -> s
  | Boolean true -> "#t"
  | Boolean false -> "#f"
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
  | Cons cons ->
      let rec loop cons =
        match cons.cdr with
          Nil -> to_string cons.car
        | Cons cons' -> to_string cons.car ^ " " ^ loop cons'
        | a -> to_string cons.car ^ " . " ^ to_string a
      in
      "(" ^ loop cons ^ ")"
  | Nil -> "()"
  | Void -> ""
  | Promise _ -> "#<promise>"
  | Lambda _ | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      "#<closure>"

let display x = let _ = print_string (to_string x) in Void

let apply f args =
  match f with
    Lambda f -> f args
  | Lambda0 f ->
      begin match args with
        Nil -> f ()
      | _ -> failwith "apply: arity error"
      end
  | Lambda1 f ->
      begin match args with
        Cons {car = arg1; cdr = Nil} -> f arg1
      | _ -> failwith "apply: arity error"
      end
  | Lambda2 f ->
      begin match args with
        Cons {car = arg1; cdr = Cons {car = arg2; cdr = Nil}} -> f arg1 arg2
      | _ -> failwith "apply: arity error"
      end
  | Lambda3 f ->
      begin match args with
        Cons
          {car = a1;
           cdr = Cons {car = a2; cdr = Cons {car = a3; cdr = Nil}}} ->
          f a1 a2 a3
      | _ -> failwith "apply: arity error"
      end
  | Lambda4 f ->
      begin match args with
        Cons
          {car = a1;
           cdr =
             Cons
               {car = a2;
                cdr = Cons {car = a3; cdr = Cons {car = a4; cdr = Nil}}}} ->
          f a1 a2 a3 a4
      | _ -> failwith "apply: arity error"
      end
  | _ -> failwith "apply: not a function"

let apply0 f =
  match f with
    Lambda f -> f Nil
  | Lambda0 f -> f ()
  | Lambda1 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply1 f a =
  match f with
    Lambda f -> f (Cons {car = a; cdr = Nil})
  | Lambda1 f -> f a
  | Lambda0 _ | Lambda2 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply2 f a b =
  match f with
    Lambda f -> f (Cons {car = a; cdr = Cons {car = b; cdr = Nil}})
  | Lambda2 f -> f a b
  | Lambda0 _ | Lambda1 _ | Lambda3 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply3 f a b c =
  match f with
    Lambda f ->
      f
        (Cons
           {car = a; cdr = Cons {car = b; cdr = Cons {car = c; cdr = Nil}}})
  | Lambda3 f -> f a b c
  | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda4 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let apply4 f a b c d =
  match f with
    Lambda f ->
      f
        (Cons
           {car = a;
            cdr =
              Cons
                {car = b;
                 cdr = Cons {car = c; cdr = Cons {car = d; cdr = Nil}}}})
  | Lambda4 f -> f a b c d
  | Lambda0 _ | Lambda1 _ | Lambda2 _ | Lambda3 _ ->
      failwith "apply: arity error"
  | _ -> failwith "apply: not a function"

let is_true x = not (x == f)
  (* fun
  [ Boolean False -> False
  | _ -> True ]; *)

let is_zero number =
  match number with
    Int n -> if n = 0 then t else f
  | _ -> failwith "zero?: wrong argument type"

let is_integer obj =
  match obj with
    Int n -> t
  | _ -> f

let is_number obj =
  match obj with
    Int n -> t
  | _ -> f

let car =
  function
    Cons cons -> cons.car
  | _ -> failwith "car: not a pair"

let cdr =
  function
    Cons cons -> cons.cdr
  | _ -> failwith "cdr: not a pair"

let cadr =
  function
    Cons {car = _; cdr = Cons {car = a; cdr = _}} -> a
  | _ -> failwith "cadr: bad args"

let cddr =
  function
    Cons {car = _; cdr = Cons {car = _; cdr = a}} -> a
  | _ -> failwith "cddr: bad args"

let cdar =
  function
    Cons {car = Cons {car = _; cdr = a}; cdr = _} -> a
  | _ -> failwith "cdar: bad args"

let caar =
  function
    Cons {car = Cons {car = a; cdr = _}; cdr = _} -> a
  | _ -> failwith "caar: bad args"

let caaar =
  function
    Cons {car = Cons {car = Cons {car = a; cdr = _}; cdr = _}; cdr = _} -> a
  | _ -> failwith "caaar: bad args"

let caddr =
  function
    Cons {car = _; cdr = Cons {car = _; cdr = Cons {car = a; cdr = _}}} -> a
  | _ -> failwith "caddr: bad args"

let caadr =
  function
    Cons {car = _; cdr = Cons {car = Cons {car = a; cdr = _}; cdr = _}} -> a
  | _ -> failwith "caadr: bad args"

let cdddr =
  function
    Cons {car = _; cdr = Cons {car = _; cdr = Cons {car = _; cdr = a}}} -> a
  | _ -> failwith "cdddr: bad args"

let cdadr =
  function
    Cons {car = _; cdr = Cons {car = Cons {car = _; cdr = a}; cdr = _}} -> a
  | _ -> failwith "cdadr: bad args"

let cadddr =
  function
    Cons
      {car = _;
       cdr =
         Cons
           {car = _; cdr = Cons {car = _; cdr = Cons {car = a; cdr = _}}}} ->
      a
  | _ -> failwith "cadddr: bad args"

let number_to_string =
  function
    Int n -> String (string_of_int n)
  | _ -> failwith "number->string: not a number"

let is_boolean =
  function
    Boolean _ -> t
  | _ -> f

let _not obj = if is_true obj then f else t

let is_pair =
  function
    Cons _ -> t
  | _ -> f

let cons x y = Cons {car = x; cdr = y}

(*value set_car_bang pair obj =
  match pair with
  [ Cons cons -> do { cons.car := obj; Void }
  | _ -> failwith "set-car!: not a pair" ];

value set_cdr_bang pair obj =
  match pair with
  [ Cons cons -> do { cons.cdr := obj; Void }
  | _ -> failwith "set-cdr!: not a pair" ];*)

let is_null =
  function
    Nil -> t
  | _ -> f

let rec map f lists =
  let rec join1 at_nil lists =
    match lists with
      Nil -> Nil, Nil
    | Cons {car = Cons {car = a; cdr = b}; cdr = b'} ->
        if at_nil < 0 then failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          Cons {car = a; cdr = heads}, Cons {car = b; cdr = tails}
    | Cons {car = Nil; cdr = z} ->
        if at_nil > 0 then failwith "map: lists not of the same length"
        else join1 (-1) z
    | _ -> failwith "map: not a list of lists"
  in
  match join1 0 lists with
    Nil, Nil -> Nil
  | heads, tails -> Cons {car = apply f heads; cdr = map f tails}

let rec for_each f lists =
  let rec join1 at_nil lists =
    match lists with
      Nil -> Nil, Nil
    | Cons {car = Cons {car = a; cdr = b}; cdr = b'} ->
        if at_nil < 0 then failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          Cons {car = a; cdr = heads}, Cons {car = b; cdr = tails}
    | Cons {car = Nil; cdr = z} ->
        if at_nil > 0 then failwith "map: lists not of the same length"
        else join1 (-1) z
    | _ -> failwith "map: not a list of lists"
  in
  match join1 0 lists with
    Nil, Nil -> Void
  | heads, tails -> ignore (apply f heads); for_each f tails

let rec is_list =
  function
    Cons cons -> is_list cons.cdr
  | Nil -> t
  | _ -> f

let list args = args

let length list =
  let rec loop i list =
    match list with
      Nil -> i
    | Cons cons -> loop (i + 1) cons.cdr
    | _ -> failwith "length: not a list"
  in
  Int (loop 0 list)

let rec append lists =
  match lists with
    Cons {car = first_list; cdr = Nil} -> first_list
  | Cons {car = first_list; cdr = rest} ->
      let rec loop =
        function
          Cons cons -> Cons {car = cons.car; cdr = loop cons.cdr}
        | Nil -> append rest
        | _ -> failwith "append: malformed arguments"
      in
      loop first_list
  | Nil -> Nil
  | _ -> failwith "append: not a list of lists"

let rec append2 list1 list2 =
  match list1 with
    Nil -> list2
  | Cons {car = a; cdr = b} -> Cons {car = a; cdr = append2 b list2}
  | _ -> failwith "append: not a list"

let reverse list =
  let rec loop list reversed =
    match list with
      Nil -> reversed
    | Cons cons -> loop cons.cdr (Cons {car = cons.car; cdr = reversed})
    | _ -> failwith "reverse: not a list"
  in
  loop list Nil

let list_tail list k =
  match k with
    Int k ->
      let rec loop list k =
        if k = 0 then list
        else
          match list with
            Cons cons -> loop cons.cdr (k - 1)
          | Nil -> failwith "list-tail: list too short"
          | _ -> failwith "list-tail: not a list"
      in
      loop list k
  | _ -> failwith "list-tail: not an int"

let list_ref list k =
  match k with
    Int k ->
      let rec loop list k =
        match list with
          Cons cons -> if k = 0 then cons.car else loop cons.cdr (k - 1)
        | Nil -> failwith "list-ref: list too short"
        | _ -> failwith "list-ref: not a list"
      in
      loop list k
  | _ -> failwith "list-ref: not an int"

let rec mem name cmp obj list =
  match list with
    Cons cons ->
      if is_true (cmp obj cons.car) then list else mem name cmp obj cons.cdr
  | Nil -> f
  | _ -> failwith (name ^ ": not a list")

let memq = mem "memq" is_eq

let memv = mem "memv" is_eqv

let member = mem "member" is_equal

let rec ass name cmp obj alist =
  match alist with
    Cons {car = Cons cons as z; cdr = rest} ->
      if is_true (cmp obj cons.car) then z else ass name cmp obj rest
  | Nil -> f
  | _ -> failwith (name ^ ": not an alist")

let assq = ass "assq" is_eq

let assv = ass "assv" is_eqv

let assoc = ass "assoc" is_equal

let is_symbol =
  function
    Symbol _ -> t
  | _ -> f

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
    Vector _ -> t
  | _ -> f

let vector objs =
  let rec loop len =
    function
      Cons {car = obj; cdr = rest} ->
        let arr = loop (len + 1) rest in arr.(len) <- obj; arr
    | Nil -> Array.make len Void
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
        else loop (i - 1) (Cons {car = vector.(i); cdr = cdr})
      in
      loop (l - 1) Nil
  | _ -> failwith "vector->list: not a vector"

let list_to_vector list =
  let rec loop l list =
    match list with
      Nil -> Array.create l Nil
    | Cons {car = a; cdr = b} -> let arr = loop (l + 1) b in arr.(l) <- a; arr
    | _ -> failwith "list->vector: not a list"
  in
  Vector (loop 0 list)

let vector_fill vector fill =
  match vector with
    Vector vector -> Array.fill vector 0 (Array.length vector) fill; Void
  | _ -> failwith "vector-fill!: not a vector"

let is_char obj =
  match obj with
    Char _ -> t
  | _ -> f

let is_char_eq char1 char2 =
  match char1, char2 with
    Char char1, Char char2 -> if char1 = char2 then t else f
  | _ -> failwith "char=?: bad arguments"

let is_char_alphabetic char =
  match char with
    Char c -> if 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' then t else f
  | _ -> failwith "char-alphabetic?: not a char"

let is_char_numeric char =
  match char with
    Char c -> if '0' <= c && c <= '9' then t else f
  | _ -> failwith "char-numeric?: not a char"

let is_char_whitespace char =
  match char with
    Char c -> if c = ' ' || c = '\t' || c = '\n' || c = '\r' then t else f
  | _ -> failwith "char-whitespace?: not a char"

let is_char_upper_case letter =
  match letter with
    Char c -> if c <= 'Z' && 'A' <= c then t else f
  | _ -> failwith "char-upper-case?: not a char"

let is_char_lower_case letter =
  match letter with
    Char c -> if 'a' <= c && c <= 'z' then t else f
  | _ -> failwith "char-lower-case?: not a char"

let char_to_integer char =
  match char with
    Char char -> Int (int_of_char char)
  | _ -> failwith "char->integer: not a char"

let integer_to_char n =
  match n with
    Int n -> Char (char_of_int n)
  | _ -> failwith "integer->char: not an integer"

let is_string string =
  match string with
    String _ -> t
  | _ -> f

let string_length string =
  match string with
    String string -> Int (String.length string)
  | _ -> failwith "string-length: not a string"

let string_ref string k =
  match string with
    String s ->
      begin match k with
        Int n -> Char s.[n]
      | _ -> failwith "string-ref: not an integer"
      end
  | _ -> failwith "string-ref: not a string"

let string_set string k char =
  match string with
    String s ->
      begin match k with
        Int n ->
          begin match char with
            Char c -> s.[n] <- c; Void
          | _ -> failwith "string-set!: not a char"
          end
      | _ -> failwith "string-set!: not an integer"
      end
  | _ -> failwith "string-set!: not a string"

let substring string start finish =
  match string with
    String string ->
      begin match start with
        Int n ->
          begin match finish with
            Int m -> String (String.sub string n (m - n + 1))
          | _ -> failwith "substring: end is not an integer"
          end
      | _ -> failwith "substring: start is not an integer"
      end
  | _ -> failwith "substring: string is not a string"

let string_append strings =
  let rec loop strings =
    match strings with
      Nil -> ""
    | Cons {car = a; cdr = b} ->
        begin match a with
          String string -> string ^ loop b
        | _ -> failwith "string-append: not a list of strings"
        end
    | _ -> failwith "string-append: not a list of strings"
  in
  String (loop strings)

let string_to_list string =
  match string with
    String string ->
      let len = String.length string in
      let rec loop i =
        if i >= len then Nil
        else Cons {car = Char string.[i]; cdr = loop (i + 1)}
      in
      loop 0
  | _ -> failwith "string->list: not a string"

let list_to_string cons =
  let rec loop i cons =
    match cons with
      Nil -> String.make i '\000'
    | Cons {car = Char c; cdr = cons'} ->
        let string = loop (i + 1) cons' in string.[i] <- c; string
    | _ -> failwith "list->string: not a list of chars"
  in
  String (loop 0 cons)

let string_copy string =
  match string with
    String string -> String (String.copy string)
  | _ -> failwith "string-copy: not a string"

let string_fill string char =
  match string with
    String string ->
      begin match char with
        Char char -> String.fill string 0 (String.length string) char; Void
      | _ -> failwith "string-fill!: not a char"
      end
  | _ -> failwith "string-fill!: not a string"

let is_input_port obj =
  match obj with
    In _ -> t
  | _ -> f

let is_output_port obj =
  match obj with
    Out _ -> t
  | _ -> f

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
      let result = apply thunk Nil in
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
