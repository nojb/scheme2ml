type in_port = {
  ch : in_channel;
  peek : mutable option char
};

type out_port = out_channel;

type t =
  [ Int of int
  | Symbol of string
  | Boolean of bool
  | Char of char
  | Vector of array t
  | String of string
  | Cons of cons
  | Lambda of t -> t
  | Lambda0 of unit -> t
  | Lambda1 of t -> t
  | Lambda2 of t -> t -> t
  | Lambda3 of t -> t -> t -> t
  | Lambda4 of t -> t -> t -> t -> t
  | Promise of Lazy.t t
  | Void
  | In of in_port
  | Out of out_port
  | Nil ]

and cons = {
  car : mutable t;
  cdr : mutable t
};

value t = Boolean True;
value f = Boolean False;

module W = Weak.Make (
  struct
    type t2 = t;
    type t = t2;
    value equal x y =
      match (x, y) with
      [ (Symbol s, Symbol t) -> String.compare s t = 0
      | _ -> False ];
    value hash = Hashtbl.hash;
  end);

value symbols = W.create 10;

(* be careful --- this definition (interning
 * the string, instead of the Symbol ..., means
 * that when we want to eq? two symbols we have to
 * pointer-compare the string!, not the symbol. cf.
 * the definition of eqp below *)

value intern s = W.merge symbols (Symbol s);

value is_procedure obj =
  match obj with
  [ Lambda _ | Lambda0 _ | Lambda1 _
  | Lambda2 _ | Lambda3 _ | Lambda4 _ -> t
  | _ -> f ];

value is_eq a b =
  if a == b then t else f;

  (* my implementation of eqv? compares strings char by char *)
value is_eqv a b =
  if a == b then t
  else
  match (a, b) with
  [ (Char a, Char b) -> if a = b then t else f
  | (Vector a, Vector b) -> if a == b then t else f
  | (String a, String b) -> if a = b then t else f
  | (Int a, Int b) -> if a = b then t else f
  | _ -> f ];

value is_equal a b =
  if a == b then t else
  let rec is_equal_aux a b =
  match (a, b) with
  [ (Char a, Char b) -> a = b
  | (Cons a, Cons b) ->
      is_equal_aux a.car b.car && is_equal_aux a.cdr b.cdr
  | (Vector a, Vector b) ->
      let la = Array.length a in
      let lb = Array.length b in
      if la <> lb then False
      else let rec loop i =
        if i >= la then True
        else if is_equal_aux a.(i) b.(i) then loop (i+1)
        else False
      in loop 0
  | (String a, String b) -> a = b
  | (Int a, Int b) -> a = b
  | _ -> False ]
  in if is_equal_aux a b then t else f;

value rec splice lst z =
  match lst with
  [ Cons {car=a;cdr=b} ->
    Cons {car=a;cdr=splice b z}
  | Nil -> z
  | _ -> failwith "splice: not a list" ];

value rec fold_left f start cons =
  match cons with
  [ Cons cons ->
    fold_left f (f start cons.car) cons.cdr
  | Nil -> start
  | _ -> failwith "fold-left: not a list" ];

value add2 obj1 obj2 =
  match obj1 with
  [ Int n ->
    match obj2 with
    [ Int m -> Int (n + m)
    | _ -> failwith "+: bad arguments" ]
  | _ -> failwith "+: bad arguments" ];

value add args =
  Int (fold_left (fun start next ->
    match next with
    [ Int n -> start + n
    | _ -> failwith "+: bad arguments" ]) 0 args);

value mul2 obj1 obj2 =
  match obj1 with
  [ Int n ->
    match obj2 with
    [ Int m -> Int (n * m)
    | _ -> failwith "*: bad arguments" ]
  | _ -> failwith "*: bad arguments" ];

value mul args =
  Int (fold_left (fun start next ->
    match next with
    [ Int n -> start * n
    | _ -> failwith "*: bad arguments" ]) 1 args);

value sub2 obj1 obj2 =
  match obj1 with
  [ Int n ->
    match obj2 with
    [ Int m -> Int (n - m)
    | _ -> failwith "-: bad arguments" ]
  | _ -> failwith "-: bad arguments" ];

value sub args =
  match args with
  [ Cons {car = Int n; cdr = Nil} -> Int (- n)
  | Cons {car = Int n; cdr = rest} ->
    Int (fold_left (fun start next ->
      match next with
      [ Int n -> start - n
      | _ -> failwith "-: bad arguments" ]) n rest)
  | Nil -> Int 0
  | _ -> failwith "-: bad arguments" ];

value remainder n1 n2 =
  match (n1, n2) with
  [ (Int n1, Int n2) -> Int (n1 mod n2)
  | _ -> failwith "remainder: not a pair of ints" ];

value cmp_nums name cmp z1 z2 rest =
  match (z1, z2) with
  [ (Int z1, Int z2) ->
    let rec loop last rest =
      match rest with
      [ Nil -> t
      | Cons { car = Int a; cdr = rest } ->
          if cmp last a then loop a rest
          else f
      | _ -> failwith (name ^ ": not numbers") ]
    in if cmp z1 z2 then loop z2 rest else f
  | _ -> failwith (name ^ ": not numbers") ];

value lt z1 z2 rest =
  cmp_nums "<" (fun a b -> a < b) z1 z2 rest;

value gt z1 z2 rest =
  cmp_nums ">" (fun a b -> a > b) z1 z2 rest;

value le z1 z2 rest =
  cmp_nums "<=" (fun a b -> a <= b) z1 z2 rest;

value ge z1 z2 rest =
  cmp_nums ">=" (fun a b -> a >= b) z1 z2 rest;

value eq z1 z2 rest =
  cmp_nums "=" (fun a b -> a == b) z1 z2 rest;

value rec to_string = fun
  [ Int n -> string_of_int n
  | Symbol s -> s
  | Boolean True -> "#t"
  | Boolean False -> "#f"
  | Char c -> String.make 1 c
  | String s -> s
  | Vector vector ->
      let len = Array.length vector in
      let rec loop i =
        if i >= len then ")"
        else if i = len-1 then (to_string vector.(i)) ^ ")"
        else (to_string vector.(i)) ^ " " ^ (loop (i+1))
      in "#(" ^ (loop 0)
  | In _ -> "#<input-port>"
  | Out _ -> "#<output-port>"
  | Cons cons ->
    let rec loop cons =
    match cons.cdr with
    [ Nil -> to_string cons.car
    | Cons cons' -> to_string cons.car ^ " " ^ (loop cons')
    | a -> to_string cons.car ^ " . " ^ to_string a ]
    in ("(" ^ loop cons ^ ")")
  | Nil -> "()"
  | Void -> ""
  | Promise _ -> "#<promise>"
  | Lambda _
  | Lambda0 _
  | Lambda1 _
  | Lambda2 _
  | Lambda3 _
  | Lambda4 _ -> "#<closure>" ];

value display x =
  let _ = print_string (to_string x) in Void;

value apply f args =
  match f with
  [ Lambda f -> f args
  | Lambda0 f ->
    match args with
    [ Nil -> f ()
    | _ -> failwith "apply: arity error" ]
  | Lambda1 f ->
    match args with
    [ Cons {car=arg1;cdr=Nil}-> f arg1
    | _ -> failwith "apply: arity error" ]
  | Lambda2 f ->
    match args with
    [ Cons {car=arg1;cdr=Cons{car=arg2;cdr=Nil}} -> f arg1 arg2
    | _ -> failwith "apply: arity error" ]
  | Lambda3 f ->
    match args with
    [ Cons{car=a1;cdr=Cons{car=a2;cdr=Cons{car=a3;cdr=Nil}}} -> f a1 a2 a3
    | _ -> failwith "apply: arity error" ]
  | Lambda4 f ->
    match args with
    [ Cons{car=a1;cdr=Cons{car=a2;cdr=Cons{car=a3;cdr=Cons{car=a4;cdr=Nil}}}} ->
      f a1 a2 a3 a4
    | _ -> failwith "apply: arity error" ]
  | _ -> failwith "apply: not a function" ];

value apply0 f =
  match f with
  [ Lambda f -> f Nil
  | Lambda0 f -> f ()
  | Lambda1 _
  | Lambda2 _
  | Lambda3 _
  | Lambda4 _ -> failwith "apply: arity error"
  | _ -> failwith "apply: not a function" ];

value apply1 f a =
  match f with
  [ Lambda f -> f (Cons{car=a;cdr=Nil})
  | Lambda1 f -> f a
  | Lambda0 _
  | Lambda2 _
  | Lambda3 _
  | Lambda4 _ -> failwith "apply: arity error"
  | _ -> failwith "apply: not a function" ];

value apply2 f a b =
  match f with
  [ Lambda f -> f (Cons{car=a;cdr=Cons{car=b;cdr=Nil}})
  | Lambda2 f -> f a b
  | Lambda0 _
  | Lambda1 _
  | Lambda3 _
  | Lambda4 _ -> failwith "apply: arity error"
  | _ -> failwith "apply: not a function" ];

value apply3 f a b c =
  match f with
  [ Lambda f -> f (Cons{car=a;cdr=Cons{car=b;cdr=Cons{car=c;cdr=Nil}}})
  | Lambda3 f -> f a b c
  | Lambda0 _
  | Lambda1 _
  | Lambda2 _
  | Lambda4 _ -> failwith "apply: arity error"
  | _ -> failwith "apply: not a function" ];

value apply4 f a b c d =
  match f with
  [ Lambda f -> f
  (Cons{car=a;cdr=Cons{car=b;cdr=Cons{car=c;cdr=Cons{car=d;cdr=Nil}}}})
  | Lambda4 f -> f a b c d
  | Lambda0 _
  | Lambda1 _
  | Lambda2 _
  | Lambda3 _ -> failwith "apply: arity error"
  | _ -> failwith "apply: not a function" ];

value is_true x =
  not (x == f);
  (* fun
  [ Boolean False -> False
  | _ -> True ]; *)

value is_zero number =
  match number with
  [ Int n -> if n = 0 then t else f
  | _ -> failwith "zero?: wrong argument type" ];

value is_integer obj =
  match obj with
  [ Int n -> t
  | _ -> f ];

value is_number obj =
  match obj with
  [ Int n -> t
  | _ -> f ];

value car = fun
  [ Cons cons -> cons.car
  | _ -> failwith "car: not a pair" ];

value cdr = fun
  [ Cons cons -> cons.cdr
  | _ -> failwith "cdr: not a pair" ];

value cadr = fun
  [ Cons { car = _; cdr = Cons { car = a; cdr = _ }} -> a
  | _ -> failwith "cadr: bad args" ];

value cddr = fun
  [ Cons { car = _; cdr = Cons { car = _; cdr = a}} -> a
  | _ -> failwith "cddr: bad args" ];

value cdar = fun
  [ Cons{car=Cons{car=_;cdr=a};cdr=_} -> a
  | _ -> failwith "cdar: bad args" ];

value caar = fun
  [ Cons { car = Cons { car = a; cdr = _}; cdr = _} -> a
  | _ -> failwith "caar: bad args" ];

value caaar = fun
  [ Cons{car=Cons{car=Cons{car=a;cdr=_};cdr=_};cdr=_} -> a
  | _ -> failwith "caaar: bad args" ];

value caddr = fun
  [ Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=a;cdr=_}}} -> a
  | _ -> failwith "caddr: bad args" ];

value caadr = fun
  [ Cons{car=_;cdr=Cons{car=Cons{car=a;cdr=_};cdr=_}} -> a
  | _ -> failwith "caadr: bad args" ];

value cdddr = fun
  [ Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=_;cdr=a}}} -> a
  | _ -> failwith "cdddr: bad args" ];

value cdadr = fun
  [ Cons{car=_;cdr=Cons{car=Cons{car=_;cdr=a};cdr=_}} -> a
  | _ -> failwith "cdadr: bad args" ];

value cadddr = fun
  [ Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=a;cdr=_}}}} -> a
  | _ -> failwith "cadddr: bad args" ];

value number_to_string = fun
  [ Int n -> String (string_of_int n)
  | _ -> failwith "number->string: not a number" ];

value is_boolean = fun
  [ Boolean _ -> t
  | _ -> f ];

value _not obj =
  if is_true obj then f
  else t;

value is_pair = fun
  [ Cons _ -> t
  | _ -> f ];

value cons x y =
  Cons { car = x; cdr = y };

value set_car_bang pair obj =
  match pair with
  [ Cons cons -> do { cons.car := obj; Void }
  | _ -> failwith "set-car!: not a pair" ];

value set_cdr_bang pair obj =
  match pair with
  [ Cons cons -> do { cons.cdr := obj; Void }
  | _ -> failwith "set-cdr!: not a pair" ];

value is_null = fun
  [ Nil -> t
  | _ -> f ];

value rec map f lists =
  let rec join1 at_nil lists =
    match lists with
    [ Nil -> (Nil, Nil)
    | Cons {
        car = Cons {
          car = a;
          cdr = b
        };
        cdr = b'
      } ->
        if at_nil < 0 then
          failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          (Cons {car = a; cdr = heads}, Cons {car = b; cdr = tails})
    | Cons {
        car = Nil;
        cdr = z
      } ->
        if at_nil > 0 then
          failwith "map: lists not of the same length"
        else
          join1 (-1) z
    | _ -> failwith "map: not a list of lists" ]
  in match join1 0 lists with
  [ (Nil, Nil) -> Nil
  | (heads, tails) ->
      Cons {
        car = apply f heads;
        cdr = map f tails } ];

value rec for_each f lists =
  let rec join1 at_nil lists =
    match lists with
    [ Nil -> (Nil, Nil)
    | Cons {
        car = Cons {
          car = a;
          cdr = b
        };
        cdr = b'
      } ->
        if at_nil < 0 then
          failwith "map: lists not of the same length"
        else
          let (heads, tails) = join1 1 b' in
          (Cons {car = a; cdr = heads}, Cons {car = b; cdr = tails})
    | Cons {
        car = Nil;
        cdr = z
      } ->
        if at_nil > 0 then
          failwith "map: lists not of the same length"
        else
          join1 (-1) z
    | _ -> failwith "map: not a list of lists" ]
  in match join1 0 lists with
  [ (Nil, Nil) -> Void
  | (heads, tails) -> do {
      ignore (apply f heads);
      for_each f tails
    } ];

value rec is_list = fun
  [ Cons cons -> is_list cons.cdr
  | Nil -> t
  | _ -> f ];

value list args =
  args;

value length list =
  let rec loop i list =
    match list with
    [ Nil -> i
    | Cons cons -> loop (i+1) cons.cdr
    | _ -> failwith "length: not a list" ]
  in Int (loop 0 list);

value rec append lists =
  match lists with
  [ Cons { car = first_list; cdr = Nil } ->
    first_list
  | Cons { car = first_list;
    cdr = rest } ->
    let rec loop = fun
      [ Cons cons -> Cons {car = cons.car; cdr = loop cons.cdr }
      | Nil -> append rest
      | _ -> failwith "append: malformed arguments" ]
    in loop first_list
  | Nil -> Nil
  | _ -> failwith "append: not a list of lists" ];

value rec append2 list1 list2 =
  match list1 with
  [ Nil -> list2
  | Cons{car=a;cdr=b} -> Cons{car=a;cdr=append2 b list2}
  | _ -> failwith "append: not a list" ];

value reverse list =
  let rec loop list reversed =
    match list with
    [ Nil -> reversed
    | Cons cons ->
      loop cons.cdr (Cons {car = cons.car; cdr = reversed})
    | _ -> failwith "reverse: not a list" ]
  in loop list Nil;

value list_tail list k =
  match k with
  [ Int k ->
    let rec loop list k =
      if k = 0 then list
      else match list with
      [ Cons cons -> loop cons.cdr (k-1)
      | Nil -> failwith "list-tail: list too short"
      | _ -> failwith "list-tail: not a list" ]
    in loop list k
  | _ -> failwith "list-tail: not an int" ];

value list_ref list k =
  match k with
  [ Int k ->
    let rec loop list k =
      match list with
      [ Cons cons -> if k = 0 then cons.car else loop cons.cdr (k-1)
      | Nil -> failwith "list-ref: list too short"
      | _ -> failwith "list-ref: not a list" ]
    in loop list k
  | _ -> failwith "list-ref: not an int" ];

value rec mem name cmp obj list =
  match list with
  [ Cons cons ->
    if is_true (cmp obj cons.car) then list
    else mem name cmp obj cons.cdr
  | Nil -> f
  | _ -> failwith (name ^ ": not a list") ];

value memq =
  mem "memq" is_eq;

value memv =
  mem "memv" is_eqv;

value member =
  mem "member" is_equal;

value rec ass name cmp obj alist =
  match alist with
  [ Cons {
      car = (Cons cons as z);
      cdr = rest
    } ->
      if is_true (cmp obj cons.car) then z
      else ass name cmp obj rest
  | Nil -> f
  | _ -> failwith (name ^ ": not an alist") ];

value assq =
  ass "assq" is_eq;

value assv =
  ass "assv" is_eqv;

value assoc =
  ass "assoc" is_equal;

value is_symbol = fun
  [ Symbol _ -> t
  | _ -> f ];

value symbol_to_string symbol =
  match symbol with
  [ Symbol symbol -> String (String.copy symbol)
  (* just in case -- otherwise, we have to consider having immutable strings *)
  | _ -> failwith "symbol->string: not a symbol" ];

value string_to_symbol string =
  match string with
  [ String string -> intern (String.copy string)
  | _ -> failwith "string->symbol: not a string" ];

value is_vector = fun
  [ Vector _ -> t
  | _ -> f ];

value vector objs =
  let rec loop len = fun
    [ Cons {car = obj; cdr = rest} ->
      let arr = loop (len+1) rest in do {
        arr.(len) := obj;
        arr
      }
    | Nil -> Array.make len Void
    | _ -> failwith "vector: bad arglist" ]
  in Vector (loop 0 objs);

value make_vector size =
  match size with
  [ Int n -> Vector (Array.make n Void)
  | _ -> failwith "make-vector: not an integer" ];

value vector_length vector =
  match vector with
  [ Vector vector -> Int (Array.length vector)
  | _ -> failwith "vector-length: not a vector" ];

value vector_ref vector k =
  match vector with
  [ Vector vector ->
    match k with
    [ Int n -> vector.(n)
    | _ -> failwith "vector-ref: bad index" ]
  | _ -> failwith "vector-ref: not a vector" ];

value vector_set vector k obj =
  match vector with
  [ Vector vector ->
    match k with
    [ Int n -> do {
        vector.(n) := obj;
        Void
      }
    | _ -> failwith "vector-set!: bad index" ]
  | _ -> failwith "vector-set!: not a vector" ];

value vector_to_list vector =
  match vector with
  [ Vector vector ->
    let l = Array.length vector in
    let rec loop i cdr =
      if i < 0 then cdr
      else loop (i-1) (Cons { car = vector.(i); cdr = cdr })
    in loop (l-1) Nil
  | _ -> failwith "vector->list: not a vector" ];

value list_to_vector list =
  let rec loop l list =
    match list with
    [ Nil -> Array.create l Nil
    | Cons {
        car = a;
        cdr = b
      } ->
        let arr = loop (l+1) b in do {
          arr.(l) := a;
          arr
        }
    | _ -> failwith "list->vector: not a list" ]
  in Vector (loop 0 list);

value vector_fill vector fill =
  match vector with
  [ Vector vector -> do {
      Array.fill vector 0 (Array.length vector) fill;
      Void
    }
  | _ -> failwith "vector-fill!: not a vector" ];

value is_char obj =
  match obj with
  [ Char _ -> t
  | _ -> f ];

value is_char_eq char1 char2 =
  match (char1, char2) with
  [ (Char char1, Char char2) -> if char1 = char2 then t else f
  | _ -> failwith "char=?: bad arguments" ];

value is_char_alphabetic char =
  match char with
  [ Char c -> if 'a' <= c  && c <= 'z' || 'A' <= c && c <= 'Z' then t else f
  | _ -> failwith "char-alphabetic?: not a char" ];

value is_char_numeric char =
  match char with
  [ Char c -> if '0' <= c && c <= '9' then t else f
  | _ -> failwith "char-numeric?: not a char" ];

value is_char_whitespace char =
  match char with
  [ Char c -> if c = ' ' || c = '\t' || c = '\n' || c = '\r' then t else f
  | _ -> failwith "char-whitespace?: not a char" ];

value is_char_upper_case letter =
  match letter with
  [ Char c -> if c <= 'Z' && 'A' <= c then t else f
  | _ -> failwith "char-upper-case?: not a char" ];

value is_char_lower_case letter =
  match letter with
  [ Char c -> if 'a' <= c && c <= 'z' then t else f
  | _ -> failwith "char-lower-case?: not a char" ];

value char_to_integer char =
  match char with
  [ Char char -> Int (int_of_char char)
  | _ -> failwith "char->integer: not a char" ];

value integer_to_char n =
  match n with
  [ Int n -> Char (char_of_int n)
  | _ -> failwith "integer->char: not an integer" ];

value is_string string =
  match string with
  [ String _ -> t
  | _ -> f ];

value string_length string =
  match string with
  [ String string -> Int (String.length string)
  | _ -> failwith "string-length: not a string" ];

value string_ref string k =
  match string with
  [ String s ->
    match k with
    [ Int n -> Char (s.[n])
    | _ -> failwith "string-ref: not an integer" ]
  | _ -> failwith "string-ref: not a string" ];

value string_set string k char =
  match string with
  [ String s ->
    match k with
    [ Int n ->
      match char with
      [ Char c -> do {
          s.[n] := c;
          Void
        }
      | _ -> failwith "string-set!: not a char" ]
    | _ -> failwith "string-set!: not an integer" ]
  | _ -> failwith "string-set!: not a string" ];

value substring string start finish =
  match string with
  [ String string ->
    match start with
    [ Int n ->
      match finish with
      [ Int m -> String (String.sub string n (m-n+1))
      | _ -> failwith "substring: end is not an integer" ]
    | _ -> failwith "substring: start is not an integer" ]
  | _ -> failwith "substring: string is not a string" ];

value string_append strings =
  let rec loop strings =
    match strings with
    [ Nil -> ""
    | Cons {
        car = a;
        cdr = b
      } ->
        match a with
        [ String string ->
          string ^ (loop b)
        | _ -> failwith "string-append: not a list of strings" ]
    | _ -> failwith "string-append: not a list of strings" ]
  in String (loop strings);

value string_to_list string =
  match string with
  [ String string ->
    let len = String.length string in
    let rec loop i =
      if i >= len then Nil
      else Cons {car = Char string.[i]; cdr = loop (i+1)}
    in loop 0
  | _ -> failwith "string->list: not a string" ];

value list_to_string cons =
  let rec loop i cons =
    match cons with
    [ Nil -> String.make i '\000'
    | Cons {car = Char c; cdr = cons'} ->
      let string = loop (i+1) cons' in do {
        string.[i] := c;
        string
      }
    | _ -> failwith "list->string: not a list of chars" ]
  in String (loop 0 cons);

value string_copy string =
  match string with
  [ String string -> String (String.copy string)
  | _ -> failwith "string-copy: not a string" ];

value string_fill string char =
  match string with
  [ String string ->
    match char with
    [ Char char -> do {
        String.fill string 0 (String.length string) char;
        Void
      }
    | _ -> failwith "string-fill!: not a char" ]
  | _ -> failwith "string-fill!: not a string" ];

value is_input_port obj =
  match obj with
  [ In _ -> t
  | _ -> f ];

value is_output_port obj =
  match obj with
  [ Out _ -> t
  | _ -> f ];

value std_in = { ch = stdin; peek = None };
value std_out = stdout;

value current_in = ref std_in;
value current_out = ref std_out;

value current_input_port () =
  current_in.val;

value current_output_port () =
  current_out.val;

value with_input_from_file string thunk =
  match string with
  [ String string ->
    let old_in = current_in.val in do {
      let ch = open_in string in
      current_in.val := { ch = ch; peek = None };
      let result = apply thunk Nil in
      close_in ch;
      current_in.val := old_in;
      result
    }
  | _ -> failwith "with-input-from-file: not a string" ];

value open_input_file filename =
  match filename with
  [ String filename -> In {ch = open_in filename; peek = None }
  | _ -> failwith "open-input-file: not a string" ];

value open_output_file filename =
  match filename with
  [ String filename -> Out (open_out filename)
  | _ -> failwith "open-output-file: not a string" ];

value close_input_port port =
  match port with
  [ In port -> do { close_in port.ch; Void }
  | _ -> failwith "close-input-port: not a port" ];

value close_output_port port =
  match port with
  [ Out ch -> do { close_out ch; Void }
  | _ -> failwith "close-output-port: not a port" ];

value newline () = do {
  output_char current_out.val '\n';
  flush current_out.val;
  Void
};

value newline_to_port port =
  match port with
  [ Out port -> do {
      output_char port '\n';
      flush port;
      Void
    }
  | _ -> failwith "newline: not a port" ];

value write_char char =
  match char with
  [ Char char -> do {
      output_char current_out.val char;
      Void
    }
  | _ -> failwith "write-char: not a char" ];

value write_char_to_port char port =
  match char with
  [ Char char ->
    match port with
    [ Out port -> do {
        output_char port char;
        Void
      }
    | _ -> failwith "write-char: not a port" ]
  | _ -> failwith "write-char: not a char" ];

value error msg objs =
  failwith ("error: " ^ (to_string msg) ^ ": " ^ (to_string objs));

value force obj =
  match obj with
  [ Promise obj -> Lazy.force obj
  | _ -> failwith "force: not a promise" ];
