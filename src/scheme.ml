type inchan = {
  in_chan : in_channel;
  peek : mutable option char
};

type t =
  [ Num of Num.num
  | Symbol of string
  | Boolean of bool
  | Char of char
  | Vector of array t
  | String of string
  | Cons of cons
  | Lambda of t -> t
  | Void
  | Nil ]

and cons = {
  car : mutable t;
  cdr : mutable t
};

value t = Boolean True;
value f = Boolean False;
value num_zero = Num.num_of_int 0;
value num_one = Num.num_of_int 1;

module W = Weak.Make (
  struct
    type t = string;
    value equal x y = String.compare x y == 0;
    value hash = Hashtbl.hash;
  end);

value symbols = W.create 10;

(* be careful --- this definition (interning
 * the string, instead of the Symbol ..., means
 * that when we want to eq? two symbols we have to
 * pointer-compare the string!, not the symbol. cf.
 * the definition of eqp below *)

value intern s =
  try Symbol (W.find symbols s)
  with [ Not_found -> do {
    W.add symbols s;
    Symbol s
  } ];

value eqp a b =
  match (a, b) with
  [ (Symbol x, Symbol y) -> if x == y then t else f
  | (Boolean x, Boolean y) -> if x = y then t else f
  | _ -> if a == b then t else f ];

value rec fold_left f start cons =
  match cons with
  [ Cons cons ->
    fold_left f (f start cons.car) cons.cdr
  | Nil -> start
  | _ -> failwith "fold_left: not a list" ];

value rec map f cons =
  match cons with
  [ Cons cons -> Cons {car = f cons.car; cdr = map f cons.cdr}
  | Nil -> Nil
  | _ -> failwith "map: not a list" ];

value add2 obj1 obj2 =
  match obj1 with
  [ Num n ->
    match obj2 with
    [ Num m -> Num (Num.add_num n m)
    | _ -> failwith "+: bad arguments" ]
  | _ -> failwith "+: bad arguments" ];

value add args =
  Num (fold_left (fun start next ->
    match next with
    [ Num n -> Num.add_num start n
    | _ -> failwith "+: bad arguments" ]) num_zero args);

value mul2 obj1 obj2 =
  match obj1 with
  [ Num n ->
    match obj2 with
    [ Num m -> Num (Num.mult_num n m)
    | _ -> failwith "*: bad arguments" ]
  | _ -> failwith "*: bad arguments" ];

value mul args =
  Num (fold_left (fun start next ->
    match next with
    [ Num n -> Num.mult_num start n
    | _ -> failwith "*: bad arguments" ]) num_one args);

value sub2 obj1 obj2 =
  match obj1 with
  [ Num n ->
    match obj2 with
    [ Num m -> Num (Num.sub_num n m)
    | _ -> failwith "-: bad arguments" ]
  | _ -> failwith "-: bad arguments" ];

value sub args =
  match args with
  [ Cons {car = Num n; cdr = Nil} -> Num (Num.sub_num num_zero n)
  | Cons {car = Num n; cdr = rest} ->
    Num (fold_left (fun start next ->
      match next with
      [ Num n -> Num.sub_num start n
      | _ -> failwith "-: bad arguments" ]) n rest)
  | Nil -> Num num_zero
  | _ -> failwith "-: bad arguments" ];

value rec to_string = fun
  [ Num n -> Num.string_of_num n
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
  | Cons cons ->
    let rec loop cons =
    match cons.cdr with
    [ Nil -> to_string cons.car
    | Cons cons' -> to_string cons.car ^ " " ^ (loop cons')
    | a -> to_string cons.car ^ " . " ^ to_string a ]
    in ("(" ^ loop cons ^ ")")
  | Nil -> "()"
  | Void -> ""
  | Lambda _ -> "#<closure>" ];

value display x =
  let _ = print_string (to_string x) in Void;

value apply f args =
  match f with
  [ Lambda f -> f args
  | _ -> failwith "apply: not a function" ];

value is_true = fun
  [ Boolean False -> False
  | _ -> True ];

value zerop = fun
  [ Num n -> if Num.eq_num n num_zero then t else f
  | _ -> failwith "zero?: wrong argument type" ];

value is_zero = zerop;

value car = fun
  [ Cons cons -> cons.car
  | _ -> failwith "car: not a pair" ];

value cdr = fun
  [ Cons cons -> cons.cdr
  | _ -> failwith "cdr: not a pair" ];

value number_to_string = fun
  [ Num n -> Num.string_of_num n
  | _ -> failwith "number->string: not a number" ];

value is_boolean = fun
  [ Boolean _ -> t
  | _ -> f ];

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

value rec is_list = fun
  [ Cons cons -> is_list cons.cdr
  | Nil -> t
  | _ -> f ];

value rec append lists =
  match lists with
  [ Cons { car = first_list;
    cdr = rest } ->
    let rec loop = fun
      [ Cons cons -> Cons {car = cons.car; cdr = loop cons.cdr }
      | Nil -> append rest
      | _ -> failwith "append: malformed arguments" ]
    in loop first_list
  | Nil -> Nil
  | _ -> failwith "append: not a list" ];

value is_symbol = fun
  [ Symbol _ -> t
  | _ -> f ];

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

value vector_length vector =
  match vector with
  [ Vector vector -> Num (Num.num_of_int (Array.length vector))
  | _ -> failwith "vector-length: not a vector" ];

value vector_ref vector k =
  match vector with
  [ Vector vector ->
    match k with
    [ Num n -> if Num.is_integer_num n then vector.(Num.int_of_num n) else
      failwith "vector-ref: bad index"
    | _ -> failwith "vector-ref: bad index" ]
  | _ -> failwith "vector-ref: not a vector" ];

value is_char obj =
  match obj with
  [ Char _ -> t
  | _ -> f ];

value is_char_eq char1 char2 =
  match (char1, char2) with
  [ (Char char1, Char char2) -> if char1 = char2 then t else f
  | _ -> failwith "char=?: bad arguments" ];

value char_to_integer char =
  match char with
  [ Char char -> Num (Num.num_of_int (int_of_char char))
  | _ -> failwith "char->integer: not a char" ];

value integer_to_char n =
  match n with
  [ Num n when Num.is_integer_num n -> Char (char_of_int (Num.int_of_num n))
  | _ -> failwith "integer->char: not an integer" ];

value newline () =
  print_newline ();

value string_length string =
  match string with
  [ String string -> Num (Num.num_of_int (String.length string))
  | _ -> failwith "string-length: not a string" ];

value string_ref string k =
  match string with
  [ String s ->
    match k with
    [ Num n when Num.is_integer_num n ->
      Char (s.[Num.int_of_num n])
    | _ -> failwith "string-ref: not an integer" ]
  | _ -> failwith "string-ref: not a string" ];

value string_set string k char =
  match string with
  [ String s ->
    match k with
    [ Num n when Num.is_integer_num n ->
      match char with
      [ Char c -> do {
          s.[Num.int_of_num n] := c;
          Void
        }
      | _ -> failwith "string-set!: not a char" ]
    | _ -> failwith "string-set!: not an integer" ]
  | _ -> failwith "string-set!: not a string" ];

value substring string start finish =
  match string with
  [ String string ->
    match start with
    [ Num n when Num.is_integer_num n ->
      let n = Num.int_of_num n in
      match finish with
      [ Num m when Num.is_integer_num m ->
        let m = Num.int_of_num m in
        String (String.sub string n (m-n+1))
      | _ -> failwith "substring: end is not an integer" ]
    | _ -> failwith "substring: start is not an integer" ]
  | _ -> failwith "substring: string is not a string" ];

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
