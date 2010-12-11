type in_port = {
  ch : in_channel;
  peek : mutable option char
};

type out_port = out_channel;

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
  | In of in_port
  | Out of out_port
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

value intern s =
  let s = Symbol s in
  try W.find symbols s
  with [ Not_found -> do {
    W.add symbols s; s
  } ];

value is_eq a b =
  if a == b then t else f;

value is_eqv a b =
  match (a, b) with
  [ (Symbol a, Symbol b) -> if String.compare a b = 0 then t else f
  | (Boolean a, Boolean b) -> if a = b then t else f
  | (Char a, Char b) -> if a = b then t else f
  | (Nil, Nil) -> t
  | (Void, Void) -> t
  | (Cons a, Cons b) -> if a == b then t else f
  | (Vector a, Vector b) -> if a == b then t else f
  | (String a, String b) -> if a == b then t else f
  | (Lambda a, Lambda b) -> if a == b then t else f
  | (Num a, Num b) -> if Num.eq_num a b then t else f
  | (In a, In b) -> if a == b then t else f
  | (Out a, Out b) -> if a == b then t else f
  | _ -> f ];

value is_equal a b =
  let rec is_equal_aux a b =
  match (a, b) with
  [ (Symbol a, Symbol b) -> String.compare a b = 0
  | (Boolean a, Boolean b) -> a = b
  | (Char a, Char b) -> a = b
  | (Nil, Nil) -> True
  | (Void, Void) -> True
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
  | (String a, String b) -> String.compare a b = 0
  | (Lambda a, Lambda b) -> a == b
  | (Num a, Num b) -> Num.eq_num a b
  | (In a, In b) -> a == b
  | (Out a, Out b) -> a == b
  | _ -> False ]
  in if is_equal_aux a b then t else f;

value rec fold_left f start cons =
  match cons with
  [ Cons cons ->
    fold_left f (f start cons.car) cons.cdr
  | Nil -> start
  | _ -> failwith "fold-left: not a list" ];

value rec splice lst obj =
  match lst with
  [ Cons {car=a;cdr=b} -> Cons{car=a;cdr=splice b obj}
  | Nil -> obj
  | _ -> failwith "splice: not a list" ];

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

value cmp_nums name cmp z1 z2 rest =
  match (z1, z2) with
  [ (Num z1, Num z2) ->
    let rec loop last rest =
      match rest with
      [ Nil -> t
      | Cons { car = Num a; cdr = rest } ->
          if cmp last a then loop a rest
          else f
      | _ -> failwith (name ^ ": not numbers") ]
    in if cmp z1 z2 then loop z2 rest else f
  | _ -> failwith (name ^ ": not numbers") ];

value lt z1 z2 rest =
  cmp_nums "<" Num.lt_num z1 z2 rest;

value gt z1 z2 rest =
  cmp_nums ">" Num.gt_num z1 z2 rest;

value le z1 z2 rest =
  cmp_nums "<=" Num.le_num z1 z2 rest;

value ge z1 z2 rest =
  cmp_nums ">=" Num.ge_num z1 z2 rest;

value eq z1 z2 rest =
  cmp_nums "=" Num.eq_num z1 z2 rest;

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

value is_integer obj =
  match obj with
  [ Num n -> if Num.is_integer_num n then t else f
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

value cadddr = fun
  [ Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=_;cdr=Cons{car=a;cdr=_}}}} -> a
  | _ -> failwith "cadddr: bad args" ];

value number_to_string = fun
  [ Num n -> String (Num.string_of_num n)
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

value rec is_list = fun
  [ Cons cons -> is_list cons.cdr
  | Nil -> t
  | _ -> f ];

value length list =
  let rec loop i list =
    match list with
    [ Nil -> i
    | Cons cons -> loop (i+1) cons.cdr
    | _ -> failwith "length: not a list" ]
  in Num (Num.num_of_int (loop 0 list));

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

value reverse list =
  let rec loop list reversed =
    match list with
    [ Nil -> reversed
    | Cons cons ->
      loop cons.cdr (Cons {car = cons.car; cdr = reversed})
    | _ -> failwith "reverse: not a list" ]
  in loop list Nil;

value to_int string k =
  match k with
  [ Num n ->
    if Num.is_integer_num n then
      let i = Num.big_int_of_num n in
      if Big_int.is_int_big_int i then
        Big_int.int_of_big_int i
      else
        failwith (string ^ ": not an int")
    else
      failwith (string ^ ": not an int")
  | _ -> failwith (string ^ ": not an int") ];

value list_tail list k =
  let k = to_int "list-tail" k in
  let rec loop list k =
    if k = 0 then list
    else match list with
    [ Cons cons -> loop cons.cdr (k-1)
    | Nil -> failwith "list-tail: list too short"
    | _ -> failwith "list-tail: not a list" ]
  in loop list k;

value list_ref list k =
  let k = to_int "list-ref" k in
  let rec loop list k =
    match list with
    [ Cons cons -> if k = 0 then cons.car else loop cons.cdr (k-1)
    | Nil -> failwith "list-ref: list too short"
    | _ -> failwith "list-ref: not a list" ]
  in loop list k;

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
