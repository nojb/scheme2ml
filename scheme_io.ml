open Scheme

let read_from_port port =
  match port with
    In port ->
      begin match port.peek with
        None ->
          let lexbuf = Lexing.from_channel port.ch in
          Parser.ast Lexer.token lexbuf
      | Some c ->
          let lexbuf =
            Lexing.from_function
              (fun s n ->
                 if n > 0 then
                   begin
                     s.[0] <- c;
                     port.peek <- None;
                     input port.ch s 1 (n - 1)
                   end
                 else 0)
          in
          Parser.ast Lexer.token lexbuf
      end
  | _ -> failwith "read: not a port"

let read () = read_from_port (In !current_in)

let read_char_from_port port =
  match port with
    In port ->
      begin match port.peek with
        None -> (try Char (input_char port.ch) with End_of_file -> Void)
      | Some c -> port.peek <- None; Char c
      end
  | _ -> failwith "read-char: not a port"

let read_char () = read_char_from_port (In !current_in)

let peek_char_from_port port =
  match port with
    In port ->
      begin match port.peek with
        Some c -> Char c
      | None ->
          try let c = input_char port.ch in port.peek <- Some c; Char c with
            End_of_file -> Void
      end
  | _ -> failwith "peek-char: not a port"

let peek_char () = peek_char_from_port (In !current_in)

let is_eof_object obj =
  match obj with
    Void -> t
  | _ -> f

(* value is_char_ready_on_port port =
  if * port#is_char_ready () then t else f *
  match port with
  [ In port ->
    match port.peek with
    [ None -> do {
        try 
      }
    | Some _ -> t ]
  | _ -> failwith "char-ready?: not a port" ];

value is_char_ready () =
  is_char_ready_on_port current_in.val;*)

(*
class input_port = object
  method virtual peek : unit -> char;
  method virtual read_char : unit -> char;
  method virtual is_char_ready : unit -> bool;
  method virtual lexbuf : unit -> Lexing.lexbuf;
end;

class output_port = object
  method virtual write_char : char -> unit;
end;
*)
