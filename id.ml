type t = {
  name : string;
  stamp : int
}

let genid =
  let counter = ref 0 in
  (fun x -> incr counter; {name = x; stamp = !counter})
