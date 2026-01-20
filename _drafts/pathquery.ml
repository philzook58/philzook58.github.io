
type constr = Eq of string * string

type query = Select of string * query | Join of query * query
  ;;


let opt1 (q : query) = match q with
  | Select (col, Join (q1, q2)) -> Some (col, q1, q2)
  | _ -> None
;;


print_endline "Hello, Pathquery!"