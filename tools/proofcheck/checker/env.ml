open Batteries

exception CException of string

type key = string
type intv = Intv.t
type t = (key, intv) Map.t

let keys = Map.keys

let find (x : key) (e : t) : intv
    = Map.find x e

let order (e1 : t) (e2 : t) : bool =
  Map.for_all
    (fun x i1 ->
      let i2 = find x e2 in
      Intv.order i1 i2
    )
    e1

let join (e1 : t) (e2 : t) : t =
  Map.merge
    (fun x i1_op i2_op ->
      match (i1_op, i2_op) with
          (Some i1, Some i2) -> Some (Intv.join i1 i2)
        | _ -> raise (CException "Merge fail"))
    e1
    e2

let print out =
  Map.print ~first:"" ~last:"\n" ~sep:", \n"
    String.print
    Intv.print
    out

let to_list (e : t) : (key * intv) list
    = List.of_enum (Map.backwards e)

let from_list (l : (key * intv) list) : t =
  List.fold_left
    (fun e (k, i) -> Map.add k i e)
    Map.empty
    l

let make = from_list

let equals (e1 : t) (e2 : t) : bool =
  not (List.mem
       false
       (List.map
          (fun ((_, i1), (_, i2)) ->
            Intv.equals i1 i2)
          (List.combine (to_list e1) (to_list e2))))

let is_empty (e : t) : bool =
  List.mem true
    (List.map
       (fun (_, {Intv.low = l; Intv.high = h})
       -> (Float.compare l h) = 0)
       (to_list e))

(** partition e1 e2 : Partition Box e1 into subboxes which includes e2 *)
let partition (e1 : t) (e2 : t) : (t list) =
  let l1 = to_list e1 in
  let l2 = to_list e2 in
  let l =  List.map
             (fun ((key1, i1), (key2, i2)) ->
              assert(key1 = key2);
              let partitions = Intv.partition i1 i2 in
              List.map (fun i -> (key1, i)) partitions)
             (List.combine l1 l2)
  in
  List.map
    (fun l -> from_list l)
    (List.n_cartesian_product l)

let left_bound (e : t) : (string, float) Map.t =
  let keys = keys e in
  let items = Enum.map
    (fun key -> let intv = find key e in
             let v = Intv.left_bound intv in
             (key, v)
    )
    keys in
  Map.of_enum items

let right_bound (e : t) : float list =
  let keys = List.of_enum (keys e) in
  List.map
    (fun key -> let intv = find key e in Intv.right_bound intv)
    keys
