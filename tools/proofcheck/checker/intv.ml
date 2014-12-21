open Batteries
include Interval
type t = interval

let make l h = {low=l; high=h}

let top = {low=neg_infinity; high=infinity}

let order {low=l1; high=h1} {low=l2; high=h2} =
  l2 <= l1 && h1 <= h2

let width {low=l; high=h} = h -. l

let left_bound {low=l; high=h} = l

let right_bound {low=l; high=h} = h

let equals {low = l1; high = h1} {low = l2; high = h2} : bool
    = (Float.compare l1 l2) = 0 && (Float.compare h1 h2) = 0

let join = Interval.union_I_I

let meet {low=l1; high=h1} {low=l2; high=h2} =
  {low = max l1 l2; high = min h1 h2}

let contain_z {low = l; high = h} = l <= 0.0 && 0.0 <= h
let contain_pz {low = l; high = h} = h >= 0.0
let contain_nz {low = l; high = h} = l <= 0.0

let print out {low=l; high=h} =
  Printf.fprintf out "[%.30f, %.30f]" l h

(** Given interval i1 and i2 which is a subset of i1, partition i1 *)
(** into a set of disjoint intervals including i2.                 *)
(**                                                                *)
(** Input:                                                         *)
(**          [              [           ]                ]         *)
(**          l1             l2          h2              h1         *)
(**                                                                *)
(** Output:                                                        *)
(**          [              ]                                      *)
(**          l1             l2                                     *)
(**                         [           ]                          *)
(**                         l2          h2                         *)
(**                                     [                ]         *)
(**                                     h2              h1         *)
let partition ({low = l1; high = h1} : t) ({low = l2; high = h2} : t) : t list =
  match (l1 = l2, l2 = h2, h2 = h1) with
  | (false, false, false) ->
     [{low = l1; high = l2};
      {low = l2; high = h2};
      {low = h2; high = h1}]
  | (true, false, false) ->
     [{low = l2; high = h2};
      {low = h2; high = h1}]
  | (false, true, false) ->
     [{low = l1; high = l2};
      {low = h2; high = h1}]
  | (false, false, true) ->
     [{low = l1; high = l2};
      {low = l2; high = h2}]
  | (true, true, false) ->
     [{low = h2; high = h1}]
  | (true, false, true) ->
     [{low = l2; high = h2}]
  | (false, true, true) ->
     [{low = l1; high = l2}]
  | ( true,  true,  true) ->
     [{low = l1; high = h1}]
