(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl,
 * Jacek Chrzaszcz, Antoni Żewierżejew
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)


(* module Rand for easy generating random ints up to max_int-1 *)
module Rand : (sig val get : unit -> int end) =
    struct
        let int64_of_max_int = Int64.of_int max_int
        let get () = Int64.to_int (Random.int64 int64_of_max_int)
    end

(*
    type representing interval set as treap tree
    interval is defined as (x, y) where x, y are its ends (inclusive), [x <= y] holds
    interval set is set of strictly disjoint intervals
    this type has two wariants
    [Null] - representing end of tree
    [Node of { l; r; interval; key; sum }]
    [l] and [r] are sons of the root
    [interval] is pair (x, y) representing interval
    [key] is randomized key used in constucting treap
    [sum] is sum of lengths of all intervals in subtree
    treap invariants:
    is a BST tree based on intervals
    is min-heap based on keys
*)
type node = { l: tree; r: tree; interval: int * int; key: int; sum: int }
and tree = Null | Node of node

(* renaming of type tree to fit iSet.mli *)
type t = tree

(* constant representing empty interval set *)
let empty = Null

(* returns if [t] is empty intreval set *)
let is_empty t = (t = empty)

(* returns interval set containing only interval (x, y) or empty set if [x > y] *)
let create_leaf x y =
    if x > y then empty else
    Node { l = Null; r = Null; interval = (x, y); key = Rand.get (); sum = y - x + 1 }

(* return sum of interval lenghts in subtree of [t] *)
let sum = function
    | Null -> 0
    | Node t -> t.sum

(* constructs treap when given proper parameters                    *)
(* init. cond: x <= y; (intervals of l) < (x, y) < (intervals of r) *)
(* key is not bigger than keys of [l] and [r] (if they exist)       *)
let node l r (x, y) key =
    Node { l = l; r = r; interval = (x, y); key = key; sum = y - x + 1 + (sum l) + (sum r) }

(* return interval set containg all intervals from [l] and [r] *)
(* init. cond: (intervals of t1) < (intervals of t2)           *)
let rec merge t1 t2 =
    match t1, t2 with
    | Null, t | t, Null -> t
    | Node t1, Node t2 ->
        let key1 = t1.key in
        let key2 = t2.key in
        if key1 < key2 then
            node t1.l (merge t1.r (Node t2)) t1.interval key1
        else
            node (merge (Node t1) t2.l) t2.r t2.interval key2

(* given predicate [pred], returns (set of intervals fulfilling [pred], set of rest of intervals) *)
(* init. cond: ((pred interval1) && (interval1 < interval2)) implies (pred interval2)             *)
let halve pred t =
    let rec loop = function
        | Null -> Null, Null
        | Node t ->
            if pred t.interval then
                let tmp1, tmp2 = loop t.l in
                tmp1, node tmp2 t.r t.interval t.key
            else
                let tmp1, tmp2 = loop t.r in
                node t.l tmp1 t.interval t.key, tmp2 in
    loop t

(* given interval (x, y) divides t into three sets. first one contains intervals strictly *)
(* smaller third one contins those strictly bigger and second one containing the rest     *)
(* init. cond: x <= y                                                                     *)
let divide (x, y) t =
    let tmp_pred (tx, ty) = (x = min_int) || (ty >= x - 1) in
    let l, tmp_right = halve tmp_pred t in
    let tmp_pred (tx, ty) = not ((y = max_int) || (tx <= y + 1)) in
    let m, r = halve tmp_pred tmp_right in
    l, m, r

(* returns first number in interval set, max_int if set is empty *)
let rec first = function
    | Null -> max_int
    | Node t -> min (fst t.interval) (first t.l)

(* returns last number in interval set, min_int if set is empty *)
let rec last = function
    | Null -> min_int
    | Node t -> max (snd t.interval) (last t.r)

(* returns [t] with added interval (x, y) init. cond: x <= y *)
let add (x, y) t =
    let l, m, r = divide (x, y) t in
    let new_m = create_leaf (min (first m) x) (max (last m) y) in
    merge l (merge new_m r)

(* returns [t] with removed interval (x, y) init. cond: x <= y *)
let remove (x, y) t =
    let l, m, r = divide (x, y) t in
    let m1 =
        if x = min_int then Null
        else create_leaf (first m) (x - 1) in
    let m2 =
        if y = max_int then Null
        else create_leaf (y + 1) (last m) in
    merge (merge l m1) (merge m2 r)

(* returns [true] if [s] is in any interval of [t], [false] otherwise *)
let mem s t =
    let rec loop = function
        | Null -> false
        | Node t ->
            if (snd t.interval) < s then loop t.r else
            if (fst t.interval) > s then loop t.l else
            true in
    loop t

(* returns (interval set of values in [t] < [s], [mem s t], interval set of values in [t] > [s] *)
let split s t =
    let (x, y) = (s, s) in
    let l, m, r = divide (x, y) t in
    let m1 =
        if x = min_int then Null
        else create_leaf (first m) (x - 1) in
    let m2 =
        if y = max_int then Null
        else create_leaf (y + 1) (last m) in
    merge l m1, mem s m, merge m2 r

(* returns number of elements smaller than [s] in [t] or max_int if number is too big *)
let below s t =
    let tmp_pred (x, y) = x > s in
    let l, _ = halve tmp_pred t in (* KUUUUUUUUUUUUUUUUUUUUUUUUUUUUUURWA *)
    (* number of numbers not bigger than [s] is non-negative                          *)
    (* [sum] is an integer and overflows so numbers smaller than 0                    *)
    (* represent numbers bigger than max_int, with exception of zero                  *)
    (* zero can be achieved in two ways: all or none of possible integers are smaller *)
    if l = empty then 0 else
    let y = last l in
    let tmp = if s < y then (sum l) - (y - s) else sum l in
    if tmp <= 0 then max_int else tmp

(* [fold f t a] computes [(f xN ... (f x2 (f x1 a))...)],    *)
(* where x1 xN are all intervals of [t], in increasing order *)
let fold f t a =
    let rec loop a = function
        | Null -> a
        | Node t -> loop (f t.interval (loop a t.l)) t.r in
    loop a t

(* iterates f on all intervals from [t] in increasing order *)
let iter f t =
    let tmp_f interval () = f interval in
    fold tmp_f t ()

(* returns list of all intervals from [t] in increasing order *)
let elements t =
    let tmp_f interval lst = interval :: lst in
    fold tmp_f t [] |> List.rev
