(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz, Antoni Żewierżejew
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

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

module Rand : (sig val get : unit -> int end) =
    struct 
        let int64_of_max_int = Int64.of_int max_int
        let get () = Int64.to_int (Random.int64 int64_of_max_int)
    end

type node = { l: tree; r: tree; interval: int * int; key: int; sum: int }
and tree = Null | Node of node

type t = tree

let empty = Null

let is_empty t = (t = empty)

let create_leaf x y =
    if x > y then Null else
    Node { l = Null; r = Null; interval = (x, y); key = Rand.get (); sum = y - x + 1 }

let sum = function
    | Null -> 0
    | Node t -> t.sum

let node l r (x, y) key = 
    Node { l = l; r = r; interval = (x, y); key = Rand.get (); sum = y - x + 1 + (sum l) + (sum r) }

let rec merge t1 t2 =
    match t1, t2 with
    | Null, t | t, Null -> t
    | Node t1, Node t2 -> 
        let key1 = t1.key in
        let key2 = t2.key in
        if key1 < key2 then 
            node t1.l (merge t1.r (Node t2)) t1.interval t1.key
        else
            node (merge (Node t1) t2.l) t2.r t2.interval t2.key

let split pred t = 
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

let divide (x, y) t = 
    let tmp_pred (tx, ty) = (x = min_int) || (ty >= x - 1) in
    let l, tmp_right = split tmp_pred t in
    let tmp_pred (tx, ty) = not ((y = max_int) || (tx <= x + 1)) in
    let m, r = split tmp_pred tmp_right in
    l, m, r

let rec first = function
    | Null -> max_int
    | Node t -> min (fst t.interval) (first t.l)

let rec last = function
    | Null -> min_int
    | Node t -> max (snd t.interval) (last t.l)

let add (x, y) t = 
    let l, m, r = divide (x, y) t in
    let m = create_leaf (min (first m) x) (max (last m) y) in
    merge l (merge m r)

let remove (x, y) t = 
    let l, m, r = divide (x, y) t in
    let m1 = 
        if x = min_int then Null
        else create_leaf (first m) (x - 1) in 
    let m2 = 
        if y = max_int then Null
        else create_leaf (y + 1) (last m) in
    merge (merge l m1) (merge m2 r)

let mem s t = 
    let rec loop = function
        | Null -> false
        | Node t -> 
            if (snd t.interval) < s then loop t.l else
            if (fst t.interval) > s then loop t.r else
            true in
    loop t

let below s t = 
    let l, m, _ = divide (s, s) t in
    let sum, is_real_zero =
        match l, m with
        | Null, Null -> 0, true
        | t, Null -> sum t, false
        | _, Node t -> s - (fst t.interval) + 1 + (sum l), false in
    if is_real_zero then 0 else
    if sum <= 0 then max_int else
    sum
        
let fold f a t =
    let rec loop a = function
        | Null -> a
        | Node t -> loop (f t.interval (loop a t.l)) t.r in
    loop a t

let iter f t =
    let tmp_f interval () = f interval in 
    fold tmp_f () t