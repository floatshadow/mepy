(** Sorting and merging for multisets and sets *)

type order =
  | Lt
  | Eq
  | Gt

let order_of_int = function
  | n when n < 0 -> Lt
  | 0 -> Eq
  | _ -> Gt
;;

module type SORT = sig
  val merge : ('a -> 'a -> order) -> 'a list -> 'a list -> 'a list
  val sort : ('a -> 'a -> order) -> 'a list -> 'a list
end

(** Multiset sort: keeps duplicates *)
module SortMultiset : SORT = struct
  let rec merge cmp xs ys =
    match xs, ys with
    | [], ys -> ys
    | xs, [] -> xs
    | x :: xs', y :: ys' ->
      (match cmp x y with
       | Lt -> x :: merge cmp xs' ys
       | Eq -> x :: merge cmp xs' ys (* x first for stability *)
       | Gt -> y :: merge cmp xs ys')
  ;;

  let rec merge_adjacents cmp = function
    | [] -> []
    | [ xs ] -> [ xs ]
    | xs1 :: xs2 :: xss -> merge cmp xs1 xs2 :: merge_adjacents cmp xss
  ;;

  let rec sortlists cmp = function
    | [] -> []
    | [ xs ] -> xs
    | xss -> sortlists cmp (merge_adjacents cmp xss)
  ;;

  let sort cmp xs = sortlists cmp (List.map (fun x -> [ x ]) xs)
end

(** Set sort: removes duplicates *)
module SortSet : SORT = struct
  let rec merge cmp xs ys =
    match xs, ys with
    | [], ys -> ys
    | xs, [] -> xs
    | x :: xs', y :: ys' ->
      (match cmp x y with
       | Lt -> x :: merge cmp xs' ys
       | Eq -> merge cmp xs ys' (* drop duplicate y *)
       | Gt -> y :: merge cmp xs ys')
  ;;

  let rec merge_adjacents cmp = function
    | [] -> []
    | [ xs ] -> [ xs ]
    | xs1 :: xs2 :: xss -> merge cmp xs1 xs2 :: merge_adjacents cmp xss
  ;;

  let rec sortlists cmp = function
    | [] -> []
    | [ xs ] -> xs
    | xss -> sortlists cmp (merge_adjacents cmp xss)
  ;;

  let sort cmp xs = sortlists cmp (List.map (fun x -> [ x ]) xs)
end
