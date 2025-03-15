signature SORT =
sig
    val merge : ('a -> 'a -> order) -> 'a list -> 'a list -> 'a list
    val sort :  ('a -> 'a -> order) -> 'a list -> 'a list
end

structure SortMultiset :> SORT =
struct

fun merge cmp nil ys = ys
  | merge cmp xs nil = xs
  | merge cmp (x::xs) (y::ys) =
    (case cmp x y
      of LESS => x::merge cmp xs (y::ys)
       | EQUAL => x::merge cmp xs (y::ys) (* x first, to make sort stable *)
       | GREATER => y::merge cmp (x::xs) ys)

fun merge_adjacents cmp nil = nil
  | merge_adjacents cmp (xs::nil) = xs::nil
  | merge_adjacents cmp (xs1::xs2::xss) =
    merge cmp xs1 xs2 :: merge_adjacents cmp xss

fun sortlists cmp nil = nil
  | sortlists cmp (xs::nil) = xs
  | sortlists cmp xss = sortlists cmp (merge_adjacents cmp xss)

fun sort cmp xs = sortlists cmp (List.map (fn x => [x]) xs)

end

structure SortSet :> SORT =
struct

fun merge cmp nil ys = ys
  | merge cmp xs nil = xs
  | merge cmp (x::xs) (y::ys) =
    (case cmp x y
      of LESS => x::merge cmp xs (y::ys)
       | EQUAL => merge cmp (x::xs) ys (* keep x (first), drop duplicate y *)
       | GREATER => y::merge cmp (x::xs) ys)

fun merge_adjacents cmp nil = nil
  | merge_adjacents cmp (xs::nil) = xs::nil
  | merge_adjacents cmp (xs1::xs2::xss) =
    merge cmp xs1 xs2 :: merge_adjacents cmp xss

fun sortlists cmp nil = nil
  | sortlists cmp (xs::nil) = xs
  | sortlists cmp xss = sortlists cmp (merge_adjacents cmp xss)

fun sort cmp xs = sortlists cmp (List.map (fn x => [x]) xs)

end
