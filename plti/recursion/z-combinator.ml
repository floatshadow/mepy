type 't div = Div of ('t div -> 't)

(* λ x:DivT. unfold [DivT] x x)
  (fold [DivT] (λ x:DivT. unfold [DivT] x x)
let (omaga : 't) =
  (fun (x : 't div) -> match x with 
    | Div x' -> x' x
  )
  (Div (fun (x : 't div) -> 
    match x with 
    | Div x' -> x' x
  ))
 *)

(* λ f:T → T.
  (λ x:DivT. f (unfold [DivT] x x)) 
  (fold [DivT] (λ x:DivT. f (unfold [DivT] x x)))
 *)
let (y_combinator : ('t -> 't) -> 't) =
  fun (f : 't -> 't) ->
  (fun (x : 't div) -> 
    match x with 
    | Div x' -> f (x' x)
  )
  (Div (fun (x : 't div) -> 
    match x with 
    | Div x' -> f (x' x)
  ))

(* Y f --> f (Y f) (beta reduction)
  However, in a strict language such as OCaml, Y-combinator leads to infinite loop:
      (λf.(λx.f (x x)) (λx.f (x x))) g x1 x2 ...
  --> (λx.g (x x)) (λx.g (x x)) x1 x2 ...
  --> g (λx.g (x x)) (λx.g (x x)) x1 x2 ...
  Thus, it works differently with fixed point operator.

  To solve this problem, we use Z-combinator instead of Y-combinator:
  λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
  or with explicit `fold` and `unfold`:
  let T = μX. X -> (A -> B)
  Z : ((A -> B) -> (A → B)) -> (A -> B)
  Z = λf: (A -> B) -> (A -> B). 
    (λx : T. f (λy : A. (unfold[T] x) x y)) 
    (fold[T] (λx : T. f (λy : A. (unfold[T] x) x y)))

 *)
let (z_combinator : (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)) =
  fun (f : ('a -> 'b) -> ('a -> 'b)) ->
    (fun (x : ('a -> 'b) div) -> 
      f (fun (y : 'a) -> 
      match x with 
      | Div x' -> x' x y
    ))
    (Div (fun (x : ('a -> 'b) div) -> 
      f (fun (y : 'a) ->
      match x with 
      | Div x' -> (x' x y)
    )))

(* define 3 recursive functions with Z-combinator *)
let factorial_aux (f : int -> int) (n : int) : int =
  if n = 0 then 1 else n * f (n - 1)
let factorial : int -> int = z_combinator factorial_aux

let fibonacci_aux (f : int -> int) (n : int) : int =
  if n = 0 then 0 else if n = 1 then 1 else f (n - 1) + f (n - 2)
let fibonacci : int -> int = z_combinator fibonacci_aux

let list_length_aux (f : 'a list -> int) (l : 'a list) : int =
  match l with
  | [] -> 0
  | _::t -> 1 + f t
let list_length : 'a list -> int = z_combinator list_length_aux

(* test *)
let () =
  let n = 10 in
  Printf.printf "Factorial of %d is %d\n" n (factorial n);
  Printf.printf "Fibonacci of %d is %d\n" n (fibonacci n);
  let lst = [1; 2; 3; 4; 5; 6; 7; 8] in
  Printf.printf "Length of list [1; 2; 3; 4; 5; 6; 7; 8] is %d\n" (list_length lst)