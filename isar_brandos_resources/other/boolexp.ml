module Boolexp : sig
  type 'a boolexp
  val push_not : 'a boolexp -> 'a boolexp
  val boolexp_eval : ('a -> bool) -> 'a boolexp -> bool
  val remove_implies : 'a boolexp -> 'a boolexp
end = struct

type 'a boolexp = TRUE | FALSE | Var of 'a | Not of 'a boolexp |
  And of 'a boolexp * 'a boolexp | Or of 'a boolexp * 'a boolexp |
  Implies of 'a boolexp * 'a boolexp;;

let rec push_not
  = function TRUE -> TRUE
    | FALSE -> FALSE
    | Var x -> Var x
    | Not TRUE -> FALSE
    | Not FALSE -> TRUE
    | Not (Var x) -> Not (Var x)
    | Not (Not a) -> push_not a
    | Not (And (a, b)) -> Or (push_not (Not a), push_not (Not b))
    | Not (Or (a, b)) -> And (push_not (Not a), push_not (Not b))
    | Not (Implies (a, b)) -> And (push_not a, push_not (Not b))
    | And (a, b) -> And (push_not a, push_not b)
    | Or (a, b) -> Or (push_not a, push_not b)
    | Implies (a, b) -> Implies (push_not a, push_not b);;

let rec boolexp_eval
  env x1 = match env, x1 with env, TRUE -> true
    | env, FALSE -> false
    | env, Var x -> env x
    | env, Not b -> not (boolexp_eval env b)
    | env, And (a, b) -> boolexp_eval env a && boolexp_eval env b
    | env, Or (a, b) -> boolexp_eval env a || boolexp_eval env b
    | env, Implies (a, b) -> not (boolexp_eval env a) || boolexp_eval env b;;

let rec remove_implies
  = function TRUE -> TRUE
    | FALSE -> FALSE
    | Var x -> Var x
    | Not a -> Not (remove_implies a)
    | And (a, b) -> And (remove_implies a, remove_implies b)
    | Or (a, b) -> Or (remove_implies a, remove_implies b)
    | Implies (a, b) -> Or (Not (remove_implies a), remove_implies b);;

end;; (*struct Boolexp*)
