module Sat : sig
  type 'a equal
  type 'a boolexp
  type 'a bool_dnf
  val sat : 'a equal -> 'a boolexp -> (('a * bool) list) list
end = struct

let rec equal_boola p pa = match p, pa with p, true -> p
                      | p, false -> not p
                      | true, p -> p
                      | false, p -> not p;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec eq _A a b = equal _A a b;;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

type 'a boolexp = TRUE | FALSE | Var of 'a | Not of 'a boolexp |
  And of 'a boolexp * 'a boolexp | Or of 'a boolexp * 'a boolexp |
  Implies of 'a boolexp * 'a boolexp;;

type 'a bool_atom = TRUE_at | FALSE_at | Var_at of 'a | Not_Var_at of 'a;;

type 'a bool_conj = Atom of 'a bool_atom |
  And_conj of 'a bool_atom * 'a bool_conj;;

type 'a bool_dnf = Conj of 'a bool_conj | Or_dnf of 'a bool_conj * 'a bool_dnf;;

type 'a boolexp_nipn = TRUE_nipn | FALSE_nipn | Var_nipn of 'a |
  Not_Var_nipn of 'a | And_nipn of 'a boolexp_nipn * 'a boolexp_nipn |
  Or_nipn of 'a boolexp_nipn * 'a boolexp_nipn;;

let rec push_not_elim_imp
  = function TRUE -> TRUE_nipn
    | FALSE -> FALSE_nipn
    | Var x -> Var_nipn x
    | Not TRUE -> FALSE_nipn
    | Not FALSE -> TRUE_nipn
    | Not (Var x) -> Not_Var_nipn x
    | Not (Not b) -> push_not_elim_imp b
    | Not (And (a, b)) ->
        Or_nipn (push_not_elim_imp (Not a), push_not_elim_imp (Not b))
    | Not (Or (a, b)) ->
        And_nipn (push_not_elim_imp (Not a), push_not_elim_imp (Not b))
    | Not (Implies (a, b)) ->
        And_nipn (push_not_elim_imp a, push_not_elim_imp (Not b))
    | And (a, b) -> And_nipn (push_not_elim_imp a, push_not_elim_imp b)
    | Or (a, b) -> Or_nipn (push_not_elim_imp a, push_not_elim_imp b)
    | Implies (a, b) ->
        Or_nipn (push_not_elim_imp (Not a), push_not_elim_imp b);;

let rec conj_and x0 b = match x0, b with Atom a, b -> And_conj (a, b)
                   | And_conj (a, b), c -> And_conj (a, conj_and b c);;

let rec conj_or a x1 = match a, x1 with a, Conj b -> Conj (conj_and a b)
                  | a, Or_dnf (b, c) -> Or_dnf (conj_and a b, conj_or a c);;

let rec dnf_or x0 b = match x0, b with Conj a, b -> Or_dnf (a, b)
                 | Or_dnf (a, b), c -> Or_dnf (a, dnf_or b c);;

let rec dist_and_or
  x0 b = match x0, b with Conj a, b -> conj_or a b
    | Or_dnf (a, b), c -> dnf_or (conj_or a c) (dist_and_or b c);;

let rec basic_dnf
  = function TRUE_nipn -> Conj (Atom TRUE_at)
    | FALSE_nipn -> Conj (Atom FALSE_at)
    | Var_nipn x -> Conj (Atom (Var_at x))
    | Not_Var_nipn x -> Conj (Atom (Not_Var_at x))
    | And_nipn (a, b) -> dist_and_or (basic_dnf a) (basic_dnf b)
    | Or_nipn (a, b) -> dnf_or (basic_dnf a) (basic_dnf b);;

let rec dnf a = basic_dnf (push_not_elim_imp a);;

let rec sat_bool_atom = function TRUE_at -> Some None
                        | FALSE_at -> None
                        | Var_at x -> Some (Some (x, true))
                        | Not_Var_at x -> Some (Some (x, false));;

let rec member _A x xa1 = match x, xa1 with x, [] -> false
                    | x, y :: ys -> eq _A x y || member _A x ys;;

let rec sat_conj _A
  = function
    Atom a ->
      (match sat_bool_atom a with None -> None | Some None -> Some []
        | Some (Some (y, t)) -> Some [(y, t)])
    | And_conj (a, b) ->
        (match sat_bool_atom a with None -> None | Some None -> sat_conj _A b
          | Some (Some (y, t)) ->
            (match sat_conj _A b with None -> None
              | Some l ->
                (if member (equal_prod _A equal_bool) (y, not t) l then None
                  else (if member (equal_prod _A equal_bool) (y, t) l
                         then Some l else Some ((y, t) :: l)))));;

let rec sat_dnf _A
  = function Conj a -> (match sat_conj _A a with None -> [] | Some l -> [l])
    | Or_dnf (a, b) ->
        (match sat_conj _A a with None -> sat_dnf _A b
          | Some l -> l :: sat_dnf _A b);;

let rec sat _A a = sat_dnf _A (dnf a);;

end;; (*struct Sat*)
