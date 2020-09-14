theory sexpression_print
imports Pure
begin


ML \<open>
structure BoundStack =
struct
datatype boundstack = Entry of string * boundstack
                    | None;
exception BOUNDSTACK of string * int;

fun get None i  = raise BOUNDSTACK ("Not enough bounded variables", i)
  | get (Entry (s,_)) 0 = s
  | get (Entry (_,b)) i = if (i < 0) then raise BOUNDSTACK ("Negative boundstack index",i) else get b (i-1);

val empty:boundstack = None
end


fun print_sep sep xs = 
  case xs of
    [] => ""
  | [x] => x
  | x::ys => x ^ sep ^ print_sep sep ys

fun sort_to_sexpr (s: sort) = 
  print_sep " " s

(* 
sort = [<string>(, <string>)*] 
*)
(*
<type>
= (Type <string>)
| (Type <string> [<type>(, <type>)*])
| (TFree <string> <sort>)
| (TVar (<string>, <int>) <sort>) 
*)
fun typ_to_sexpr (t: typ) = 
  case t of
     Type (n, []) => "( " ^ n ^ ")"
   | Type (n, ts) => "( " ^ n ^ " [" ^ print_sep ", " (map typ_to_sexpr ts) ^ "])"
   | TFree (n, s) => "( " ^ n ^ " " ^ sort_to_sexpr s ^ ")"
   | TVar  (n, s) => "( " ^ @{make_string} n ^ " " ^ sort_to_sexpr s ^ ")"
(*
<term> 
= (Apply <term> <term>)
| (Const <string> <type>)
| (Free <string> <type>)
| (Var (<string>,<int>) <type>)
| (Bound <int>)
| (Abs <string> <type> <term>)
*)

fun to_sexpr_help (t:term) (b: BoundStack.boundstack) = 
  case t of
       f $ x => "(Apply " ^ to_sexpr_help f b ^ " " ^ to_sexpr_help x b ^ ")"
     | Const (n, _) => "(Const " ^ n  ^ ")"
     | Free (n, t) => "(Free " ^ n ^ ":: " ^ typ_to_sexpr t  ^ ")"
     | Var (n, t) => "(Var " ^  @{make_string} n ^ ":: " ^ typ_to_sexpr t  ^ ")"
     | Bound n => "(Bound " ^ (BoundStack.get b n) ^ ")"
     | Abs (n, t, e) => "(Abs " ^ n ^ ":: " ^ typ_to_sexpr t ^ " " ^ (to_sexpr_help e (BoundStack.Entry (n,b)))  ^  ")"

fun to_sexpr (t: term) = to_sexpr_help t BoundStack.empty


fun to_sexpr_untyped_help (t: term) (b: BoundStack.boundstack)= 
  case t of
       f $ x => "(Apply " ^ to_sexpr_untyped_help f b ^ " " ^ to_sexpr_untyped_help x b ^ ")"
     | Const (n, _) => "(Const " ^ n  ^ ")"
     | Free (n, _) => "(Free " ^ n  ^ ")"
     | Var (n, _) => "(Var " ^  @{make_string} n  ^ ")"
     | Bound n => "(Bound " ^ (BoundStack.get b n) ^ ")"
     | Abs (n, _, e) => "(Abs " ^ n ^ " " ^ (to_sexpr_untyped_help e (BoundStack.Entry (n,b)))  ^  ")"

fun to_sexpr_untyped (t: term) = to_sexpr_untyped_help t BoundStack.empty

\<close>

end
