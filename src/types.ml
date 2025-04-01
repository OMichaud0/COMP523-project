type sort =
    | Nat
    | Bool
    | Pair of typ * typ
    | Var of string
    | Mu of string * sort
and typ =
    | Send of sort * typ (* /\ *)
    | Reception of sort * typ (* \/ *)
    | Throw of sort * typ (* /\ *)
    | Catch of sort * typ (* \/ *)
    | Branch of ((string * typ) list) (* & *)
    | Select of ((string * typ) list) (* \oplus*)
    | Inact (* 1 *)
    | Var of string (* t *)
    | Mu of string * typ (* \mu t.\alpha *)
    | Closed (* \perp *)

let compare_type a b = true (* TODO: add comparison*)

let rec cotype (alpha : typ) (a_bar : typ) : bool = match alpha,a_bar with
    | Send (s1,t1), Reception (s2,t2) -> cotype t1 t2
    | Reception (s1,t1), Send (s2,t2) -> cotype t1 t2
    | Branch l1, Select l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Select l1, Branch l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Throw (a1,b1), Catch (a2,b2) -> (compare_type a1 a2) && (cotype b1 b2) (* TODO: add comparison*)
    | Catch (a1,b1), Throw (a2,b2) -> (compare_type a1 a2) && (cotype b1 b2) (* TODO: add comparison*)
    | Inact, Inact -> true
    | Var s1, Var s2 -> (compare s1 s2) == 0
    | Mu (s1,t1), Mu (s2,t2) -> ((compare s1 s2) == 0) && (cotype t1 t2)
    | _, _ -> false

let rec compare_Sort (sort1 : sort) (sort2 : sort) : bool = match sort1,sort2 with
| Nat, Nat -> true
| Bool, Bool -> true
| _ -> false