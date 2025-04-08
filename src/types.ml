type sort =
    | Nat_s
    | Bool_s
    | Pair_s of typ * typ
    | Var_s of string
    | Mu_s of string * sort
and typ =
    | Send_t of sort * typ (* /\ *)
    | Reception_t of sort * typ (* \/ *)
    | Throw_t of typ * typ (* /\ *)
    | Catch_t of typ * typ (* \/ *)
    | Branch_t of ((string * typ) list) (* & *)
    | Select_t of ((string * typ) list) (* \oplus*)
    | Inact_t (* 1 *)
    | Var_t of string (* t *)
    | Mu_t of string * typ (* \mu t.\alpha *)
    | Closed_t (* \perp *)
    | Unkown_t (* this is strictly used to generate the sessions *)

let compare_type a b = true (* TODO: add comparison*)

let rec cotype (alpha : typ) (a_bar : typ) : bool = match alpha,a_bar with
    | Send_t (s1,t1), Reception_t (s2,t2) -> cotype t1 t2
    | Reception_t (s1,t1), Send_t (s2,t2) -> cotype t1 t2
    | Branch_t l1, Select_t l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Select_t l1, Branch_t l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Throw_t (a1,b1), Catch_t (a2,b2) -> (compare_type a1 a2) && (cotype b1 b2) (* TODO: add comparison*)
    | Catch_t (a1,b1), Throw_t (a2,b2) -> (compare_type a1 a2) && (cotype b1 b2) (* TODO: add comparison*)
    | Inact_t, Inact_t -> true
    | Var_t s1, Var_t s2 -> (compare s1 s2) == 0
    | Mu_t (s1,t1), Mu_t (s2,t2) -> ((compare s1 s2) == 0) && (cotype t1 t2)
    | _, _ -> false

let rec compare_Sort (sort1 : sort) (sort2 : sort) : bool = match sort1,sort2 with
| Nat_s, Nat_s -> true
| Bool_s, Bool_s -> true
| _ -> false

let rec typ_equal (type1 : typ) (type2 : typ) : bool =
    match type1, type2 with 
    | Send_t (s1,t1), Send_t (s2,t2) -> (sort_equal s1 s2) && (typ_equal t1 t2)
    | Reception_t (s1,t1), Reception_t (s2,t2) -> (sort_equal s1 s2) && (typ_equal t1 t2)
    | Throw_t (t11,t12), Throw_t (t21,t22) -> (typ_equal t11 t21) && (typ_equal t12 t22)
    | Catch_t (t11,t12), Catch_t (t21,t22) -> (typ_equal t11 t21) && (typ_equal t12 t22)
    | Branch_t l1, Branch_t l2 -> true (* TODO This just needs an implementation didn't have time to write it *)
    | Select_t l1, Select_t l2 -> true (* TODO This just needs an implementation didn't have time to write it *)
    | Inact_t, Inact_t -> true
    | Var_t x, Var_t y -> true (* TODO how to handle these? *)
    | Mu_t (x,t1), Mu_t (y,t2) -> typ_equal t1 t2
    | Closed_t, Closed_t -> true
    | _, _ -> false
and sort_equal (sort1 : sort) (sort2 : sort) : bool =
    match sort1, sort2 with
    | Nat_s, Nat_s -> true
    | Bool_s, Bool_s -> true
    | Pair_s (t11,t12), Pair_s (t21,t22) -> (typ_equal t11 t21) && (typ_equal t12 t22)
    | Var_s x, Var_s y -> true (* TODO might need some sort of environment to map variables with different names used correspondingly *)
    | Mu_s (x,s1), Mu_s (y,s2) -> sort_equal s1 s2
    | _, _ -> false