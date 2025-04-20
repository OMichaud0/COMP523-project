#use "terms.ml"

type sort =
    | Nat_s
    | Bool_s
    | Pair_s of typ * typ
    | Var_s of string
and typ =
    | Send_t of sort * typ (* /\ *)
    | Reception_t of sort * typ (* \/ *)
    | Branch_t of ((label * typ) list) (* & *)
    | Select_t of ((label * typ) list) (* \oplus*)
    | Inact_t (* 1 *)
    | Closed_t (* \perp *)
    | Unknown_t (* this is strictly used to generate the sessions *)

let rec cotype (alpha : typ) (a_bar : typ) : bool = match alpha,a_bar with
    | Send_t (s1,t1), Reception_t (s2,t2) -> cotype t1 t2
    | Reception_t (s1,t1), Send_t (s2,t2) -> cotype t1 t2
    | Branch_t l1, Select_t l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Select_t l1, Branch_t l2 -> List.fold_left (fun x y -> x && y) true (List.map2 (fun (l1,t1) (l2,t2) -> ((compare l1 l2) == 0) && (cotype t1 t2)) l1 l2)
    | Inact_t, Inact_t -> true
    | _, _ -> false

let rec compare_Sort (sort1 : sort) (sort2 : sort) : bool = match sort1,sort2 with
| Nat_s, Nat_s -> true
| Bool_s, Bool_s -> true
| _ -> false

let rec typ_equal (type1 : typ) (type2 : typ) : bool =
    match type1, type2 with 
    | Send_t (s1,t1), Send_t (s2,t2) -> (sort_equal s1 s2) && (typ_equal t1 t2)
    | Reception_t (s1,t1), Reception_t (s2,t2) -> (sort_equal s1 s2) && (typ_equal t1 t2)
    | Branch_t l1, Branch_t l2 -> 
        begin
            match List.compare_lengths l1 l2 with
            | 0 -> 
                begin
                    let fold_fct = fun acc (l,lt1) -> 
                        match List.assoc_opt l l2 with
                        | Some lt2 -> acc && (typ_equal lt1 lt2)
                        | None -> false
                    in
                    List.fold_left fold_fct true l1
                end
            | _ -> false
        end
    | Select_t l1, Select_t l2 -> 
        begin
            match List.compare_lengths l1 l2 with
            | 0 -> 
                begin
                    let fold_fct = fun acc (l,lt1) -> 
                        match List.assoc_opt l l2 with
                        | Some lt2 -> acc && (typ_equal lt1 lt2)
                        | None -> false
                    in
                    List.fold_left fold_fct true l1
                end
            | _ -> false
          end
    | Inact_t, Inact_t -> true
    | Closed_t, Closed_t -> true
    | _, _ -> false
and sort_equal (sort1 : sort) (sort2 : sort) : bool =
    match sort1, sort2 with
    | Nat_s, Nat_s -> true
    | Bool_s, Bool_s -> true
    | Pair_s (t11,t12), Pair_s (t21,t22) -> (typ_equal t11 t21) && (typ_equal t12 t22)
    | Var_s x, Var_s y -> true 
    | _, _ -> false