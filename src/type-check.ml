#use "types.ml"
#use "terms.ml"

module ChannelSet = Set.Make(
  struct
    let compare = compare
    type t = channel
  end
)

module StringSet = Set.Make(
  struct
    let compare = compare
    type t = string
  end
)

type sorting = (string * sort) list (* \Gamma *) (* TODO: check if string is appropriate *)
type basis = (proc_var * ((sort list) * (typ list))) list (* \Theta *)(* TODO: check if list tuple is appropriate *)

type typing = (channel * typ) list (* \Delta *)

type scoped_process = 
  | Scoped_Request of name * channel * scoped_process
  | Scoped_Accept of name * channel * scoped_process
  | Scoped_Send of channel * expr * scoped_process
  | Scoped_Reception of channel * var * scoped_process
  | Scoped_Branch of channel * ((label * scoped_process) list)
  | Scoped_Selection of channel * label * scoped_process
  | Scoped_Throw of channel * channel * scoped_process
  | Scoped_Catch of channel * channel * scoped_process
  | Scoped_Conditional of expr * scoped_process * scoped_process
  | Scoped_Inact
  | Scoped_Hide of proc_var * scoped_process
  | Scoped_Rec of scoped_def_rec * scoped_process
  | Scoped_Proc_Var of proc_var * expr * channel
  | Scoped_Composition of sorting * scoped_process * scoped_process
and scoped_rec_atom = proc_var * var * channel * scoped_process
and scoped_def_rec = scoped_rec_atom list (* do we need to account for empty lists? *)

exception TypeError of string

let intersect (t1 : typing) (t2: typing) : channel list =
  let (d1,_) = List.split t1 in
  let (d2,_) = List.split t2 in
  let s1 = ChannelSet.of_list d1 in
  let s2 = ChannelSet.of_list d2 in
  ChannelSet.to_list (ChannelSet.inter s1 s2)

let different (t1 : typing) (t2 : typing) : channel list =
  let (d1,_) = List.split t1 in
  let (d2,_) = List.split t2 in
  let s1 = ChannelSet.of_list d1 in
  let s2 = ChannelSet.of_list d2 in
  ChannelSet.to_list (ChannelSet.diff s1 s2)

let is_compatible (t1 : typing) (t2 : typing) : bool =
  let intersection = intersect t1 t2 in
  let f = fun acc x -> acc && (cotype (List.assoc x t1) (List.assoc x t2)) in
  List.fold_left f true intersection

let compose (t1 : typing) (t2 : typing) : typing =
  let intersection = intersect t1 t2 in
  let d1 = different t1 t2 in
  let d2 = different t2 t1 in
  (List.map (fun c -> (c,Closed_t)) intersection) @ (List.map (fun k -> (k,List.assoc k t1)) d1) @ (List.map (fun k -> (k,List.assoc k t2)) d2)


let rec sort_check (gamma : sorting) (e : expr) : sort =
  match e with
    | Cst c -> (match c with
      | Int _ -> Nat_s
      | Bool _ -> Bool_s)
    | Var x -> match List.find_opt (fun (y,_) -> (compare x y == 0)) gamma with 
      | Some (_,s) -> s
      | _ -> raise (TypeError "error")

let rec type_check (theta : basis) (gamma : sorting) (input_process : process) : typing = match input_process with
(* REQ *)  | Request (a,k,p) ->
  begin
    match (List.find_opt (fun (s1,_) -> (compare s1 a) == 0) gamma) with
      | Some (a,a_type) -> 
        begin
          match a_type with 
            | Pair_s (alpha,alpha_bar) ->
              let delta = (type_check theta (List.filter (fun (s1,_) -> (compare s1 a) != 0) gamma) p) in
              let fil_f = fun (x,_) -> (compare x k != 0) in
              List.filter fil_f delta
            | _ -> raise (TypeError "error") 
        end
      | None -> raise (TypeError "error")
  end
(* ACC *)  | Accept (a,k,p) ->
  begin
    match (List.find_opt (fun (s1,_) -> (compare s1 a) == 0) gamma) with
      | Some (a,a_type) -> 
        begin
          match a_type with 
            | Pair_s (alpha,alpha_bar) ->
              let delta = (type_check theta (List.filter (fun (s1,_) -> (compare s1 a) != 0) gamma) p) in
              let fil_f = fun (x,_) -> (compare x k != 0) in
              List.filter fil_f delta
            | _ -> raise (TypeError "error") 
        end
      | _ -> raise (TypeError "error")
  end
(* SEND *) | Send (k,e,p) ->
  begin
    let e_s = sort_check gamma e in
    let delta_prime = type_check theta gamma p in
    let alpha = match List.assoc_opt k delta_prime with
    | Some a -> a
    | None -> Closed_t
    in
    (List.filter (fun (k_prime,_) -> (compare k k_prime) == 0) delta_prime) @ [(k,Send_t(e_s,alpha))]
  end
(* RCV *) | Reception (k,x,p) -> (* TODO: *)
  begin
    let sort_x : sort = Var_s x in
    let gamma_prime = gamma @ [(x,sort_x)] in
    let delta_prime = type_check theta gamma_prime p in
    let alpha = match List.assoc_opt k delta_prime with
    | Some a -> a
    | None -> Closed_t
    in
    (List.filter (fun (k_prime,_) -> (compare k k_prime) == 0) delta_prime) @ [(k,Reception_t(sort_x,alpha))]
  end
(* CONC *) | Composition (p,q) ->
    let deltap = type_check theta gamma p in
    let deltaq = type_check theta gamma q in
    if is_compatible deltap deltaq then compose deltap deltaq else raise (TypeError "error")
  | _ -> raise (TypeError "error")

  (* (match type_check theta gamma with ->


  | typing t -> List.filter (fun (chan,cotyp) -> (compare chan k) == 0) t
  | _ -> raise (TypeError "error"))
  | 
  )*)

let expr_sort (e : expr) : sort =
  match e with
    | Cst Int _ -> Nat_s
    | Cst Bool _ -> Bool_s
    | Var x -> Var_s x

let combine_sortings (s1 : sorting) (s2 : sorting) : sorting =
  let fct = (fun snd_sorting acc (a,s) -> acc || List.mem_assoc a snd_sorting) in
  match (List.fold_left (fct s2) false s1, List.fold_left (fct s1) false s2) with 
  | false, false -> s1 @ s2
  | _, _ -> raise (TypeError "error") (* Both sorting contain a common name so a name was used to create more than one session *)

let construct_pair_s (s1 : sort) (s2 : sort) : sort =
  match s1, s2 with
  | Pair_s (accept,Unknown_t), Pair_s (Unknown_t,request) -> Pair_s(accept,request)
  | Pair_s (Unknown_t,request), Pair_s (accept,Unknown_t) -> Pair_s(accept,request)
  | _, _ -> raise (TypeError "error")

let compose_sortings (s1 : sorting) (s2 : sorting) : sorting * sorting =
  let (d1,_) = List.split s1 in
  let (d2,_) = List.split s2 in
  let names1 = StringSet.of_list d1 in
  let names2 = StringSet.of_list d2 in
  let single1 = StringSet.diff names1 names2 in
  let single2 = StringSet.diff names2 names1 in
  let common = StringSet.inter names1 names2 in
  (List.map (fun a -> (a,List.assoc a s1)) (StringSet.to_list single1)) 
  @ (List.map (fun a -> (a,List.assoc a s2)) (StringSet.to_list single2)), 
  (List.map (fun a -> (a,construct_pair_s (List.assoc a s1) (List.assoc a s2))) (StringSet.to_list common)) 

let compose_typings (t1 : typing) (t2 : typing) : typing =
  let (d1,_) = List.split t1 in
  let (d2,_) = List.split t2 in
  let names1 = StringSet.of_list d1 in
  let names2 = StringSet.of_list d2 in
  let common = StringSet.inter names1 names2 in
  match StringSet.cardinal common with
  | 0 -> t1 @ t2
  | _ -> raise (TypeError "error") (* a channel is used in both sortings *)

let extend_name (label : string) (name : string) : string = String.concat "_" [label;name]

let rec combine_types_for_branching (t1 : typ) (t2 : typ) : typ =
  match t1, t2 with
  | Select_t l_t1, Select_t l_t2 -> 
    begin
      match (List.fold_left (fun acc (l,_) -> acc || (List.mem_assoc l l_t2)) false l_t1) with
      | true -> raise (TypeError "cannot combine selects with overlapping labels")
      | false -> Select_t (l_t1 @ l_t2)
    end
  | Send_t (s1,sub_t1), Send_t (s2,sub_t2) -> Send_t (s1,(combine_types_for_branching sub_t1 sub_t2)) (* TODO might need to check both sorts are the same. *)
  | Reception_t (s1,sub_t1), Reception_t (s2,sub_t2) -> Reception_t (s1,(combine_types_for_branching sub_t1 sub_t2)) (* TODO might need to check both sorts are the same. *)
  | _,_ -> raise (TypeError "incompatible type combination") (* TODO might need more cases in the future *)

let rec conditional_type_equal (t1 : typ) (t2 : typ) : bool = 
  match t1, t2 with 
  | Send_t (s1,t1), Send_t (s2,t2) -> (conditional_sort_equal s1 s2) && (conditional_type_equal t1 t2)
  | Reception_t (s1,t1), Reception_t (s2,t2) -> (conditional_sort_equal s1 s2) && (conditional_type_equal t1 t2)
  | Branch_t l1, Branch_t l2 -> 
    begin
      match List.compare_lengths l1 l2 with
      | 0 -> 
        begin
          let fold_fct = fun acc (l,lt1) -> 
            match List.assoc_opt l l2 with
            | Some lt2 -> acc && (conditional_type_equal lt1 lt2)
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
            | Some lt2 -> acc && (conditional_type_equal lt1 lt2)
            | None -> false
          in
          List.fold_left fold_fct true l1
        end
      | _ -> false
    end
  | Inact_t, Inact_t -> true
  | Closed_t, Closed_t -> true
  | _, _ -> false
and conditional_sort_equal (s1 : sort) (s2 : sort) : bool =
  match s1, s2 with
  | Nat_s, Nat_s -> true
  | Bool_s, Bool_s -> true
  | Var_s x, Var_s y -> true (* TODO might need some sort of environment to map variables with different names used correspondingly *)
  | _, _ -> false

let conditional_typing_equal (tp1 : typing) (tp2 : typing) : bool =
  let fold_fct = fun acc (k,t1) ->
    match List.assoc_opt k tp2 with
    | Some t2 -> acc && (conditional_type_equal t1 t2)
    | None -> false
  in
  match List.compare_lengths tp1 tp2 with 
  | 0 -> List.fold_left fold_fct true tp1
  | _ -> false

let conditional_sorting_equal (sr1 : sorting) (sr2 : sorting) : bool =
  let fold_fct = fun acc (a,t1) ->
    match t1, List.assoc_opt a sr2 with
    | Pair_s (accept1,Unknown_t), Some Pair_s (accept2,Unknown_t) -> acc && (conditional_type_equal accept1 accept2)
    | Pair_s (Unknown_t,request1), Some Pair_s (Unknown_t,request2) -> acc && (conditional_type_equal request1 request2)
    | _, _ -> false
  in
  match List.compare_lengths sr1 sr2 with 
  | 0 -> List.fold_left fold_fct true sr2
  | _ -> false

let rec gen_sortings (input_process : process) : scoped_process * sorting * typing =
  match input_process with 
  | Request (a, k, p) -> 
    begin
      let new_p, s, t = gen_sortings p in
      match (List.assoc_opt a s, List.assoc_opt a t) with
      | None, None -> 
        begin
          match List.assoc_opt k t with
          | Some k_type -> (Scoped_Request (a, k, new_p), [(a, Pair_s(Unknown_t,k_type))] @ s, (List.remove_assoc k t))
          | None -> (Scoped_Request (a, k, new_p), [(a, Pair_s(Unknown_t,Inact_t))] @ s, t) (* Is Inact_t appropriate as the end of the type? *)
        end
      | _, _ -> raise (TypeError "error") (* The name a was used for another session or as a channel. *)
    end
  | Accept (a, k, p) -> 
    begin
      let new_p, s, t = gen_sortings p in
      match (List.assoc_opt a s, List.assoc_opt a t) with
      | None, None -> 
        begin
          match List.assoc_opt k t with
          | Some k_type -> (Scoped_Accept (a, k, new_p), [(a, Pair_s(k_type,Unknown_t))] @ s, (List.remove_assoc k t))
          | None -> (Scoped_Accept (a, k, new_p), [(a, Pair_s(Inact_t,Unknown_t))] @ s, t) (* Is Inact_t appropriate as the end of the type? *)
        end
      | _, _ -> raise (TypeError "error") (* The name a was used for another session or as a channel. *)
    end
  | Send (k, e, p) ->
    begin
      let e_sort = expr_sort e in
      let new_p, s, t = gen_sortings p in 
      match List.assoc_opt k t with 
      | Some k_type -> (Scoped_Send (k, e, new_p), s, (List.remove_assoc k t) @ [(k, Send_t (e_sort, k_type))])
      | None -> (Scoped_Send (k, e, new_p), s, t @ [(k, Send_t (e_sort, Inact_t))]) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Reception (k, v, p) -> 
    begin
      let new_p, s, t = gen_sortings(p) in 
      match List.assoc_opt k t with 
      | Some k_type -> (Scoped_Reception (k, v, new_p), s, (List.remove_assoc k t) @ [(k, Reception_t (Var_s v, k_type))])
      | None -> (Scoped_Reception (k, v, new_p), s, t @ [(k, Reception_t (Var_s v, Inact_t))]) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Branch (k, labels_proc) -> 
    (* (* TODO Fix propagation of empty branch. If (label,process) does not contain operations on k, 
    should add to branching with Inact/Closed so it can match with the selection of this branch.*)
    begin
      let fold_fct = fun ((procs,s,t) : (((label * scoped_process) list) * sorting * typing)) (l, p) -> 
        begin
          let new_p, s_prime, t_prime = gen_sortings p in
          let sorting_extend_fct = fun (a,a_sorting) -> 
            begin
              match List.assoc_opt a s with
              | Some a_s ->
                begin 
                  match a_s, a_sorting with
                  | Pair_s (accept1, Unknown_t), Pair_s (accept2, Unknown_t) ->
                    begin
                      match accept1 with 
                      | Branch_t accept_labels -> 
                        begin
                          match List.assoc_opt l accept_labels with
                          | Some _ -> raise (TypeError "error") (* Label is already in branching *)
                          | None -> (a, Pair_s (Branch_t (accept_labels @ [(l, accept2)]), Unknown_t))
                        end
                      | _ -> raise (TypeError "error") (* Should not be possible, the None case below creates the initial branching. *)
                    end
                  | Pair_s (Unknown_t, request1), Pair_s (Unknown_t, request2) ->
                    begin
                      match request1 with 
                      | Branch_t request_labels -> 
                        begin
                          match List.assoc_opt l request_labels with
                          | Some _ -> raise (TypeError "error") (* Label is already in branching *)
                          | None -> (a, Pair_s (Unknown_t, Branch_t (request_labels @ [(l, request2)])))
                        end
                      | _ -> raise (TypeError "error") (* Should not be possible, the None case below creates the initial branching. *)
                    end
                  | _, _ -> raise (TypeError "error") (* Should not get anything but pairs. *)
                end
              | None -> 
                begin 
                  match a_sorting with
                  | Pair_s (accept, Unknown_t) -> (a, Pair_s (Branch_t [(l, accept)], Unknown_t))
                  | Pair_s (Unknown_t, request) -> (a, Pair_s (Unknown_t, Branch_t [(l, request)]))
                  | Pair_s (accept, request) -> (extend_name l a,a_sorting) (* TODO This should not be possible anymore with the scoped compositions, need to simplify this later. *)
                  | _ -> raise (TypeError "error") (* Should not get anything but pairs. *)
                end
            end
          in
          let intermediate_s = List.map sorting_extend_fct s_prime in
          let new_s = intermediate_s @ (List.filter (fun (a,_) -> not (List.mem_assoc a intermediate_s)) s) in
          let type_extend_fct = fun (k,k_type) -> 
            begin
              match List.assoc_opt k t with
              | Some (k_t) ->
                begin
                  match k_t with
                  | Branch_t k_labels -> 
                    begin
                      match List.assoc_opt l k_labels with
                      | Some _ -> raise (TypeError "error") (* The label was already in the branching*)
                      | None -> (k, Branch_t ([(l,k_type)] @ k_labels))
                    end
                  | _ -> raise (TypeError "error") (* The channel k does not have type Branch_t so label cannot be added*)
                end
              | None -> (k, Branch_t [(l, k_type)])
            end
          in
          let intermediate_t = List.map type_extend_fct t_prime in
          let new_t = intermediate_t @ (List.filter (fun (k,_) -> not (List.mem_assoc k intermediate_t)) t)
          in ([(l, new_p)] @ procs, new_s, new_t)
        end
        (* (let s, t = gen_sortings p in (combine_sortings acc s), (l,t)) in *)
      in
      let (acc : (((label * scoped_process) list) * sorting * typing)) = ([],[],[]) in
      let new_procs, s, labels_typ = List.fold_left fold_fct acc labels_proc in
      (Scoped_Branch (k, new_procs), s, labels_typ)
    end *)
    begin
      let map_gen_sortings = fun (l,l_proc) ->
        begin
          let new_p, new_s, new_t = gen_sortings l_proc in
          let new_t = match List.assoc_opt k new_t with
            | Some k_type -> new_t
            | None -> [(k,Inact_t)] @ new_t
          in
          (l, new_p, new_s, new_t)
        end
      in
      let generated = List.map map_gen_sortings labels_proc in
      let new_labels_procs = List.map (fun (l,new_p,_,_) -> (l,new_p)) generated in
      let combined_sortings = List.fold_left (fun acc (l,_,new_s,_) -> 
        List.fold_left (fun acc2 (name,n_sort) -> 
          let new_pair = match List.assoc_opt name acc2, n_sort with
            | Some (Pair_s (accept1,Unknown_t)), Pair_s (accept2,Unknown_t) -> Pair_s ((combine_types_for_branching accept1 accept2),Unknown_t)
            | Some (Pair_s (Unknown_t,request1)), Pair_s (Unknown_t,request2) -> Pair_s (Unknown_t,(combine_types_for_branching request1 request2))
            | None, Pair_s (accept,Unknown_t) -> n_sort
            | None, Pair_s (Unknown_t,request) -> n_sort
            | _,_ -> raise (TypeError "incompatible sortings in branching during sorting generation")
          in 
          [(name,new_pair)] @ (List.remove_assoc name acc2)
        ) acc new_s
      ) [] generated in 
      (* let combined_types = List.fold_left (fun acc (l,_,_,new_t) ->
        List.fold_left (fun acc2 (k_prime,k_prime_type) ->
          let new_k_prime_type = match List.assoc_opt k_prime acc2 with
            | Some Branch_t (label_types) -> 
              begin 
                match List.mem_assoc l label_types with
                | true -> raise (TypeError "label is already in branching")
                | false -> Branch_t ([(l,k_prime_type)] @ label_types) 
              end
            | None -> Branch_t ([(l,k_prime_type)])
            | _ -> raise (TypeError "unexpected type found while combining labels")
          in
          [(k_prime,new_k_prime_type)] @ (List.remove_assoc k_prime acc2)
        ) acc new_t
      ) [] generated in *)
      let combined_types = List.fold_left (fun acc (l,_,_,new_t) ->
        List.fold_left (fun acc2 (k_prime,k_prime_type) ->
          let new_k_prime_type = if (compare k k_prime) == 0 then 
              match List.assoc_opt k_prime acc2 with
              | Some Branch_t (label_types) -> 
                begin 
                  match List.mem_assoc l label_types with
                  | true -> raise (TypeError "label is already in branching")
                  | false -> Branch_t ([(l,k_prime_type)] @ label_types) 
                end
              | None -> Branch_t ([(l,k_prime_type)])
              | _ -> raise (TypeError "unexpected type found while combining labels")
            else
              match List.assoc_opt k_prime acc2 with
              | Some k_p_t -> combine_types_for_branching k_p_t k_prime_type
              | None -> k_prime_type
          in
          [(k_prime,new_k_prime_type)] @ (List.remove_assoc k_prime acc2)
        ) acc new_t
      ) [] generated in
      Scoped_Branch (k, new_labels_procs), combined_sortings, combined_types
    end
  | Selection (k, l, p) -> 
    begin
      let new_p, s, t = gen_sortings p in
      match List.assoc_opt k t with
      | Some k_type -> (Scoped_Selection (k, l, new_p), s, [(k, Select_t [(l,k_type)])] @ (List.remove_assoc k t))
      | None -> (Scoped_Selection (k, l, new_p), s, [(k, Select_t [(l,Inact_t)])] @ t) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Throw (k1, k2, p) -> (Scoped_Inact, [], []) (* TODO *)
  | Catch (k1, k2, p) -> (Scoped_Inact, [], []) (* TODO *)
  | Conditional (e, then_p, else_p) -> 
    begin
      let new_then_p, then_s, then_t = gen_sortings then_p in
      let new_else_p, else_s, else_t = gen_sortings else_p in
      match (conditional_sorting_equal then_s else_s), (conditional_typing_equal then_t else_t) with
      | true, true -> Scoped_Conditional (e, new_then_p, new_else_p), then_s, then_t
      | _, _ -> raise (TypeError "the conditional statement has different types and sortings for both P and Q in \"if e then P else Q\"")
    end
  | Composition (p1, p2) ->
    begin
      let new_p1, s1, t1 = gen_sortings p1 in
      let new_p2, s2, t2 = gen_sortings p2 in
      let partial, complete = compose_sortings s1 s2 in
      (Scoped_Composition (complete, new_p1, new_p2), partial, compose_typings t1 t2)
    end
  | Inact -> (Scoped_Inact, [], [])
  | Hide (p_var, p) -> (Scoped_Inact, [], []) (* TODO *)
  | Rec (def, p) -> (Scoped_Inact, [], []) (* TODO *)
  | Proc_Var (p_var, e, k) -> (Scoped_Inact, [], []) (* TODO *)

let pop_type (k : channel) (types : typing) : typ * typing =
  let t = match List.assoc_opt k types with
    | Some k_type -> k_type
    | None -> raise (TypeError ("could not pop type, channel " ^ k ^ " not in typing"))
  in
  let types_prime = List.remove_assoc k types in
  let popped_type, subtype = match t with
    | Send_t (s, sub_t) -> Send_t (s, Inact_t), sub_t
    | Reception_t (s, sub_t) -> Reception_t (s, Inact_t), sub_t
    | Throw_t (t_prime, sub_t) -> Throw_t (t_prime, Inact_t), sub_t
    | Catch_t (t_prime, sub_t) -> Catch_t (t_prime, Inact_t), sub_t
    | _ -> raise (TypeError ("could not pop type, unexpected type found for channel " ^ k)) (* TODO Add Inact handling? *)
  in
  let new_typing = [(k, subtype)] @ types_prime in
  (popped_type, new_typing)

let replace_type (k : channel) (t : typ) (types : typing) : typing =
  [(k, t)] @ (List.remove_assoc k types) (* TODO check if k in typing otherwise we would add instead of replace *)

let propagate_from_cotype (t : typ) (co_t : typ) : bool * typ = 
  match t, co_t with
  | Reception_t (s1,t1), Send_t (Nat_s,t2) -> true, Reception_t (Nat_s,t1)
  | Reception_t (s1,t1), Send_t (Bool_s,t2) -> true, Reception_t (Bool_s,t2)
  | Reception_t (s1,t1), Send_t (Var_s (x),t2) -> false, t
  | Reception_t (s1,t1), Send_t (_,t2) -> raise (TypeError "propagate_from_cotype") (* I don't think this can happen. *)
  | Branch_t l1, Select_t l2 -> raise (TypeError "propagate_from_cotype") (* TODO rip *)
  | Catch_t (a1,b1), Throw_t (a2,b2) -> raise (TypeError "propagate_from_cotype") (* TODO: implement *)
  | _, _ -> raise (TypeError "propagate_from_cotype") (* TODO might need more cases later on *)

let pop_session (a : name) (s : sorting) : typ * typ * sorting =
  let a_sort = match List.assoc_opt a s with
    | Some a_s -> a_s
    | None -> raise (TypeError "pop_session session not in sorting")
  in
  let new_s = List.remove_assoc a s in
  match a_sort with
  | Pair_s (accept,request) -> accept, request, new_s
  | _ -> raise (TypeError "pop_session session is not a pair") 

let e_sort (s : sorting) (e : expr) : sort =
  match e with
  | Cst Int _ -> Nat_s
  | Cst Bool _ -> Bool_s
  | Var x -> 
    begin
      match List.assoc_opt x s with
      | Some Nat_s -> Nat_s
      | Some Bool_s -> Bool_s
      | Some Var_s y -> Var_s y
      | Some Pair_s (_,_) -> raise (TypeError "e_sort")
      | Some Mu_s (v,s_prime) -> Mu_s (v,s_prime)
      | None -> Var_s x
    end

let possible_selection (k : channel) (t : typing) = 
  match List.assoc_opt k t with
  | Some Select_t label_types -> List.map (fun (l,_) -> l) label_types
  | _ -> raise (TypeError "the cotype is not a selection")

let consume_branching (k : channel) (l : label) (t : typing) : typing = 
  let new_k_type = match List.assoc_opt k t with
    | Some Branch_t (label_types) -> 
      begin 
        match List.assoc_opt l label_types with
        | Some l_type -> l_type
        | None -> raise (TypeError "failed to consume branching, label not found")
      end
    | None -> raise (TypeError ("could not find type for channel " ^ k))
    | _ -> raise (TypeError "failed to consume branching, type was not a branch")
  in
  [(k,new_k_type)] @ (List.remove_assoc k t)

let consume_select (k : channel) (l : label) (t : typing) : typing =
  let new_k_type = match List.assoc_opt k t with
    | Some Select_t (label_types) -> 
      begin 
        match List.assoc_opt l label_types with
        | Some l_type -> l_type
        | None -> raise (TypeError "failed to consume selection, label not found")
      end
    | None -> raise (TypeError ("could not find type for channel " ^ k))
    | _ -> raise (TypeError "failed to consume selection, type was not a select")
  in
  [(k,new_k_type)] @ (List.remove_assoc k t)

let rec propagate_sorts_rec (input_sorting : sorting) (types : typing) (cotypes : typing) (input_process : scoped_process) : scoped_process * sorting * typing * bool =
  match input_process with 
  | Scoped_Request (a, k, p) -> 
    begin
      let accept, request, new_sorting = pop_session a input_sorting in
      let new_types = [(k,request)] @ types in
      let new_cotypes = [(k,accept)] @ cotypes in
      let new_p, new_s, new_t, change = propagate_sorts_rec new_sorting new_types new_cotypes p in
      let new_s, new_t = match List.assoc_opt k new_t with
        | Some k_type -> [(a, Pair_s(Unknown_t,k_type))] @ new_s, (List.remove_assoc k new_t)
        | None -> [(a, Pair_s(Unknown_t,Inact_t))] @ new_s, new_t
      in Scoped_Request (a, k, new_p), new_s, new_t, change
    end
  | Scoped_Accept (a, k, p) -> 
    begin
      let accept, request, new_sorting = pop_session a input_sorting in
      let new_types = [(k,accept)] @ types in
      let new_cotypes = [(k,request)] @ cotypes in
      let new_p, new_s, new_t, change = propagate_sorts_rec new_sorting new_types new_cotypes p in
      let new_s, new_t = match List.assoc_opt k new_t with
        | Some k_type -> [(a, Pair_s(k_type,Unknown_t))] @ new_s, (List.remove_assoc k new_t)
        | None -> [(a, Pair_s(Inact_t,Unknown_t))] @ new_s, new_t
      in Scoped_Accept (a, k, new_p), new_s, new_t, change
    end
  | Scoped_Send (k, e, p) -> 
    begin
      let t, new_types = pop_type k types in
      let co_t, new_cotypes = pop_type k cotypes in
      let new_p, new_s, new_t, change = propagate_sorts_rec input_sorting new_types new_cotypes p in
      let new_sort, new_change = match t with 
        | Send_t (Var_s _,_) -> 
          begin
            match e_sort input_sorting e with
            | Var_s x -> Var_s x, false
            | e_s -> e_s, true (* This should only be Nat_s or Bool_s, e_sort checks the important stuff. *)
          end
        | Send_t (cur_s,_) -> cur_s, false
        | Inact_t -> raise (TypeError "propagate_sorts_rec Scoped_Send found inact")
        | Reception_t (_,_) -> raise (TypeError "propagate_sorts_rec Scoped_Send found reception")
        | _ -> raise (TypeError "propagate_sorts_rec Scoped_Send") (* This should not be possible. *)
      in
      let new_t = match List.assoc_opt k new_t with
        | Some k_type -> [(k,Send_t(new_sort,k_type))] @ (List.remove_assoc k new_t)
        | None -> [(k,Send_t(new_sort,Inact_t))] @ new_t
      in
      Scoped_Send (k, e, new_p), new_s, new_t, new_change || change
    end
  | Scoped_Reception (k, v, p) -> 
    begin
      let t, new_types = pop_type k types in
      let co_t, new_cotypes = pop_type k cotypes in
      let new_sort, new_change = match t, co_t with 
        | Reception_t (Var_s _,_), Send_t (Nat_s,_) -> Nat_s, true
        | Reception_t (Var_s _,_), Send_t (Bool_s,_) -> Bool_s, true
        | Reception_t (_,_), Send_t (Var_s _,_) -> Var_s v, false (* The cotype send is still on a var *)
        | Reception_t (recept_s,_), Send_t (_,_) -> recept_s, false (* Keep what was already known *)
        | _ -> raise (TypeError "propagate_sorts_rec Scoped_Reception") (* This should not be possible. *)
      in
      let new_sorting = [(v,new_sort)] @ input_sorting in
      let new_p, new_s, new_t, change = propagate_sorts_rec new_sorting new_types new_cotypes p in
      let new_t = match List.assoc_opt k new_t with
        | Some k_type -> [(k,Reception_t(new_sort,k_type))] @ (List.remove_assoc k new_t)
        | None -> [(k,Reception_t(new_sort,Inact_t))] @ new_t
      in
      Scoped_Reception (k, v, new_p), new_s, new_t, new_change || change
    end
  | Scoped_Branch (k, labels_proc) ->
    begin
      let label_selection = possible_selection k cotypes in
      let branch_to_check = List.filter (fun (l,_) -> (List.exists (fun l_prime -> (compare l l_prime) == 0) label_selection)) labels_proc in
      let map_propagation = fun (l,l_proc) : (label * scoped_process * sorting * typing * bool) ->
        begin
          let new_types = consume_branching k l types in 
          let new_cotypes = consume_select k l cotypes in
          let new_p, new_s, new_t, new_change = propagate_sorts_rec input_sorting new_types new_cotypes l_proc in
          let new_t = match List.assoc_opt k new_t with
            | Some k_type -> new_t
            | None -> [(k,Inact_t)] @ new_t
          in
          (l, new_p, new_s, new_t, new_change)
        end
      in
      let propagated = List.map map_propagation branch_to_check in
      let new_labels_procs = List.map (fun (l,new_p,_,_,_) -> (l,new_p)) propagated in
      let new_change = List.fold_left (fun acc (_,_,_,_,cur_change) -> acc || cur_change) false propagated in
      (* let combined_sortings = List.fold_left (fun acc (l,_,new_s,_,_) -> 
        List.fold_left (fun acc2 (name,n_sort) -> 
          let new_pair = match List.assoc_opt name acc2, n_sort with
            | Some (Pair_s (Branch_t (labels_types1),Unknown_t)), Pair_s (accept2,Unknown_t) -> Pair_s (Branch_t ([(l,accept2)] @ labels_types1),Unknown_t)
            | Some (Pair_s (Unknown_t,Branch_t (labels_types1))), Pair_s (Unknown_t,request2) -> Pair_s (Unknown_t,Branch_t ([(l,request2)] @ labels_types1))
            | None, Pair_s (accept,Unknown_t) -> Pair_s (Branch_t ([(l,accept)]),Unknown_t)
            | None, Pair_s (Unknown_t,request) -> Pair_s (Unknown_t, Branch_t (([(l,request)])))
            | _,_ -> raise (TypeError "incompatible sortings in branching")
          in 
          [(name,new_pair)] @ (List.remove_assoc name acc2)
        ) acc new_s
      ) [] propagated in  *)
      let combined_sortings = List.fold_left (fun acc (l,_,new_s,_,_) -> 
        List.fold_left (fun acc2 (name,n_sort) -> 
          let new_pair = match List.assoc_opt name acc2, n_sort with
            | Some (Pair_s (accept1,Unknown_t)), Pair_s (accept2,Unknown_t) -> Pair_s ((combine_types_for_branching accept1 accept2),Unknown_t)
            | Some (Pair_s (Unknown_t,request1)), Pair_s (Unknown_t,request2) -> Pair_s (Unknown_t,(combine_types_for_branching request1 request2))
            | None, Pair_s (accept,Unknown_t) -> n_sort
            | None, Pair_s (Unknown_t,request) -> n_sort
            | _,_ -> raise (TypeError "incompatible sortings in branching during sorting generation")
          in 
          [(name,new_pair)] @ (List.remove_assoc name acc2)
        ) acc new_s
      ) [] propagated in
      (* let combined_types = List.fold_left (fun acc (l,_,_,new_t,_) ->
        List.fold_left (fun acc2 (k,k_type) ->
          let new_k_type = match List.assoc_opt k acc2 with
            | Some Branch_t (label_types) -> Branch_t ([(l,k_type)] @ label_types)
            | None -> Branch_t ([(l,k_type)])
            | _ -> raise (TypeError "unxpected type found while combining labels")
          in
          [(k,new_k_type)] @ (List.remove_assoc k acc2)
        ) acc new_t
      ) [] propagated in *)
      let combined_types = List.fold_left (fun acc (l,_,_,new_t,_) ->
        List.fold_left (fun acc2 (k_prime,k_prime_type) ->
          let new_k_prime_type = if (compare k k_prime) == 0 then 
              match List.assoc_opt k_prime acc2 with
              | Some Branch_t (label_types) -> 
                begin 
                  match List.mem_assoc l label_types with
                  | true -> raise (TypeError "label is already in branching")
                  | false -> Branch_t ([(l,k_prime_type)] @ label_types) 
                end
              | None -> Branch_t ([(l,k_prime_type)])
              | _ -> raise (TypeError "unexpected type found while combining labels")
            else
              match List.assoc_opt k_prime acc2 with
              | Some k_p_t -> combine_types_for_branching k_p_t k_prime_type
              | None -> k_prime_type
          in
          [(k_prime,new_k_prime_type)] @ (List.remove_assoc k_prime acc2)
        ) acc new_t
      ) [] propagated in
      Scoped_Branch (k, new_labels_procs), combined_sortings, combined_types, new_change
    end
  | Scoped_Selection (k, l, p) -> 
    begin
      let new_types = consume_select k l types in
      let new_cotypes = consume_branching k l cotypes in
      let new_p, new_s, new_t, change = propagate_sorts_rec input_sorting new_types new_cotypes p in
      let new_t =   match List.assoc_opt k new_t with
        | Some k_type -> [(k, Select_t [(l,k_type)])] @ (List.remove_assoc k new_t)
        | None -> [(k, Select_t [(l,Inact_t)])] @ new_t
      in
      Scoped_Selection (k, l, new_p), new_s, new_t, change
    end
  | Scoped_Throw (k1, k2, p) -> Scoped_Inact, [], [], false (* TODO *)
  | Scoped_Catch (k1, k2, p) -> Scoped_Inact, [], [], false (* TODO *)
  | Scoped_Conditional (e, then_p, else_p) -> 
    begin
      let new_then_p, then_s, then_t, then_change = propagate_sorts_rec input_sorting types cotypes then_p in
      let new_else_p, else_s, else_t, else_change = propagate_sorts_rec input_sorting types cotypes else_p in
      match (conditional_sorting_equal then_s else_s), (conditional_typing_equal then_t else_t) with
      | true, true -> Scoped_Conditional (e, new_then_p, new_else_p), then_s, then_t, then_change || else_change
      | _, _ -> raise (TypeError "the conditional statement has different types and sortings for both P and Q in \"if e then P else Q\"")
    end
  | Scoped_Composition (scope, p1, p2) -> 
    begin
      let new_sorting = scope @ input_sorting in
      let new_p1, new_s1, new_t1, new_change1 = propagate_sorts_rec new_sorting types cotypes p1 in
      let new_p2, new_s2, new_t2, new_change2 = propagate_sorts_rec new_sorting types cotypes p2 in
      let partial, complete = compose_sortings new_s1 new_s2 in
      (Scoped_Composition (complete, new_p1, new_p2), partial, compose_typings new_t1 new_t2, new_change1 || new_change2)
    end
  | Scoped_Inact -> Scoped_Inact, [], [], false
  | Scoped_Hide (p_var, p) -> Scoped_Inact, [], [], false (* TODO *)
  | Scoped_Rec (def, p) -> Scoped_Inact, [], [], false (* TODO [], *)
  | Scoped_Proc_Var (p_var, e, k) -> Scoped_Inact, [], [], false (* TODO *)

let rec propagate_sorts (p : scoped_process) : scoped_process =
  let new_p, _, _, changed = propagate_sorts_rec [] [] [] p in
  match changed with
  | true -> propagate_sorts new_p
  | false -> new_p
