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

exception TypeError

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
      | _ -> raise TypeError

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
            | _ -> raise TypeError 
        end
      | None -> raise TypeError
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
            | _ -> raise TypeError 
        end
      | _ -> raise TypeError
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
    if is_compatible deltap deltaq then compose deltap deltaq else raise TypeError
  | _ -> raise TypeError

  (* (match type_check theta gamma with ->


  | typing t -> List.filter (fun (chan,cotyp) -> (compare chan k) == 0) t
  | _ -> raise TypeError)
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
  | _, _ -> raise TypeError (* Both sorting contain a common name so a name was used to create more than one session *)

let construct_pair_s (s1 : sort) (s2 : sort) : sort =
  match s1, s2 with
  | Pair_s (accept,Unkown_t), Pair_s (Unkown_t,request) -> Pair_s(accept,request)
  | Pair_s (Unkown_t,request), Pair_s (accept,Unkown_t) -> Pair_s(accept,request)
  | _, _ -> raise TypeError

let compose_sortings (s1 : sorting) (s2 : sorting) : sorting =
  let (d1,_) = List.split s1 in
  let (d2,_) = List.split s2 in
  let names1 = StringSet.of_list d1 in
  let names2 = StringSet.of_list d2 in
  let single1 = StringSet.diff names1 names2 in
  let single2 = StringSet.diff names2 names1 in
  let common = StringSet.inter names1 names2 in
  (List.map (fun a -> (a,List.assoc a s1)) (StringSet.to_list single1)) 
  @ (List.map (fun a -> (a,construct_pair_s (List.assoc a s1) (List.assoc a s2))) (StringSet.to_list common)) 
  @ (List.map (fun a -> (a,List.assoc a s2)) (StringSet.to_list single2))

let compose_typings (t1 : typing) (t2 : typing) : typing =
  let (d1,_) = List.split t1 in
  let (d2,_) = List.split t2 in
  let names1 = StringSet.of_list d1 in
  let names2 = StringSet.of_list d2 in
  let common = StringSet.inter names1 names2 in
  match StringSet.cardinal common with
  | 0 -> t1 @ t2
  | _ -> raise TypeError (* a channel is used in both sortings *)

let extend_name (label : string) (name : string) : string = String.concat "_" [label;name]

let rec gen_sortings (input_process : process) : sorting * typing =
  match input_process with 
  | Request (a, k, p) -> 
    begin
      let s, t = gen_sortings p in
      match (List.assoc_opt a s, List.assoc_opt a t) with
      | None, None -> 
        begin
          match List.assoc_opt k t with
          | Some k_type -> ([(a, Pair_s(Unkown_t,k_type))] @ s, (List.remove_assoc k t))
          | None -> ([(a, Pair_s(Unkown_t,Inact_t))] @ s, t) (* Is Inact_t appropriate as the end of the type? *)
        end
      | _, _ -> raise TypeError (* The name a was used for another session or as a channel. *)
    end
  | Accept (a, k, p) -> 
    begin
      let s, t = gen_sortings p in
      match (List.assoc_opt a s, List.assoc_opt a t) with
      | None, None -> 
        begin
          match List.assoc_opt k t with
          | Some k_type -> ([(a, Pair_s(k_type,Unkown_t))] @ s, (List.remove_assoc k t))
          | None -> ([(a, Pair_s(Inact_t,Unkown_t))] @ s, t) (* Is Inact_t appropriate as the end of the type? *)
        end
      | _, _ -> raise TypeError (* The name a was used for another session or as a channel. *)
    end
  | Send (k, e, p) ->
    begin
      let e_sort = expr_sort e in
      let s, t = gen_sortings p in 
      match List.assoc_opt k t with 
      | Some k_type -> (s, (List.remove_assoc k t) @ [(k, Send_t (e_sort, k_type))])
      | None -> (s, t @ [(k, Send_t (e_sort, Inact_t))]) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Reception (k, v, p) -> 
    begin
      let s, t = gen_sortings(p) in 
      match List.assoc_opt k t with 
      | Some k_type -> (s, (List.remove_assoc k t) @ [(k, Reception_t (Var_s v, k_type))])
      | None -> (s, t @ [(k, Reception_t (Var_s v, Inact_t))]) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Branch (k, labels_proc) -> 
    (* TODO Fix propagation of empty branch. If (label,process) does not contain operations on k, 
    should add to branching with Inact/Closed so it can match with the selection of this branch.*)
    begin
      let fold_fct = fun ((s,t) : (sorting * typing)) (l, p) -> 
        begin
          let s_prime, t_prime = gen_sortings p in
          let sorting_extend_fct = fun (a,a_sorting) -> 
            begin
              match List.assoc_opt a s with
              | Some a_s ->
                begin 
                  match a_s, a_sorting with
                  | Pair_s (accept1, Unkown_t), Pair_s (accept2, Unkown_t) ->
                    begin
                      match accept1 with 
                      | Branch_t accept_labels -> 
                        begin
                          match List.assoc_opt l accept_labels with
                          | Some _ -> raise TypeError (* Label is already in branching *)
                          | None -> (a, Pair_s (Branch_t (accept_labels @ [(l, accept2)]), Unkown_t))
                        end
                      | _ -> raise TypeError (* Should not be possible, the None case below creates the initial branching. *)
                    end
                  | Pair_s (Unkown_t, request1), Pair_s (Unkown_t, request2) ->
                    begin
                      match request1 with 
                      | Branch_t request_labels -> 
                        begin
                          match List.assoc_opt l request_labels with
                          | Some _ -> raise TypeError (* Label is already in branching *)
                          | None -> (a, Pair_s (Unkown_t, Branch_t (request_labels @ [(l, request2)])))
                        end
                      | _ -> raise TypeError (* Should not be possible, the None case below creates the initial branching. *)
                    end
                  | _, _ -> raise TypeError (* Should not get anything but pairs. *)
                end
              | None -> 
                begin 
                  match a_sorting with
                  | Pair_s (accept, Unkown_t) -> (a, Pair_s (Branch_t [(l, accept)], Unkown_t))
                  | Pair_s (Unkown_t, request) -> (a, Pair_s (Unkown_t, Branch_t [(l, request)]))
                  | Pair_s (accept, request) -> (extend_name l a,a_sorting)
                  | _ -> raise TypeError (* Should not get anything but pairs. *)
                end
              (* match s with
              | Pair_s (accept,Unkown_t) -> 
                begin 
                  match accept with 
                  | Branch accept_labels ->
                  | 
                end
              | Pair_s (Unkown_t, request) -> 
              | Pair_s (accept,request) -> (extend_name l a,s)
              | _ -> raise TypeError (* Should not encounter anything but pairs here. *) *)
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
                      | Some _ -> raise TypeError (* The label was already in the branching*)
                      | None -> (k, Branch_t ([(l,k_type)] @ k_labels))
                    end
                  | _ -> raise TypeError (* The channel k does not have type Branch_t so label cannot be added*)
                end
              | None -> (k, Branch_t [(l, k_type)])
            end
          in
          let intermediate_t = List.map type_extend_fct t_prime in
          let new_t = intermediate_t @ (List.filter (fun (k,_) -> not (List.mem_assoc k intermediate_t)) t)
          in (new_s, new_t)
        end
        (* (let s, t = gen_sortings p in (combine_sortings acc s), (l,t)) in *)
      in
      let (acc : (sorting * typing)) = ([],[]) in
      let s, labels_typ = List.fold_left fold_fct acc labels_proc in
      (s, labels_typ)
    end
  | Selection (k, l, p) -> 
    begin
      let s, t = gen_sortings p in
      match List.assoc_opt k t with
      | Some k_type -> (s, [(k, Select_t [(l,k_type)])] @ (List.remove_assoc k t))
      | None -> (s, [(k, Select_t [(l,Inact_t)])] @ t) (* Is Inact_t appropriate as the end of the type? *)
    end
  | Throw (k1, k2, p) -> ([], []) (* TODO *)
  | Catch (k1, k2, p) -> ([], []) (* TODO *)
  | Conditional (e, then_p, else_p) -> 
    begin
      (* let then_s, then_t = gen_sortings then_p in
      let else_s, else_t = gen_sortings else_p in *)
      ([], []) (* TODO Either check here that both sides has same type or combine the outputs and delegate to later. *)
    end
  | Composition (p1, p2) ->
    begin
      let s1, t1 = gen_sortings p1 in
      let s2, t2 = gen_sortings p2 in
      (compose_sortings s1 s2, compose_typings t1 t2)
    end
  | Inact -> ([], [])
  | Hide (p_var, p) -> ([], []) (* TODO *)
  | Rec (def, p) -> ([], []) (* TODO *)
  | Proc_Var (p_var, e, k) -> ([], []) (* TODO *)
