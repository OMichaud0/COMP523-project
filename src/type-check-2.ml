#use "type-check.ml"

(* take scoped_process p and return  *)


let rec type_check_2 (p : scoped_process) (s : sorting) (c : typing) : typing =
  match p with
  | Scoped_Request (a,k,p) ->
      let alpha,alpha_bar,s_new = pop_session a s in
      let delta = type_check_2 p s_new (c @ [(k,alpha)]) in
      let alpha_prime,delta = match List.assoc_opt k delta with
        | Some k_t -> k_t, (List.remove_assoc k delta)
        | None -> Inact_t, delta
      in
      if alpha_prime = alpha_bar then delta else raise (TypeError ("Expected type " ^ " for request of channel " ^ k ^ " but got type "))
  | Scoped_Accept (a,k,p) -> 
      let alpha,alpha_bar,s_new = pop_session a s in
      let delta = type_check_2 p s_new (c @ [(k,alpha_bar)]) in
      let alpha_prime,delta = match List.assoc_opt k delta with
        | Some k_t -> k_t, (List.remove_assoc k delta)
        | None -> Inact_t, delta
      in
      if alpha_prime = alpha then delta else raise (TypeError ("Expected type " ^  " for accept of channel " ^ k ^ " but got type " ))
  | Scoped_Send (k,e,p) ->
      let s_tilde = e_sort s e in
      let _,c = pop_type k c in
      let delta = type_check_2 p s c in
      begin
        match List.assoc_opt k delta with
        | Some alpha -> [(k,Send_t (s_tilde,alpha))] @ (List.remove_assoc k delta)
        | _ -> [(k,Send_t (s_tilde,Inact_t))] @ (List.remove_assoc k delta)
      end
  | Scoped_Reception (k,x,p) ->
    let co_t,c = pop_type k c in
    let s_tilde = match co_t with
      | Send_t (s_sort,_) -> s_sort
      | _ -> raise (TypeError ("Cotype is not a send"))
    in
    let delta = type_check_2 p ([(x,s_tilde)] @ s) c in
    begin
      match List.assoc_opt k delta with
      | Some alpha -> [(k,Reception_t (s_tilde,alpha))] @ (List.remove_assoc k delta)
      | _ -> [(k,Reception_t (s_tilde,Inact_t))] @ (List.remove_assoc k delta)
    end
  | Scoped_Branch (k,ls) ->
    let map_branch = fun (lab,lab_proc) : (label * typing) ->
      let cotypes = consume_select k lab c in
      let delta = type_check_2 lab_proc s cotypes in
      let delta_prime = match List.assoc_opt k delta with
        | Some t -> delta
        | _ -> [(k,Inact_t)] @ delta
      in
      (lab,delta_prime)
    in
    let mapped_labels = List.map map_branch ls in
    List.fold_left (fun acc (l,new_t) ->
      List.fold_left (fun acc2 (k_prime,k_prime_type) ->
        let new_k_prime_type = if (compare k k_prime) == 0 then 
            match List.assoc_opt k_prime acc2 with
            | Some Branch_t (label_types) -> Branch_t ([(l,k_prime_type)] @ label_types) 
            | None -> Branch_t ([(l,k_prime_type)])
            | _ -> raise (TypeError "unexpected type found while combining labels")
          else
            match List.assoc_opt k_prime acc2 with
            | Some k_p_t -> combine_types_for_branching k_p_t k_prime_type
            | None -> k_prime_type
        in
        [(k_prime,new_k_prime_type)] @ (List.remove_assoc k_prime acc2)
      ) acc new_t
    ) [] mapped_labels
  | Scoped_Selection (k,l,p) ->
    let new_cotypes = consume_branching k l c in
      let new_t = type_check_2 p s new_cotypes in
      begin
        match List.assoc_opt k new_t with
          | Some k_type -> [(k, Select_t [(l,k_type)])] @ (List.remove_assoc k new_t)
          | None -> [(k, Select_t [(l,Inact_t)])] @ new_t
      end 
  | Scoped_Conditional (cond, then_p, else_p) ->
    begin
      match e_sort s cond with
      | Bool_s -> 
        begin
          let then_t = type_check_2 then_p s c in
          let else_t = type_check_2 else_p s c in
          match conditional_typing_equal then_t else_t with
          | true -> then_t
          | _ -> raise (TypeError "P and Q of conditional \"if e then P else Q\" have different typings")
        end
      | _ -> raise (TypeError "condition of conditional statement does not have sort bool")
    end
  | Scoped_Inact -> []
  | Scoped_Composition (s_new,p,q) ->
    let s = s @ s_new in
    let delta = type_check_2 p s c in
    let delta_prime = type_check_2 q s c in
    if is_compatible delta delta_prime then compose delta delta_prime else raise (TypeError "Scoped_Composition typing error: composed processes have incompatible typings")

let check_program (p : process) : bool =
  (* TODO: add try catch *)
  let scoped, _, _  = gen_sortings p in (* TODO: need to check if others are empty? *)
  let propagated = propagate_sorts scoped in
  match type_check_2 propagated [] [] with
  | [] -> true (* Delta is empty *)
  | _ -> false