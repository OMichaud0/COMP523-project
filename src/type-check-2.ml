#use type-check.ml
#use example.ml

(* take scoped_process p and return  *)
let check-program (p : process) : boolean =
  (* TODO: add try catch *)
  let scoped, _, _  = gen_sortings p in (* TODO: need to check if others are empty? *)
  let propagated = propagate_sorts scoped in
  match type_check propagated [] [] with
  | [] -> true (* Delta is empty *)
  | _ -> false

let rec type_check_2 (p : scoped_process) (s : sorting) (c : typing) : typing =
  match p with
  | Scoped_Request (a,k,p) ->
      let alpha,alpha_bar,s_new = pop_session a s in
      let delta = type_check_2 p s_new (c @ (k,alpha)) in
      let alpha_prime,delta = pop_type k delta in
      if alpha_prime = alpha_bar then delta else raise TypeError ("Expected type " ^ alpha_bar ^ " for request of channel " ^ k ^ " but got type " ^ alpha_prime)
  | Scoped_Accept (a,k,p) -> 
      let alpha,alpha_bar_s_new = pop_session a s in
      let delta = type_check_2 p s_new (c @ (k,alpha_bar)) in
      let alpha_prime,delta = pop_type k delta in
      if alpha_prime = alpha then delta else raise TypeError ("Expected type " ^ alpha ^ " for accept of channel " ^ k ^ " but got type " ^ alpha_prime)
  | Scoped_Send (k,e,p) ->
      let s_tilde = e_sort s e in
      let _,c = pop_type k c in
      let delta = type_check_2 p s c in
      begin
        match List.assoc_opt k delta with
        | Some alpha -> [(k,Send_t (s_tilde,alpha))] @ (List.remove_assoc k delta)
        | _ -> [(k,Send_t (s_tilde,Inact))] @ (List.remove_assoc k delta)
      end
  | Scoped_Reception (k,x,p) ->
    let s_tilde,c = pop_type k c in
    let delta = type_check_2 p ([(x,s_tilde)] @ s) c in
    begin
      match List.assoc_opt k delta with
      | Some alpha -> [(k,Reception_t (s_tilde,alpha))] @ (List.remove_assoc k delta)
      | _ -> [(k,Reception_t (s_tilde,Inact))] @ (List.remove_assoc k delta)
    end
  | Scoped_Branch (k,ls) ->
    
  | Scoped_Throw (k,k_prime,p) ->
    let delta = type_check_2 p s c in
    let alpha,c = pop_type k_prime c in
    begin
      match List.assoc_opt k delta with
      | Some beta -> [(k,Send_t (alpha,beta))] @ [(k_prime,alpha)] @ (List.remove_assoc k delta)
      | _ -> [(k,Send_t (alpha,Inact))] @ [(k_prime,alpha)] @ (List.remove_assoc k delta)
    end
  | Scoped_Catch (k,k_prime,p) ->
    let delta = type_check_2 p s c in
    let beta =
      match List.assoc_opt k delta with
      | Some b -> b
      | _ -> Inact
    in
    let alpha =
      match List.assoc_opt k' delta with
      | Some a -> a
      | _ -> Inact
    in
    [(k,Reception_t (alpha,beta))] @ (List.remove_assoc k delta)
  | Scoped_Conditional (e,p,q) ->
  | Scoped_Inact -> []
  | Scoped_Composition (s_new,p,q) ->
    let s = s @ s_new in
    let delta = type_check_2 p s in
    let delta_prime = type_check_2 q s in
    if is_compatible delta delta_prime then compose delta delta_prime else (raise TypeError "Scoped_Composition typing error: composed processes have incompatible typings")