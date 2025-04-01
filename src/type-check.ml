

type sorting = (string * sort) list (* \Gamma *) (* TODO: check if string is appropriate *)
type basis = (proc_var * ((sort list) * (typ list))) list (* \Theta *)(* TODO: check if list tuple is appropriate *)

type typing = (channel * typ) list (* \Delta *)

exception TypeError

let rec type_check (theta : basis) (gamma : sorting) (input_process : process) : typing = match input_process with
(* REQ *)  | Request (a,k,p) -> (match (find_opt (fun (s1,_) -> (compare s1 a) == 0) gamma) with 
    | Some (a,a_type) -> (
      match a_type with 
        | Pair (alpha,alpha_bar) -> (if cotype )
        | _ -> raise TypeError 
    )
)


(match type_check theta gamma with ->


  | typing t -> List.filter (fun (chan,cotyp) -> (compare chan k) == 0) t
  | _ -> raise TypeError)
  | 
  )