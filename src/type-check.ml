#use "types.ml"
#use "terms.ml"

module ChannelSet = Set.Make(
  struct
    let compare = compare
    type t = channel
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
  (List.map (fun c -> (c,Closed)) intersection) @ (List.map (fun k -> (k,List.assoc k t1)) d1) @ (List.map (fun k -> (k,List.assoc k t2)) d2)


let rec sort_check (gamma : sorting) (e : expr) : sort =
  match e with
    | Cst c -> (match c with
      | Int _ -> Nat
      | Bool _ -> Bool)
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
            | Pair (alpha,alpha_bar) ->
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
            | Pair (alpha,alpha_bar) ->
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
    | None -> Closed
    in
    (List.filter (fun (k_prime,_) -> (compare k k_prime) == 0) delta_prime) @ [(k,Send(e_s,alpha))]
  end
(* RCV *) | Reception (k,x,p) -> (* TODO: *)
  begin
    let sort_x : sort = Var x in
    let gamma_prime = gamma @ [(x,sort_x)] in
    let delta_prime = type_check theta gamma_prime p in
    let alpha = match List.assoc_opt k delta_prime with
    | Some a -> a
    | None -> Closed
    in
    (List.filter (fun (k_prime,_) -> (compare k k_prime) == 0) delta_prime) @ [(k,Reception(sort_x,alpha))]
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
