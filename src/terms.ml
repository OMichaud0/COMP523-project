type name = string

type channel = string

type label = string

type var = string

type const =
  | Int of int
  | Bool of bool

type proc_var =
  | Name of name
  | Channel of channel

type variable = string

type expr = 
  | Var of var
  | Cst of const

type process = 
  | Request of name * channel * process
  | Accept of name * channel * process
  | Send of channel * expr * process
  | Reception of channel * variable * process
  | Branch of channel * label * process
  | Selection of channel * ((label * process) list)
  | Throw of channel * channel * process
  | Catch of channel * channel * process
  | Conditional of expr * process * process
  | Composition of process * process
  | Inact
  | Hide of proc_var * process
  | Rec of def_rec * process
  | Proc_Var of proc_var * expr * channel
and rec_atom = proc_var * variable * channel * process
and def_rec = rec_atom list (* do we need to account for empty lists? *)

(* let P = Request("test" "test" Proc_var("Q")) *)