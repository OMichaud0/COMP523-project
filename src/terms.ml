type name = string

type channel = string

type label = string

type var = string

type const =
  | Int of int
  | Bool of bool

type expr = 
  | Var of var
  | Cst of const

type process = 
  | Request of name * channel * process
  | Accept of name * channel * process
  | Send of channel * expr * process
  | Reception of channel * var * process
  | Branch of channel * 
      ((label * process) list)
  | Selection of channel * label * process
  | Conditional of expr * process * process
  | Composition of process * process
  | Inact
