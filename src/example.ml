#use "types.ml"
#use "terms.ml"
#use "type-check.ml"

let (bank : process) = Accept ("b", "h", Branch ("h", [
  ("deposit", Reception ("h", "id", Reception ("h", "amt", Inact)));
  ("withdraw", Reception ("h", "id", Reception ("h", "amt", Selection ("h", "failure", Inact))));
  ("balance", Send ("h", Cst (Int 0), Inact));
]))

let (atm : process) = Accept ("a", "k", Reception ("k", "id", Branch ("k", [
  ("deposit", Request ("b", "h", Reception ("k", "amt", Selection ("h", "deposit", Send ("h", Var "id", Send ("h", Var "amt", Inact))))));
  ("withdraw", Request ("b", "h", Reception ("k", "amt", Selection ("h", "withdraw", Send ("h", Var "id", Send ("h", Var "amt", Branch ("h", [
    ("success", Selection ("k", "dispense", Send ("k", Var "amt", Inact)));
    ("failure", Selection ("k", "overdraft", Inact));
  ])))))));
  ("balance", Request ("b", "h", Selection ("h", "balance", Reception ("h", "amt", Send ("k", Var "amt", Inact)))));
])))

let (user : process) = Request ("a", "k", Send ("k", Cst (Int 42), Selection ("k", "withdraw", Send ("k", Cst (Int 100), Branch ("k", [
  ("dispense", Reception ("k", "amt", Inact));
  ("overdraft", Inact);
])))))

let (p : process) = Composition (bank, Composition (atm, user))

let s, _ = gen_sortings p

let a = List.assoc "a" s

let Pair_s (a_accept,a_request) = a