#use "types.ml"
#use "terms.ml"
#use "type-check.ml"

let (bank : process) = Accept ("b", "h", Branch ("h", [
  ("bank_deposit", Reception ("h", "id", Reception ("h", "amt", Inact)));
  ("bank_withdraw", Reception ("h", "id", Reception ("h", "amt", Selection ("h", "atm_failure", Inact))));
  ("bank_balance", Send ("h", Cst (Int 0), Inact));
]))

let (atm : process) = Accept ("a", "k", Reception ("k", "id", Branch ("k", [
  ("atm_deposit", Request ("b", "h", Reception ("k", "amt", Selection ("h", "bank_deposit", Send ("h", Var "id", Send ("h", Var "amt", Inact))))));
  ("atm_withdraw", Request ("b", "h", Reception ("k", "amt", Selection ("h", "bank_withdraw", Send ("h", Var "id", Send ("h", Var "amt", Branch ("h", [
    ("atm_success", Selection ("k", "user_dispense", Send ("k", Var "amt", Inact)));
    ("atm_failure", Selection ("k", "user_overdraft", Inact));
  ])))))));
  ("atm_balance", Request ("b", "h", Selection ("h", "bank_balance", Reception ("h", "amt", Send ("k", Var "amt", Inact)))));
])))

let (user : process) = Request ("a", "k", Send ("k", Cst (Int 42), Selection ("k", "atm_withdraw", Send ("k", Cst (Int 100), Branch ("k", [
  ("user_dispense", Reception ("k", "amt", Inact));
  ("user_overdraft", Inact);
])))))

let (p : process) = Composition (bank, Composition (atm, user))

let scoped_p, s, t = gen_sortings p

(* let a = List.assoc "a" s *)

(* let Pair_s (a_accept,a_request) = a *)

let (example_user : process) = Request ("a", "k", Reception ("k", "x", Inact))

let (example_server : process) = Accept ("a", "k", Send ("k", Cst (Int 5), Inact))

(* let example_sorting, _ = gen_sortings (Composition (example_user, example_server)) *)

let (test_user : process) = Request ("a", "k", Reception ("k", "x", Inact))

let (test_mid : process) = Accept ("a", "k", Request ("b", "h", Reception ("h", "y", Send ("k", Var "y", Inact))))

let (test_server : process) = Accept ("b", "h", Send ("h", Cst (Int 5), Inact))

let scoped_test, _, _ = gen_sortings (Composition (test_user, Composition (test_mid, test_server)))

let propagated_test = propagate_sorts scoped_test