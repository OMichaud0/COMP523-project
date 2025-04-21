#use "types.ml"
#use "terms.ml"
#use "type-check.ml"

(* ################################################################################ *)

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

let (atm : process) = Composition (bank, Composition (atm, user))

let atm_check = check_program atm

(* ################################################################################ *)

let (example_user : process) = Request ("a", "k", Reception ("k", "x", Inact))

let (example_server : process) = Accept ("a", "k", Send ("k", Cst (Int 5), Inact))

(* ################################################################################ *)

let (test_user : process) = Request ("a", "k", Reception ("k", "x", Inact))

let (test_mid : process) = Accept ("a", "k", Request ("b", "h", Reception ("h", "y", Send ("k", Var "y", Inact))))

let (test_server : process) = Accept ("b", "h", Send ("h", Cst (Int 5), Inact))

let test = Composition (test_user, Composition (test_mid, test_server))

let test_check = check_program test

(* ################################################################################ *)

let (cond_test_user : process) =  Request ("a", "k", Reception ("k", "x", Conditional (Var "x", Inact, Inact)))

let (cond_test_mid : process) = Accept ("a", "k", Request ("b", "h", Reception ("h", "y", Send ("k", Var "y", Inact))))

let (cond_test_server_fail : process) = Accept ("b", "h", Send ("h", Cst (Int 5), Inact))

let (cond_test_server_ok : process) = Accept ("b", "h", Send ("h", Cst (Bool true), Inact))

let (cond_test_fail : process) = (Composition (cond_test_user, Composition (cond_test_mid, cond_test_server_fail)))

let (cond_test_ok : process) = (Composition (cond_test_user, Composition (cond_test_mid, cond_test_server_ok)))

let cond_test_fail_check = check_program cond_test_fail

let cond_test_ok_check = check_program cond_test_ok