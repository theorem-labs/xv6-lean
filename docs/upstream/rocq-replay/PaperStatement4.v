Require Import xv6iris.SystemUartAccepted.
Definition statement_seed := ltac:(let T := type of (@xv6_out_accepted_xv6Σ) in exact T).
Set Printing Width 300.
Print All Dependencies statement_seed.
Print Assumptions statement_seed.
