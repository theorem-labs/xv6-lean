Require Import xv6iris.SystemAdequacy.
Definition statement_seed := ltac:(let T := type of (@xv6_obs_wf_xv6Σ) in exact T).
Set Printing Width 300.
Print All Dependencies statement_seed.
Print Assumptions statement_seed.
