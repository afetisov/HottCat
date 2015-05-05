Require Import HoTT.

Definition nat_discr {n: nat}: 0 <> S n := 
  fun p: 0 = S n => path_nat^-1 p.

Definition nat_discr' {m n: nat}: m <> m + n := 
  fun p: 0 = S n => path_nat^-1 p.
