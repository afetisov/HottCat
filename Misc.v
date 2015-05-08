Require Import HoTT.

Open Scope nat_scope.

Definition nat_discr {n: nat}: 0 <> S n := 
  fun p: 0 = S n => path_nat^-1 p.

Definition nat_discr' {m n: nat}: m <> m + (S n).
  intro p.
  apply (path_nat^-1) in p.
  induction m; auto.
  Qed.