Local Unset Elimination Schemes.

Definition relation (A: Type) := A -> A -> Type.
Inductive Chain {A: Type} (P: relation A) : relation A :=
  | idchain {x: A} : Chain P x x
  | concat {x y z: A} : (P y z) -> (Chain P x y) -> (Chain P x z).

(*Scheme Chain_ind := Induction for Chain Sort Type.*)
Scheme Chain_ind := Induction for Chain Sort Type.
Scheme Chain_rec := Minimality for Chain Sort Type.
Definition Chain_rect := Chain_ind.

Inductive nat' : Type :=
  | O : nat'
  | I : nat'.   (* Two constructors => FAIL!!! *)
(*  | S : nat' -> nat'.  (* !!!!!!  *)*)

 Definition length {A: Type}{PA: relation A}{x y: A} (fs: Chain PA x y) : nat' := O.

(*Inductive path {A: Type} (x y: A) :=.*)
Inductive path {A: Type}(x: A) : A -> Type := idpath : path x x.

Lemma map_length {A: Type} {P: relation A}{x y: A} (cs: Chain P x y) : 
    path (length cs) O.
Proof.
  induction cs. exact (idpath O). exact (idpath O).

Qed.

map_length = 
fun (A : Type) (P : relation A) (x y : A) (cs : Chain P x y) =>
Chain_rec A P (fun (x0 y0 : A) (cs0 : Chain P x0 y0) => path (length cs0) 0)
  (fun _ : A => idpath 0)
  (fun (x0 y0 z : A) (_ : P y0 z) (cs0 : Chain P x0 y0)
     (_ : path (length cs0) 0) => idpath 0) x y cs
     : forall (A : Type) (P : relation A) (x y : A) (cs : Chain P x y),
       path (length cs) 0
       
rec

forall (A : Type) (P : relation A) (P0 : A -> A -> Type),
(forall x : A, P0 x x) ->
(forall x y z : A, P y z -> Chain P x y -> P0 x y -> P0 x z) ->
forall y y0 : A, Chain P y y0 -> P0 y y0


rect

forall (A : Type) (P : relation A)
  (P0 : forall a a0 : A, Chain P a a0 -> Type),
(forall x : A, P0 x x (idchain P)) ->
(forall (x y z : A) (p : P y z) (c : Chain P x y),
 P0 x y c -> P0 x z (concat P p c)) ->
forall (y y0 : A) (c : Chain P y y0), P0 y y0 c