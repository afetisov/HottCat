Require Import HoTT.

Definition push_sigma {A B: Type} (P: A -> Type) (f: A -> B): B -> Type
  := fun b: B => { a: A | P a & f a = b}.

Definition push_prod {A B: Type} (P: A -> Type) (f: A -> B): B -> Type
  := fun b: B => forall a: A, (f a = b) -> P a.