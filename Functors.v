Require Import HoTT.

Generalizable Variables T F A B.

Class TCategory := {
  Ob: Type;
  Hom: relation Ob;
  id: forall x: Ob, Hom x x;
  comp: forall x y z: Ob, Hom y z -> Hom x y -> Hom x z
  }.

Infix "-->" := Hom (at level 90, right associativity).
Coercion Ob: TCategory >-> Sortclass.

Global Instance Grpd: TCategory := {
  Ob := Type;
  Hom := fun x y: Type => x -> y;
  id := fun x: Type => idmap;
  comp := fun (x y z: Type) (f: y -> z) (g: x -> y) => f o g
  }.

Class TFunctor (F: Type -> Type) :=
  fmap: forall {A B: Type}, (A -> B) -> (F A -> F B).

Arguments fmap F {_ A B} _ _.
Global Notation "f $ a" := (fmap f a) (at level 99, right associativity).

Class TApplicative (T: Type -> Type) {E: TFunctor T} := {
(*  pure: forall {A: Type}, A -> T A; *)  (*Causes bug in Coq. See #4208 *)
  fzip: forall {A B: Type}, T (A -> B) -> T A -> T B
  }.

Class TMonad (T: Type -> Type) := {
  bind: forall {A B: Type}, (T A) -> (A -> T B) -> T B;
  ret: forall {A: Type}, A -> T A
  }.

Notation "x >>= f" := (bind x f) (at level 90).
Notation "x <- y ; f" := (y >>= (fun x => f)) 
    (at level 100, f at level 200, 
    format "'[v' x  '<-'  y ';' '/' f ']'").

Section Monads.

  Context `{E: TMonad T}.

  Global Instance monad_is_functor: TFunctor T :=
    fun `(f: A -> B) (t: T A) => x <- t; ret (f x).

  Definition join {A: Type} (t: T (T A)): T A 
    := x <- t; x.

  Lemma join_is_action (A: Type): 
    join o (T $ join) = join o (join (A:=T A)).
  Admitted.
    
  Lemma ret_is_unit (A: Type) (x: T A): join ((T $ ret) x) = x.
  Admitted.

  Global Instance monad_is_applicative (A B: Type): TApplicative T
    := {| fzip := fun A B (f: T (A -> B)) (t: T A) => 
        a <- t; g <- f; ret (g a) |}.
(*
    (* Cannot use this definition due to #4208 *)
  Global Instance monad_is_applicative (A B: Type): TApplicative T
    := let Tapply A B := fun (f: T (A -> B)) (t: T A) => 
    a <- t; g <- f; ret (g a) 
    in {| pure := ret; fzip := Tapply |}.
*)

End Monads.