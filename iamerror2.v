Require Import HoTT.
Require Import Pushforwards.

Generalizable Variables T F A B.

Local Notation Endofunctor := (Type -> Type).

Class TFunctor (F: Endofunctor) :=
  fmap: forall {A B: Type}, (A -> B) -> (F A -> F B).

Arguments fmap F {_} A B _ _.
Global Notation "f $ a" := (fmap f _ _ a) (at level 99, right associativity).

Class TApplicative `{TFunctor T} := {
  pure: forall {A: Type}, A -> T A;
  fzip: forall {A B: Type}, T (A -> B) -> T A -> T B
  }.

Arguments TApplicative T [_].
Arguments pure T [_ _ A] _.
Arguments fzip T [_ _] A B _ _.

Class TMonad (T: Endofunctor) := {
  bind: forall {A B: Type}, (T A) -> (A -> T B) -> T B;
  ret: forall {A: Type}, A -> T A
  }.

Notation "x >>= f" := (bind x f) (at level 90).
Notation "x <- y ; f" := (y >>= (fun x => f)) 
    (at level 100, f at level 200, 
    format "'[v' x  '<-'  y ';' '/' f ']'").

Section Monads.

  Context `{TMonad T}.

  Global Instance monad_is_functor: TFunctor T :=
    fun `(f: A -> B) (t: T A) => x <- t; ret (f x).

  Definition join {A: Type} (t: T (T A)): T A 
    := x <- t; x.

  Lemma join_is_action (A: Type): 
    join o (T $ join) = join o (join (A:=T A)).
  Admitted.
    
  Lemma ret_is_unit (A: Type) (x: T A): join ((T $ ret) x) = x.
  Admitted.

  Global Instance monad_is_applicative: TApplicative T
    := let Tapply A B := fun (f: T (A -> B)) (t: T A) => 
    a <- t; g <- f; ret (g a) 
    in {| pure := @ret _ _; fzip := fun A B => Tapply  A B |}.

End Monads.

Section Algebras.

  Context `{TMonad T}.
  Variable T_act: T Type -> Type.

  Section Composition.
  
    Context {A: Type}.
    Variable is_op : (T A -> A) -> Type.

    (** Morally a point in this type corresponds to T h, where h is some virtual operation. In the case T = List such points are lists [f_1, .. , f_k] of operations with arities [n_1, .. , n_k]. *)
    Definition T_is_op: (T (T A) -> T A) -> Type :=
      let t_fam := T_act o (T $ is_op)
      in push_sigma t_fam (fzip T _ _).

    Definition VirtualCompose :=
      forall (f: sig T_is_op) (g: sig is_op),
      { h: sig is_op | h.1 o join = g.1 o f.1 }.
    
    Definition VirtualUnit :=
      forall (f: sig is_op), f.1 o ret = idmap.

  End Composition.
  
  Record TAlgebra (A: Type):= 
  {
    is_op: (T A -> A) -> Type;
    comp: VirtualCompose is_op;
    unit: VirtualUnit is_op;
    unique_op: Contr (sig is_op)
    }.
    
  Arguments is_op {A} _ _.
  Arguments comp {A} _ _ _.
  Arguments unit {A} _ _.
  Arguments unique_op {A} _.
  
  Theorem unique_compose {X: Type} {A: TAlgebra X} 
        (f: sig (T_is_op A.(is_op)))  (g: sig A.(is_op)) 
        (R S: VirtualCompose A.(is_op)): R f g = S f g.
    unfold VirtualCompose in R, S.
    pose (Rx := R f g).
    pose (Sx := S f g).
    assert (Rx = Sx).
    destruct Rx as [?h ?p], Sx as [?h ?p].
    destruct A.
