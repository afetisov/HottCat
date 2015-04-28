Require Import HoTT.

Generalizable Variables T F A B.

Local Notation Endofunctor := (Type -> Type).
(*
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
*)

Class TFunctor (F: Endofunctor) :=
  fmap: forall {A B: Type}, (A -> B) -> (F A -> F B).

Arguments fmap F {_ A B} _ _.
Global Notation "f $ a" := (fmap f a) (at level 99, right associativity).

Class TApplicative (T: Endofunctor) {E: TFunctor T} := {
  pure: forall {A: Type}, A -> T A;
  fzip: forall {A B: Type}, T (A -> B) -> T A -> T B
  }.

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

  Global Instance monad_is_applicative (A B: Type): TApplicative T
    := let Tapply A B := fun (f: T (A -> B)) (t: T A) => 
    a <- t; g <- f; ret (g a) 
    in {| pure := @ret _ _; fzip := Tapply |}.

End Monads.

Section Algebras.

  Context `{TMonad T}.

  Section Composition.
  
    Variable A: Type.
    Variable is_op : (T A -> A) -> Type.
    Variable T_act: T Type -> Type.
    
    Definition T_is_op: (T (T A) -> T A) -> Type.
    apply (fmap (B:=Type)) in is_op.
    apply (@fzip _ _ _ (T A -> A) Type) in T is_op.
    
    
  Definition VirtualCompose (is_op : (T A -> A) -> Type) := 
  
    let V := (exists f, is_op f) in
    forall (f g: V), exists (h: V), (g.1 o (list_map f.1) = h.1 o merge).

  Record TAlgebra (A: Type):= 
  {
    is_op: (T A -> A) -> Type;
    comp: VirtualCompose is_op;
    unique_operation: Contr (exists f, is_op f)
    }.

  Definition VirtualOp {X: Type} (A: Associative X) := 
    exists (f: list X -> X), A.(is_op) f.

  Record Assoc_map {X Y: Type} (A: Associative X) (B: Associative Y) :=
    {
      base_map: X -> Y;
      operation_map: forall (f: VirtualOp A), exists (g: VirtualOp B),
                      g.1 o base_map = base_map o f.1;
      compose_map: 

End Algebras.