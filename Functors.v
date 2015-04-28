Require Import HoTT.
Require Import Pushforwards.

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
<<<<<<< Updated upstream
=======

  (** We regard the type family is_op as a predicate stating that a function `f: T A -> A` is a "virtual operation", i.e. it is an iterated composition of some deining set of primitive operations or their deformations. E.g. if A is a strict semigroup and T = List, then `m: T A -> A` is a tuple (m_0, m_1, .. , m_k, ..) of k-ary products `m_k: A^k -> A` and a virtual operation is a pair (h: T A -> A, p: h = m). Note that in this case all iterated compositions of m are trivially equal to m and thus we can define a composition of virtual operations, extending the usual one. In general there will be nontrivial paths between iterated compositions of m_i, thus we need to choose composition on `sig is_op` beforehand. *)
(*  Definition VirtualOp {A: Type} (is_op: (T A -> A) -> Type) := 
    exists (f: T A -> A), is_op f.*)
>>>>>>> Stashed changes

  Section Composition.
  
    Context {A: Type}.
    Variable is_op : (T A -> A) -> Type.
    Variable T_act: T Type -> Type.
    

    (** Morally a point in this type corresponds to T h, where h is some virtual operation. In the case T = List such points are lists [f_1, .. , f_k] of operations with arities [n_1, .. , n_k]. *)
    Definition T_is_op: (T (T A) -> T A) -> Type :=
      let t_fam := T_act o (T $ is_op)
      in push_sigma t_fam (fzip T _ _).

    Definition VirtualCompose :=
      forall (f: sig T_is_op) (g: sig is_op),
      { h: sig is_op | h.1 o join = g.1 o f.1 }.

  End Composition.
  
  Record TAlgebra (A: Type):= 
  {
    is_op: (T A -> A) -> Type;
    comp: VirtualCompose is_op;
    unique_operation: Contr (exists f, is_op f)
    }.


  Record Assoc_map {X Y: Type} (A: Associative X) (B: Associative Y) :=
    {
      base_map: X -> Y;
      operation_map: forall (f: VirtualOp A), exists (g: VirtualOp B),
                      g.1 o base_map = base_map o f.1;
      compose_map: 

End Algebras.