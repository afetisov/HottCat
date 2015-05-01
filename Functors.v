Require Import HoTT.
Require Import Pushforwards.
Require Import FunextAxiom.

Generalizable Variables T F A B C.

Local Notation Endofunctor := (Type -> Type).
Notation "f $ x" := (f(x)) (at level 60, right associativity, only parsing).

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

Class TFunctor (T: Endofunctor) := {
  fmap: forall {A B: Type}, (A -> B) -> (T A -> T B);
  pres_id: forall {A: Type}, @fmap A A idmap = idmap;
  pres_compose: forall {A B C: Type} (f: B -> C) (g: A -> B), 
                fmap (f o g) = (fmap f) o (fmap g) 
  }.

Arguments fmap T {_} A B _ _.
Notation "T $$ a" := (fmap T _ _ a) (at level 60, right associativity).

Class TApplicative (T: Endofunctor) := {
  pure: forall {A: Type}, A -> T A;
  fzip: forall {A B: Type}, T (A -> B) -> T A -> T B;
  pure_id: forall {A: Type}, @fzip A A (pure idmap) = idmap;
  (** [f] $* [x] = [f x] *)
  homomorphism: forall {A B: Type} (f: A -> B) (x: A), 
                  fzip (pure f) (pure x) = pure (f x);
  (** u $* [x] = [fun g => g x] $* u *)
  interchange: forall {A B: Type} (u: T (A -> B)) (x: A),
               fzip u (pure x) = fzip (pure (fun g => g x)) u;
  (** f $* (g $* x) = (([o] $* f) $* g) $* x *)
  composition: forall {A B C: Type} (f: T(B -> C)) (g: T(A -> B)) (x: T A),
    fzip f (fzip g x) = fzip (fzip (fzip (pure (fun u v => u o v)) f) g) x
  }.

Arguments pure T {_ A} _.
Arguments fzip T {_} A B _ _.

Notation "[ x ]" := (pure _ x).
Notation "f $* a" := (fzip _ _ _  f a) (at level 60, right associativity).

Section Applicative.

  Context `{TApplicative T}.
  
  Section Applicative_is_functor.
  
    Let T_fmap := fun (A B: Type) (f: A -> B) => fzip T _ _ [f].
    Let T_pres_id := fun A: Type => @pure_id _ _ A.
    Let T_pres_compose: forall (A B C : Type) (f : B -> C) (g : A -> B),
              T_fmap A C (fun x : A => f (g x)) =
              (fun x : T A => T_fmap B C f (T_fmap A B g x)).
      intros; unfold T_fmap.
      by_extensionality x.
      transitivity ((([compose] $* [f]) $* [g]) $* x).
      - rewrite (homomorphism compose f).
        rewrite (homomorphism _ g).
        trivial.
      - exact (composition [f] [g] x)^.
      Defined.
    
    Global Instance applicative_is_functor: TFunctor T
      := Build_TFunctor T T_fmap T_pres_id T_pres_compose.
    
  End Applicative_is_functor.

  Lemma pure_natural `(f: A -> B) (x: A): (T $$ f) [x] = [f x].
    unfold "$$", applicative_is_functor.
    destruct H; eauto.
    Defined.

End Applicative.

Class TMonad (T: Endofunctor) := {
  bind: forall {A B: Type}, (T A) -> (A -> T B) -> T B;
  ret: forall {A: Type}, A -> T A;
  ret_unit_left: forall {A B: Type} (k: A -> T B) (a: A),
                 bind (ret a) k  =  k a;
  ret_unit_right: forall {A: Type} (m: T A), bind m ret = m;
  bind_assoc: forall {A B C: Type} (m: T A) (k: A -> T B) (h: B -> T C),
              bind m (fun x => bind (k x) h) = bind (bind m k) h
  }.

Notation "x >>= f" := (bind x f) (at level 60).
Notation "x <- y ; f" := (y >>= (fun x => f)) 
    (at level 100, f at level 200, 
    format "'[v' x  '<-'  y ';' '/' f ']'").

Section Monads.

  Context `{TMonad T}.
  (*
  Section Monad_is_functor.
  
    Let T_fmap
    Global Instance monad_is_functor: TFunctor T :=
      fun `(f: A -> B) (t: T A) => x <- t; ret (f x).
  
  End Monad_is_functor.
  *)

  Section Monad_is_applicative.
  
    Let T_fzip := fun (A B: Type) (f: T (A -> B)) (t: T A)
                  => a <- t; g <- f; ret (g a).
    Let T_pure := @ret _ _.
    
    Notation "[ x ]" := (T_pure _ x).
    Notation "f $* a" := (T_fzip _ _  f a) 
                         (at level 60, right associativity).

    Local Definition T_pure_id : `(T_fzip A A (T_pure (A -> A) idmap) = idmap).
      intro; unfold T_fzip, T_pure.
      by_extensionality t.
      assert (p := fun a: A => 
                   (ret_unit_left (fun g => ret (g a)) idmap)^).
      apply path_forall in p.
      apply (ap (fun x => (t >>= x) = t)) in p.
      path_induction.
      exact (ret_unit_right t).
      Defined.
    
    Local Definition T_homomorphism : forall (A B : Type) (f : A -> B) 
                      (x : A), ([f] $* [x]) = [f x].
      intros. unfold T_fzip, T_pure.
      assert (p := ret_unit_left (fun a => g <- ret f; ret (g a)) x).
      assert (q := ret_unit_left (fun g => ret (g x)) f).
      path_induction; done.
      Defined.
    
    Local Definition T_interchange : 
            forall (A B : Type) (u : T (A -> B)) (x : A),
            u $* [x] = [fun g => g x] $* u.
      intros; unfold T_fzip, T_pure.
      assert (p := (ret_unit_left (fun a => g <- u; ret (g a)) x)^).
      assert (q := fun a: A -> B => 
              (ret_unit_left (fun g => ret (g a)) (fun g => g x))^).
      apply path_forall in q.
      path_induction.
      done.
      Defined.
    
    Local Definition T_composition : 
          forall (A B C: Type) (f: T(B -> C)) (g: T(A -> B)) (x: T A), 
          f $* (g $* x) = (([compose] $* f) $* g) $* x.
      intros; unfold T_pure, T_fzip.
      Admitted.

    Global Instance monad_is_applicative: TApplicative T
    := {| pure := T_pure; fzip := T_fzip; pure_id := T_pure_id;
        homomorphism := T_homomorphism; interchange := T_interchange;
        composition := T_composition |}.

  End Monad_is_applicative.
  
  Definition join {A: Type} (t: T (T A)): T A 
    := x <- t; x.

  Lemma join_is_action (A: Type): 
        join o (T $$ join) = join o (join (A:=T A)).
    unfold join, fmap. simpl.
    apply path_forall. unfold "_ == _". intro.
    f_ap.
    assert (p := fun a => inverse $ ret_unit_left (fun g => ret (g a)) 
          (fun t : T (T A) => x0 <- t; x0)).
    apply path_forall in p.
    induction p.
    Admitted.
    
  Lemma ret_is_unit (A: Type) (x: T A): join ((T $$ ret) x) = x.
  Admitted.

End Monads.

Section Algebras.

  (** We need to define a T-algebra on Type (regarding T as a functor, not as a monad). The most important case is `T = List`, `T_act ([X_1, .. , X_n]) := X_1 * .. * X_n`, but there are at least a few other variants (corresponding to commutative product on Type or the structure of commutative ring wrt +,* ). *)
  Context `{TMonad T}.
  Variable T_act: T Type -> Type.

  (** We regard the type family is_op as a predicate stating that a function `f: T A -> A` is a "virtual operation", i.e. it is an iterated composition of some deining set of primitive operations or their deformations. E.g. if A is a strict semigroup and T = List, then `m: T A -> A` is a tuple (m_0, m_1, .. , m_k, ..) of k-ary products `m_k: A^k -> A` and a virtual operation is a pair (h: T A -> A, p: h = m). Note that in this case all iterated compositions of m are trivially equal to m and thus we can define a composition of virtual operations, extending the usual one. In general there will be nontrivial paths between iterated compositions of m_i, thus we need to choose composition on `sig is_op` beforehand. *)
(*  Definition VirtualOp {A: Type} (is_op: (T A -> A) -> Type) := 
    exists (f: T A -> A), is_op f.*)

  Section Composition.
  
    Context {A: Type}.
    Variable is_op : (T A -> A) -> Type.

    (** Morally a point in this type corresponds to T h, where h is some virtual operation. In the case T = List such points are lists [f_1, .. , f_k] of operations with arities [n_1, .. , n_k]. *)
    Definition T_is_op: (T (T A) -> T A) -> Type :=
      let t_fam := T_act o (T $$ is_op)
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
  

  Record TAlg_map {A B: Type} (AT: TAlgebra A) (BT: TAlgebra B) :=
    {
      base_map: A -> B;
      op_map: forall (f: sig AT.(is_op)), { g: sig BT.(is_op) |
              g.1 o base_map = base_map o f.1 };
      compose_map: ???
    }.
    
End Algebras.