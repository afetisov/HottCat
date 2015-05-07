Require Import HoTT.
Require Import HottCat.TFunctors.

Section Option_is_monad.
  Notation T := option.
  
  Local Definition T_bind (A B : Type) (x: T A) (f: A -> T B): T B
    := match x with
       | None => None
       | Some a => f a
       end.
  
  Local Definition T_ret: forall A : Type, A -> T A := Some.
  
  Local Definition T_ret_unit_left: forall (A B : Type) (k : A -> T B) 
        (a : A), T_bind A B (T_ret A a) k = k a.
    intros; auto. Defined.
  
  Local Definition T_ret_unit_right : forall (A : Type) (m : T A), 
        T_bind A A m (T_ret A) = m.
    intros; destruct m; auto.
    Defined.
  
  Local Definition T_bind_assoc : forall (A B C : Type) (m : T A) 
        (k : A -> T B) (h : B -> T C), T_bind A C m (fun x : A 
        => T_bind B C (k x) h) = T_bind B C (T_bind A B m k) h.
    intros; destruct m; auto.
    Defined.

  Global Instance option_is_monad: TMonad option
    := Build_TMonad option T_bind T_ret T_ret_unit_left 
        T_ret_unit_right T_bind_assoc.
  
End Option_is_monad.

Section Option_eq.
  Context {A: Type}.
  Implicit Types (x y: option A).
  
  Local Fixpoint option_eq (x y: option A): Type :=
    match x, y with
    | None, None => Unit
    | Some a, Some b => a = b
    | _, _ => Empty
    end.
  
  Infix "=opt" := option_eq (at level 75, right associativity).
  
  Local Definition option_encode {x y}: x = y -> x =opt y.
    induction 1; destruct x; done.
    Defined.
    
  Local Definition option_decode {x y}: x =opt y -> x = y.
    destruct x, y; simpl; induction 1; auto.
    Defined.
    
  Global Instance isequiv_option_encode {x y}: IsEquiv (@option_encode x y).
    refine (isequiv_adjointify option_encode option_decode _ _).
    - unfold Sect. 
      destruct x, y; unfold option_encode, option_decode; simpl; 
          intros; induction x; done.
    - unfold Sect, option_encode, option_decode; simpl; intros.
      path_induction. induction x; done.
    Defined.
  
  Definition equiv_path_opt {x y}: x = y <~> x =opt y
    := BuildEquiv _ _ option_encode isequiv_option_encode.
  
  Lemma error_ne_some (x: A): (error = Some x) -> Empty.
    intro p; apply (equiv_fun equiv_path_opt) in p.
    done. Qed.
  
End Option_eq.


