Require Import HoTT.
Require Import Functors.

Open Scope list_scope.

Generalizable Variables A B X Y f g x y z w T F.

Section List_is_monad.
  Notation T := list.
  Local Fixpoint bind (A B: Type) (X: T A) (f: A -> list B): list B
    := match X with
       | nil => nil
       | x :: xs => (f x) ++ (bind A B xs f)
       end.

  Local Definition ret (A: Type) (X: A): T A := X :: nil.
  
  Local Definition ret_unit_left : forall (A B : Type) (k : A -> T B) (a : A),
                    bind A B (ret A a) k = k a.
    intros; unfold bind, ret.
    SearchAbout "++".
  
  Local Definition ret_unit_right : forall (A : Type) (m : T A), 
                    bind A A m (ret A) = m.
  
  Local Definition bind_assoc : forall (A B C : Type) (m : T A) (k : A -> T B)
                   (h : B -> T C), bind A C m (fun x : A => 
                   bind B C (k x) h) = bind B C (bind A B m k) h.
  
  Global Instance list_is_monad : TMonad list
    := {|  |}

End List_is_monad.

Definition merge {X: Type} : list (list X) -> list X :=
  fix merge lists :=
  match lists with
  | nil => nil
  | xs :: lists => xs ++ (merge lists)
  end.

Fixpoint list_map {X Y: Type} (f: X -> Y) (xs: list X) : list Y := 
  match xs with
  | nil => nil
  | x :: xs' => (f x) :: (list_map f xs')
  end.

Section Assoc_Algebra.
  Notation Ends X := (list X -> X).

  Variable A : Type.

  Definition VirtualCompose (is_op : Ends A -> Type) := 
    let V := (exists f, is_op f) in
    forall (f g: V), exists (h: V), (g.1 o (list_map f.1) = h.1 o merge).
  
  Record Associative := 
  {
    is_op: Ends A -> Type;
    comp: VirtualCompose is_op;
    unique_operation: Contr (exists f, is_op f)
    }.
  
End Assoc_Algebra.

Arguments comp [_] _ _ _.
Arguments is_op [_] _ _.
Arguments unique_operation [_] _ .
Arguments VirtualCompose [A] _.

(* Note: we can reduce the structures in definition of A_00 algebras and
their maps from maps of type families to maps of elemets, i.e. a composition
in A_00 structure is a path p: m m = m concat, where m is some virtual 
operation. A functor is a map f: X -> Y with p: f m_X = m_Y f and preserving 
composition p. *)

Definition VirtualOp {X: Type} (A: Associative X) := 
  exists (f: list X -> X), A.(is_op) f.

Record Assoc_map {X Y: Type} (A: Associative X) (B: Associative Y) :=
  {
    base_map: X -> Y;
    operation_map: forall (f: VirtualOp A), exists (g: VirtualOp B),
                      g.1 o base_map = base_map o f.1;
    compose_map: 
  (** Simplicial objects: to associate simplicial object to monoid M, consider Hom( F_n , M), where F_n is a free monoid on n generators. Free monoid form a simplicial object, thus Hom(..) is cosimplicial. **)
  (** Simplicial category maps to FinSet (forget the ordering) and FinSet maps to Monoid via free monoid functor. Thus free monoids are cosimplicial.**)