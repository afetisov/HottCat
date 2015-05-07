Require Import HoTT.


Open Scope list_scope.
Open Scope type_scope.

(** Standard notations for lists. 
In a special module to avoid conflicts. *)
Module ListNotations.
Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.
End ListNotations.

Import ListNotations.


  Fixpoint list_code {A: Type}(l l': list A) :=
    match l, l' with
    | [], [] => Unit
    | x::xs, y::ys => (x = y) /\ (list_code xs ys)
    | _, _ => Empty
    end.
  
  Infix "=list" := list_code (at level 70, right associativity).
  
  Fixpoint list_code_id {A: Type}(l: list A): l =list l :=
    match l with
    | [] => tt
    | x :: xs => (idpath, list_code_id xs)
    end.
  
  Definition list_encode {A: Type}(l l': list A): (l = l') -> (l =list l')
    := fun p => match p with | idpath => list_code_id _ end.

  Fixpoint list_decode {A: Type}(l l': list A): (l =list l') -> (l = l').
    induction l, l'; induction 1.
    exact idpath.
    f_ap.
    exact (list_decode A l l' snd).
    Defined.

  Global Instance isequiv_list_encode {A: Type}{l l': list A}: 
                                      IsEquiv (list_encode l l').
    refine (isequiv_adjointify (list_encode l l') (list_decode l l') _ _); revert l l'.
    - unfold Sect.
      (* Should make up some tactic to use here TODO *)
      pose (T := fun (l l' : list A) (x : l =list l') => list_encode l l' (list_decode l l' x) = x).
      refine (fix sect (l l': list A) (x : l =list l'): T l l' x:= _ ).
      unfold T; intros.
      induction l, l'; unfold list_encode, list_decode; simpl.
      * exact (path_contr _ _).
      * induction x.
      * induction x.
      * destruct x as [p Ix].
        apply (sect l l') in Ix.
