(* This is Yoneda's lemma in Coq? *)
(* which is derived from one in Scala by https://www.slideshare.net/100005930379759/scala-scala *)
(* NOTE that this is not a proof, but just an implication inside programming language *)

Require Import List String Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* f for object mapping and fmap for morphism mapping *)
(* ref. https://github.com/jwiegley/coq-haskell/blob/master/src/Data/Functor.v *)
Class EndoFunctor (f : Type -> Type) : Type := {
    fmap : forall {a b : Type}, (a -> b) -> f a -> f b
}.

(* Natural transformation: F and G are functors *)
Class Nat {f: Type -> Type} (F : EndoFunctor f) {g: Type -> Type} (G : EndoFunctor g) : Type := {
    trans : forall {x : Type}, (f x) -> (g x)
}.
Notation "F ~> G" := (Nat F G) (at level 28, left associativity, only parsing).

(* Seq functor *)
Instance SeqFunctor : EndoFunctor list := {
    fmap _ _ f l := List.map f l
}.

(* Const functor: always mapping to the specific object and the specific morphism *)
Definition const (X: Type) := nat.
Instance ConstFunctor : EndoFunctor const := {
    fmap _ _ _ := fun x => x
}.

(* a natural transformation from Seq functor to Const functor *)
Instance Length : SeqFunctor ~> ConstFunctor := {
    trans _ l := List.length l 
}.

(* from https://coq.inria.fr/library/Coq.Strings.String.html *)
Fixpoint string_of_list_ascii (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons ch s => String ch (string_of_list_ascii s)
     end.

(* a morphism mapped by functors *)
Open Scope char_scope.
Definition myf x := string_of_list_ascii (repeat "X" x).

Definition seq := [1;2;3].

(* Verify commutativity for specific instance *)
Goal trans (fmap myf seq) = fmap myf (trans seq).
Proof.
    auto.
Qed.

(* Verify commutativity *)
Goal forall x, trans (fmap myf x) = fmap myf (trans x).
Proof.
    induction x.
    - simpl. reflexivity.
    - simpl. simpl in IHx. rewrite IHx. reflexivity.
Qed.

(* Yoneda's lemma *)
Definition liftY {F: Type -> Type} (FF: EndoFunctor F) {X: Type} (x: F X) :=
    fun A => fun f: X -> A => @fmap F FF X A f x.

Definition lowerY {F: Type -> Type} (FF: EndoFunctor F) {X: Type} (f: forall A, (X -> A) -> F A) :=
    f X (fun x => x).

(* for specific instance *)
Goal seq = (lowerY _ (liftY _ seq)).
Proof.
    auto.
Qed.

(* for list nat, which means SeqFunctor and nat *)
Theorem lowerY_liftY_id:  forall l: list nat, l = (lowerY _ (liftY _ l)).
Proof.
    induction l.
    - auto.
    - unfold liftY in *. unfold lowerY in *.
      simpl in *. rewrite <- IHl. reflexivity.
Qed.

(* for inverse, too difficult for me *)
Goal forall n :(forall A, (nat -> A) -> list A), forall f,
    n nat f = (liftY _ (lowerY _ n)) nat f.
Proof.
    intros.
    unfold lowerY. unfold liftY.
    simpl.
    (* stucked at
       n nat f = map f (n nat (fun x : nat => x)) *)
Admitted.
