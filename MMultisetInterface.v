(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


Require Import RelationPairs.
Require Import MSetInterface.
Require Import Equalities.
Require Import SetoidPermutation.
Require Import MMultisets.Preliminary.


(** *  Signature of operations on multisets  **)

Module Type MMOps (E : DecidableType).

  Definition elt := E.t.
  Parameter t : Type.
  (** The types of elements and multisets. *)

  Parameter empty : t.
  (** The empty multiset. *)

  Parameter is_empty : t -> bool.
  (** Test whether a multiset is empty or not. *)

  Parameter multiplicity : elt -> t -> nat.
  (** [multiplicity x s] gives the number of occurences of [x] inside [s]. *)

  Parameter add : elt -> nat -> t -> t.
  (** [add x n s] returns a multiset containing all elements of s, plus [n] copies of [x]. *)
  (* If [n] is [0], should we return /exactly/ the original multiset? *)

  Parameter singleton : elt -> nat -> t.
  (** [singleton x n] returns the multiset containing only [n] copies of [x].
      It is [empty] if [n] is [0]. *)

  Parameter remove : elt -> nat -> t -> t.
  (** [remove x n s] returns a multiset containing all elements of s, minus [n] copies of [x].
      If the multiplicity of [x] in [s] is less than [n], we remove all the copies of [x] from [s]. *)

  Parameter union : t -> t -> t.
  (** Multiset union. *)

  Parameter inter : t -> t -> t.
  (** Multiset intersection. *)

  Parameter diff : t -> t -> t.
  (** Multiset difference. *)

  Parameter lub : t -> t -> t.
  (** Multiset lowest upper bound: the multiplicity of any [x] in [sup s1 s2] is the maximum of the multiplicities
  of [x] in [s1] and [s2]. *)

  Parameter equal : t -> t -> bool.
  (** [equal s1 s2] tests whether the multisets [s1] and [s2] are equal,
      that is, contain equal elements with equal multiplicities. *)

  Parameter subset : t -> t -> bool.
  (** [subset s1 s2] tests whether the multiset [s1] is a subset of the multiset [s2]. *)

  Parameter fold : forall {A : Type}, (elt -> nat -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN nN ... (f x2 n2 (f x1 n1 a))...)], where [x1 ... xN]
      are the distinct elements of [s] with respective positive multiplicities [n1 ... nN].
      The order in which the elements of [s] are presented to [f] is unspecified. *)

  Parameter for_all : (elt -> nat -> bool) -> t -> bool.
  (** [for_all p s] checks if all elements of the multiset (with their multiplicities) satisfy the predicate [p]. *)

  Parameter exists_ : (elt -> nat -> bool) -> t -> bool.
  (** [exists_ p s] checks if at least one element of the multiset (with its multiplicity)
      satisfies the predicate [p]. *)

  Parameter nfilter : (elt -> nat -> bool) -> t -> t.
  (** [nfilter p s] returns the multiset of all elements with multiplicity in [s] that satisfy the predicate [p]. *)

  Parameter filter : (elt -> bool) -> t -> t.
  (** [filter p s] returns the multiset of all elements in [s] that satisfy the predicate [p],
      keeping their multiplicity. *)

  Parameter npartition : (elt -> nat -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of multisets [(s1, s2)], where [s1] is the multiset of all the elements of [s]
      with multiplicity that satisfy the predicate [p], and [s2] is the multiset of all the elements of [s] with
      multiplicity that do not satisfy [p]. *)

  Parameter partition : (elt -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of multisets [(s1, s2)], where [s1] is the multiset of all the elements of [s]
      that satisfy the predicate [p], and [s2] is the multiset of all the elements of [s] that do not satisfy [p]. *)

  Parameter elements : t -> list (elt * nat).
  (** Return the list of all elements with multiplicity of the given multiset, in any order. *)

  Parameter support : t -> list elt.
  (** Return the list of all different elements without multiplicity of the given multiset, in any order. *)

  Parameter cardinal : t -> nat.
  (** Return the number of elements of a multiset, with multiplicity. *)

  Parameter size : t -> nat.
  (** Return the size of the support of a multiset,
      that is, the number of different elements (without multiplicity). *)

  Parameter choose : t -> option elt.
  (** Return one element of the given multiset, or [None] if the multiset is empty.
      Which element is chosen is unspecified: equal multisets could return different elements. *)
End MMOps.


(** *  Full signature for multisets  **)

Module Type MMultisetsOn (E : DecidableType).
  (** First, we ask for all the functions *)
  Include MMOps E.

  (** ** Logical predicates *)

  Definition In := fun x s => multiplicity x s > 0.

  Definition eq s s' := forall x, multiplicity x s = multiplicity x s'.
  Definition Subset s s' := forall x, multiplicity x s <= multiplicity x s'.
  Definition For_all (P : elt -> nat -> Prop) s := forall x, In x s -> P x (multiplicity x s).
  Definition Exists (P : elt -> nat -> Prop) s := exists x, In x s /\ P x (multiplicity x s).

  Global Notation "s  [=]  t" := (eq s t) (at level 70, no associativity, only parsing).
  Global Notation "m1  ≡  m2" := (eq m1 m2) (at level 70).
  Global Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity, only parsing).
  Global Notation "m1  ⊆  m2" := (Subset m1 m2) (at level 70).
  Global Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").

  (** ** Specifications of multiset operators *)

  Notation compatb := (Proper (E.eq ==> Logic.eq ==> @Logic.eq bool)) (only parsing).
  Declare Instance multiplicity_compat : Proper (E.eq ==> eq ==> Logic.eq) multiplicity.

  Declare Instance fold_compat A (eqA : A -> A -> Prop) `{Equivalence A eqA} :
    forall f, Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    Proper (eq ==> eqA ==> eqA) (fold f).

  Parameter equal_spec : forall s s', equal s s' = true <-> s [=] s'.
  Parameter subset_spec : forall s s', subset s s' = true <-> s [<=] s'.
  Parameter empty_spec : forall x, empty[x] = 0.
  Parameter is_empty_spec : forall s, is_empty s = true <-> s [=] empty.
  Parameter add_same : forall x n s, (add x n s)[x] = s[x] + n.
  Parameter add_other : forall x y n s, ~E.eq y x -> (add x n s)[y] = s[y].
  Parameter remove_same : forall x n s, (remove x n s)[x] = s[x] - n.
  Parameter remove_other : forall x y n s, ~E.eq y x -> (remove x n s)[y] = s[y].
  Parameter singleton_same : forall x n, (singleton x n)[x] = n.
  Parameter singleton_other : forall x y n, ~E.eq y x -> (singleton x n)[y] = 0.
  Parameter union_spec : forall x s s', (union s s')[x] = s[x] + s'[x].
  Parameter inter_spec : forall x s s', (inter s s')[x] = min s[x] s'[x].
  Parameter diff_spec : forall x s s', (diff s s')[x] = s[x] - s'[x].
  Parameter lub_spec : forall x s s', (lub s s')[x] = max s[x] s'[x].
  Parameter fold_spec : forall (A : Type) s (i : A) (f : elt -> nat -> A -> A),
    fold f s i = fold_left (fun acc xn => f (fst xn) (snd xn) acc) (elements s) i.
  Parameter cardinal_spec : forall s, cardinal s = fold (fun x n acc => n + acc) s 0.
  Parameter size_spec : forall s, size s = length (support s).
  Parameter nfilter_spec : forall f x s, compatb f -> (nfilter f s)[x] = if f x s[x] then s[x] else 0.
  Parameter filter_spec : forall f x s, Proper (E.eq ==> Logic.eq) f -> (filter f s)[x] = if f x then s[x] else 0.
  Parameter for_all_spec : forall f s, compatb f -> (for_all f s = true <-> For_all (fun x n => f x n = true) s).
  Parameter exists_spec : forall f s, compatb f -> (exists_ f s = true <-> Exists (fun x n => f x n = true) s).
  Parameter npartition_spec_fst : forall f s, compatb f -> fst (npartition f s) [=] nfilter f s.
  Parameter npartition_spec_snd : forall f s, compatb f ->
    snd (npartition f s) [=] nfilter (fun x n => negb (f x n)) s.
  Parameter partition_spec_fst : forall f s, Proper (E.eq ==> Logic.eq) f -> fst (partition f s) [=] filter f s.
  Parameter partition_spec_snd : forall f s, Proper (E.eq ==> Logic.eq) f ->
    snd (partition f s) [=] filter (fun x => negb (f x)) s.

  Definition eq_pair := RelProd E.eq (@Logic.eq nat).
  Definition eq_elt := RelCompFun E.eq (@fst E.t nat).

  Instance eq_pair_equiv : Equivalence eq_pair.
  Proof. split.
  intros [x n]. now split; hnf.
  intros [x n] [y m] [H1 H2]; split; hnf in *; now auto.
  intros ? ? ? [? ?] [? ?]. split. hnf in *. now transitivity (fst y). now transitivity (snd y).
  Qed.

  Parameter elements_spec : forall x n s, InA eq_pair (x, n) (elements s) <-> s[x] = n /\ n > 0.
  Parameter elements_NoDupA : forall s, NoDupA eq_elt (elements s).
  Parameter support_spec : forall x s, InA E.eq x (support s) <-> In x s.
  Parameter support_NoDupA : forall s, NoDupA E.eq (support s).

  Parameter choose_Some : forall x s, choose s = Some x -> In x s.
  Parameter choose_None : forall s, choose s = None <-> s [=] empty.
End MMultisetsOn.


(** **  Signature on an ordered type  **)

Module Type Sord (E : OrderedType).

  (** We include all the common interface *)
  Include MMultisetsOn E.

  (** Orders on elements *)
  Definition lt_elt (xn yp : elt * nat) := E.lt (fst xn) (fst yp).

  Parameter elements_Sorted : forall s, Sorted lt_elt (elements s).

  (** Multiset ordering is left as future works *)

(*
  Include HasLt <+ IsEq <+ IsStrOrder.

  Definition cmp := Nat.eqb.

  Parameter compare : t -> t -> comparison.

  Parameter compare_spec : forall m1 m2, CompSpec eq lt m1 m2 (compare m1 m2).
*)
End Sord.
