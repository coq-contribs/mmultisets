(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


Require Import Omega.
Require Import Arith.Div2.
Require Import Reals.
Require Import List.
Require Import Morphisms.
Require Import Sorting.Permutation.
Require Import Psatz.
Require Import SetoidList.
Require Export SetoidPermutation.


Set Implicit Arguments.
Require Import Bool.


Lemma nat_compare_Eq_comm : forall n m, nat_compare n m = Eq <-> nat_compare m n = Eq.
Proof. intros n m. do 2 rewrite nat_compare_eq_iff. now split. Qed.

Lemma nat_compare_Lt_Gt : forall n m, nat_compare n m = Lt <-> nat_compare m n = Gt.
Proof. intros n m. rewrite <- nat_compare_lt, <- nat_compare_gt. now split. Qed.

Definition injective {A B : Type} eqA eqB (f : A -> B) := (forall x y, eqB (f x) (f y) -> eqA x y).

Definition transpose2 {A B C : Type} eqC (f : A -> B -> C -> C) :=
  forall x y x' y' z, eqC (f x x' (f y y' z)) (f y y' (f x x' z)).

Definition additive2 {A B : Type} eqB (f : A -> nat -> B -> B) :=
  forall x n p z, eqB (f x n (f x p z)) (f x (n + p) z).

Instance compose_compat {A B C : Type} eqA eqB eqC : forall (f : A -> B) (g : B -> C),
  Proper (eqA ==> eqB) f -> Proper (eqB ==> eqC) g -> Proper (eqA ==> eqC) (fun x => g (f x)).
Proof. intros f g Hf Hg x y Heq. now apply Hg, Hf. Qed.

Instance compose2_compat {A B C D : Type} eqA eqB eqC eqD : forall (f : A -> B) (g : B -> C -> D),
  Proper (eqA ==> eqB) f -> Proper (eqB ==> eqC ==> eqD) g -> Proper (eqA ==> eqC ==> eqD) (fun x => g (f x)).
Proof. intros f g Hf Hg x y Heq. now apply Hg, Hf. Qed.

Instance compose3_compat {A B C D E : Type} eqA eqB eqC eqD eqE : forall (f : A -> B) (g : B -> C -> D -> E),
  Proper (eqA ==> eqB) f -> Proper (eqB ==> eqC ==> eqD ==> eqE) g ->
  Proper (eqA ==> eqC ==> eqD ==> eqE) (fun x => g (f x)).
Proof. intros f g Hf Hg x y Heq. now apply Hg, Hf. Qed.

Lemma le_neq_lt : forall m n : nat, n <= m -> n <> m -> n < m.
Proof. intros n m Hle Hneq. now destruct (le_lt_or_eq _ _ Hle). Qed.

Lemma min_is_0 : forall n m, min n m = 0 <-> n = 0 \/ m = 0.
Proof. intros [| n] [| m]; intuition. discriminate. Qed.

Lemma max_is_0 : forall n m, max n m = 0 <-> n = 0 /\ m = 0.
Proof. intros [| n] [| m]; intuition; discriminate. Qed.

Lemma Bleb_refl : forall x, Bool.leb x x.
Proof. intros [|]; simpl; auto. Qed.


(** *  Some results on Lists  **)

Section List_results.
Context (A B C : Type).
Context (eqA eqA' : relation A) (eqB : relation B).
Context (HeqA : Equivalence eqA) (HeqB : Equivalence eqB).

Lemma length_1 : forall l : list A, length l = 1 <-> exists x, l = x :: nil.
Proof. intros [| ? [| ? ?]]; simpl; split; try discriminate; eauto; intros [? ?]; discriminate. Qed.

Lemma In_InA_weak : forall x l, In x l -> InA eqA x l.
Proof.
intros x l Hin. induction l.
- inversion Hin.
- destruct Hin. subst. now left. right. auto.
Qed.

Lemma PermutationA_subrelation_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@PermutationA A).
Proof.
intros eqA1 eqA2 Hrel l1 l2 H12 l3 l4 H34 Hperm. subst. induction Hperm.
- constructor.
- constructor. now apply Hrel. assumption.
- constructor 3.
- now constructor 4 with l₂.
Qed.

Lemma NoDupA_2 : forall x y, ~eqA x y -> NoDupA eqA (x :: y :: nil).
Proof.
intros x y Hdiff. constructor.
  intro Habs. inversion_clear Habs.
    now elim Hdiff.
    inversion H.
  apply NoDupA_singleton.
Qed.

Lemma NoDupA_3 : forall x y z, ~eqA x y -> ~eqA y z -> ~eqA x z -> NoDupA eqA (x :: y :: z :: nil).
Proof.
intros x y z Hxy Hyz Hxz. constructor.
  intro Habs. inversion_clear Habs. contradiction. inversion_clear H. contradiction. inversion_clear H0.
  now apply NoDupA_2.
Qed.

Global Instance PermutationA_eq_compat : Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@PermutationA A).
Proof.
intros f g Hfg l1 l2 Hl12 l3 l4 Hl34. subst l4 l2. split; intro H.
+ induction H.
  - constructor.
  - constructor. now rewrite <- (Hfg _ _ (eq_refl x₁) _ _ (eq_refl x₂)). assumption.
  - constructor 3.
  - now constructor 4 with l₂.
+ induction H.
  - constructor.
  - constructor. now rewrite (Hfg _ _ (eq_refl x₁) _ _ (eq_refl x₂)). assumption.
  - constructor 3.
  - now constructor 4 with l₂.
Qed.

Global Instance eqlistA_PermutationA_subrelation : subrelation (eqlistA eqA) (PermutationA eqA).
Proof. intros l l' Hl. induction Hl; constructor; assumption. Qed.

Theorem InA_map_iff : forall f, Proper (eqA ==> eqB) f ->
  forall l y, InA eqB y (map f l) <-> exists x, eqB (f x) y /\ InA eqA x l.
Proof.
intros f Hf l y. induction l.
+ split; intro Hin.
  - inversion Hin.
  - destruct Hin as [x [_ Hin]]. inversion Hin.
+ split; intro Hin.
  - inversion_clear Hin.
      exists a. split. now symmetry. now left.
      rewrite IHl in H. destruct H as [x [Hx H]]. exists x; auto.
  - destruct Hin as [x [Hx Hin]]. inversion_clear Hin.
      left. now rewrite <- Hx, H.
      simpl. right. rewrite IHl. exists x. now split.
Qed.

Lemma removeA_out eq_dec : forall x l, ~InA eqA x l -> @removeA A eqA eq_dec x l = l.
Proof.
intros x l Hin. induction l; simpl.
+ reflexivity.
+ destruct (eq_dec x a).
  - elim Hin. now left.
  - f_equal. apply IHl. intro Habs. apply Hin. now right.
Qed.

Lemma removeA_InA_out eq_dec : forall x y l, ~eqA y x ->
  (InA eqA x (@removeA A eqA eq_dec y l) <-> InA eqA x l).
Proof.
intros x y l Hxy. induction l. reflexivity.
simpl. destruct (eq_dec y a).
  subst. rewrite IHl. split; intro H. now right. inversion_clear H.
    elim Hxy. now transitivity a.
    assumption.
  split; intro H; inversion_clear H; (now left) || right; now rewrite IHl in *.
Qed.
Global Arguments removeA_InA_out eq_dec [x] y l _.

Theorem removeA_InA_iff_strong eqA'' eq_dec : subrelation eqA'' eqA ->
  forall x y l, InA eqA'' x (@removeA A eqA eq_dec y l) <-> InA eqA'' x l /\ ~eqA x y.
Proof.
intros Hsub x y l. induction l as [| a l].
* split; intro Habs. inversion Habs. destruct Habs as [Habs _]. inversion Habs.
* simpl. destruct (eq_dec y a) as [Heq | Hneq].
  + rewrite IHl. intuition. inversion_clear H2. apply Hsub in H0. now elim H3; transitivity a. assumption.
  + split; intro Hin.
    - inversion_clear Hin.
        split. now left. rewrite H. intro. now apply Hneq.
        rewrite IHl in H. destruct H. split; trivial. now right.
    - destruct Hin as [Hin ?]. inversion_clear Hin.
        now left.
        right. rewrite IHl. now split.
Qed.

Theorem removeA_InA_iff eq_dec : forall x y l, InA eqA x (@removeA A eqA eq_dec y l) <-> InA eqA x l /\ ~eqA x y.
Proof. apply (removeA_InA_iff_strong eq_dec). reflexivity. Qed.

Lemma removeA_InA_weak eq_dec : forall x y l, InA eqA' x (@removeA A eqA eq_dec y l) -> InA eqA' x l.
Proof.
intros x y l Hin. induction l; simpl in *.
+ rewrite InA_nil in Hin. elim Hin.
+ destruct (eq_dec y a) as [Heq | Heq].
  - auto.
  - inversion_clear Hin; auto.
Qed.

Global Instance removeA_el_compat eq_dec : Proper (eqA ==> eq ==> eq) (@removeA A eqA eq_dec).
Proof.
intros x y Hxy l l' ?. subst l'. induction l; simpl.
+ reflexivity.
+ destruct (eq_dec x a) as [Heqx | Hneqx], (eq_dec y a) as [Heqy | Hneqy].
  - apply IHl.
  - elim Hneqy. now rewrite <- Hxy.
  - elim Hneqx. now rewrite Hxy.
  - f_equal. apply IHl.
Qed.

Global Instance removeA_Perm_compat eq_dec :
  Proper (eqA ==> PermutationA eqA ==> PermutationA eqA) (@removeA A eqA eq_dec).
Proof.
intros x y ? l1 l2 Hl. subst. induction Hl.
+ constructor.
+ simpl. destruct (eq_dec x x₁) as [Heq₁ | Hneq₁], (eq_dec y x₂) as [Heq₂ | Hneq₂].
  - assumption.
  - elim Hneq₂. now rewrite <- H, Heq₁.
  - elim Hneq₁. now rewrite H, Heq₂.
  - now apply PermutationA_cons.
+ simpl. destruct (eq_dec x x0), (eq_dec y y0), (eq_dec y x0), (eq_dec x y0);
  try (now elim n; rewrite H) || (now elim n; rewrite <- H).
  - now erewrite removeA_el_compat.
  - constructor. reflexivity. now erewrite removeA_el_compat.
  - elim n0. now rewrite <- H.
  - constructor. reflexivity. now erewrite removeA_el_compat.
  - elim n1. now rewrite H.
  - elim n0. now rewrite <- H.
  - etransitivity. constructor 3. repeat constructor; reflexivity || now erewrite removeA_el_compat.
+ constructor 4 with (removeA eq_dec y l₂).
  - assumption.
  - transitivity (removeA (eqA:=eqA) eq_dec x l₂). now erewrite removeA_el_compat. assumption.
Qed.

Lemma removeA_app eq_dec : forall (x : A) l1 l2,
  @removeA A eqA eq_dec x (l1 ++ l2) = removeA eq_dec x l1 ++ removeA eq_dec x l2.
Proof.
intros x l1 l2. induction l1. reflexivity. simpl.
destruct (eq_dec x a). apply IHl1. simpl. f_equal. apply IHl1.
Qed.

Corollary removeA_inside_in eq_dec :
  forall (x : A) l1 l2, @removeA A eqA eq_dec x (l1 ++ x :: l2) = removeA eq_dec x l1 ++ removeA eq_dec x l2.
Proof. intros x ? ?. rewrite removeA_app. simpl. destruct (eq_dec x x) as [| Hneq]; trivial. now elim Hneq. Qed.

Corollary removeA_inside_out eq_dec : forall (x y : A) l1 l2,
  ~eqA x y -> @removeA A eqA eq_dec x (l1 ++ y :: l2) = removeA eq_dec x l1 ++ y :: removeA eq_dec x l2.
Proof. intros x y ? ? ?. rewrite removeA_app. simpl. destruct (eq_dec x y). contradiction. reflexivity. Qed.

Lemma removeA_idempotent eq_dec : forall x l, @removeA A eqA eq_dec x (removeA eq_dec x l) = removeA eq_dec x l.
Proof.
intros x l. induction l.
+ reflexivity.
+ simpl. destruct (eq_dec x a) eqn:Hx.
  - assumption.
  - simpl. rewrite Hx. now rewrite IHl.
Qed.

Lemma removeA_comm eq_dec : forall (x y : A) l,
  @removeA A eqA eq_dec x (removeA eq_dec y l) = removeA eq_dec y (removeA eq_dec x l).
Proof.
intros x y l. induction l.
  reflexivity.
  simpl. destruct (eq_dec y a) eqn:Hy, (eq_dec x a) eqn:Hx; simpl;
  try rewrite Hx; try rewrite Hy; simpl; now rewrite IHl.
Qed.

Lemma removeA_length_le eq_dec : forall l (x : A), length (@removeA A eqA eq_dec x l) <= length l.
Proof.
intros l x. induction l; simpl.
  reflexivity.
  destruct (eq_dec x a); simpl; omega.
Qed.

Lemma removeA_NoDupA eq_dec : forall x l, NoDupA eqA l -> NoDupA eqA (@removeA A eqA eq_dec x l).
Proof.
intros x l Hl. induction Hl; simpl.
+ constructor.
+ destruct (eq_dec x x0).
  - assumption.
  - constructor; trivial. intro Habs. apply H. eapply removeA_InA; eassumption.      
Qed.

Global Instance InA_impl_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof.
intros R1 R2 HR x y Hxy l l2 Hl Hin. subst y l2. induction l.
  now inversion Hin.
  inversion_clear Hin.
    constructor. now apply HR.
    constructor 2. now apply IHl.
Qed.

Lemma PermutationA_nil : forall l, PermutationA eqA l nil -> l = nil.
Proof.
intros l Hl. destruct l.
  reflexivity.
  exfalso. rewrite <- InA_nil. rewrite (PermutationA_equivlistA HeqA).
    now left.
    symmetry. eassumption.
Qed.

Global Instance InA_compat : Proper (eqA ==> equivlistA eqA ==> iff) (InA eqA).
Proof.
intros x y Hxy l1 l2 Hl. split; intro H; eapply InA_eqA; try eassumption.
  now rewrite <- Hl.
  symmetry. eassumption.
  now rewrite Hl.
Qed.

Global Instance InA_perm_compat : Proper (eqA ==> PermutationA eqA ==> iff) (InA eqA).
Proof. intros x y Hxy l1 l2 Hl. now apply InA_compat; try apply PermutationA_equivlistA. Qed.

Lemma PermutationA_InA_inside : forall (x : A) l l',
  PermutationA eqA l l' -> InA eqA x l -> exists l1 y l2, eqA x y /\ l' = l1 ++ y :: l2.
Proof. intros x l l' Hperm Hin. rewrite Hperm in Hin. apply (InA_split Hin). Qed.

Lemma PermutationA_cons_split : forall (x : A) l l',
  PermutationA eqA (x :: l) l' -> exists l'', PermutationA eqA l' (x :: l'').
Proof.
intros x l l' Hperm. assert (Hin : InA eqA x l'). { rewrite <- Hperm. now left. }
symmetry in Hperm. destruct (PermutationA_InA_inside Hperm Hin) as [l1 [y [l2 [Heq Hll]]]].
exists (l1 ++ l2). rewrite Hperm, Hll. etransitivity. symmetry. apply (PermutationA_middle _).
constructor. now symmetry. reflexivity.
Qed.

Theorem PermutationA_ind_bis :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x₁ x₂ l l', eqA x₁ x₂ -> PermutationA eqA l l' -> P l l' -> P (x₁ :: l) (x₂ :: l')) ->
   (forall x y l l', PermutationA eqA l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationA eqA l l' -> P l l' -> PermutationA eqA l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationA eqA l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1; auto.
    apply Hswap; auto.
      reflexivity.
      induction l; auto. now apply Hskip.
    now apply Htrans with l₂.
Qed.

Ltac break_list l x l' H := destruct l as [| x l']; inversion H; subst; simpl in *.

Theorem PermutationA_app_inv : forall (l1 l2 l3 l4:list A) a,
  PermutationA eqA (l1++a::l2) (l3++a::l4) -> PermutationA eqA (l1++l2) (l3 ++ l4).
Proof.
  set (P l l' :=
         forall a b l1 l2 l3 l4, eqA a b -> l=l1++a::l2 -> l'=l3++b::l4 -> PermutationA eqA (l1++l2) (l3++l4)).
  cut (forall l l', PermutationA eqA l l' -> P l l').
  intros; apply (H _ _ H0 a a); auto. reflexivity.
  intros; apply (PermutationA_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto.
+ (* nil *)
  intros; destruct l1; simpl in *; discriminate.
+ (* skip *)
  intros x x' l l' Heq H IH; intros.
  break_list l1 c l1' H1; break_list l3 d l3' H2.
  - now auto. 
  - rewrite H. symmetry. etransitivity.
      constructor 2. transitivity a. symmetry. apply Heq. apply H0. reflexivity.
      now apply PermutationA_middle.
  - rewrite <- H. etransitivity.
      constructor 2. transitivity b. apply Heq. symmetry. apply H0. reflexivity.
      now apply PermutationA_middle.
  - rewrite (IH a _ _ _ _ _ H0 eq_refl eq_refl). now constructor 2.
+ (* contradict *)
  intros x y l l' Hp IH; intros.
  break_list l1 c l1' H0; break_list l3 d l3' H1.
  - now constructor 2.
  - break_list l3' c l3'' H4.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. now rewrite Hp, H. refine _. 
  - break_list l1' d l1'' H0.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. now rewrite <- H, Hp. refine _. 
  - break_list l3' e l3'' H1; break_list l1' g l1'' H4.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. rewrite permA_swap, <- H. now constructor 2. refine _.
      rewrite permA_swap, PermutationA_middle, H. now constructor 2. refine _.
      now rewrite permA_swap, (IH a _ _ _ _ _ H eq_refl eq_refl).
+ (* trans *)
  intros.
  destruct (@InA_split _ eqA l' a) as [l'1 [y [l'2 [H7 H6]]]].
  - rewrite <- H. subst l. rewrite InA_app_iff. now right; left.
  - apply permA_trans with (l'1++l'2).
      apply (H0 _ _ _ _ _ _ H7 H4 H6).
      rewrite H7 in H3. apply (H2 _ _ _ _ _ _ H3 H6 H5).
Qed.

Theorem PermutationA_cons_inv :
   forall l l' (a : A), PermutationA eqA (a::l) (a::l') -> PermutationA eqA l l'.
Proof. intros; exact (PermutationA_app_inv nil l nil l' a H). Qed.

Global Instance PermutationA_length : Proper (PermutationA eqA ==> Logic.eq) (@length A).
Proof.
intro l. induction l; intros l' Hperm.
  symmetry in Hperm. apply PermutationA_nil in Hperm. now subst.
  assert (Hp := @PermutationA_InA_inside a _ _ Hperm).
  destruct Hp as [l1 [y [l2 [Heq1 Heq2]]]]. now left. subst l'.
  rewrite app_length. simpl. rewrite <- plus_n_Sm. f_equal. rewrite <- app_length.
  apply IHl. apply PermutationA_cons_inv with a.
  transitivity (l1 ++ y :: l2). assumption. etransitivity. symmetry. apply PermutationA_middle. assumption.
  constructor. now symmetry. reflexivity.
Qed.

Lemma PermutationA_NoDupA : forall (l l' : list A), PermutationA eqA l l' -> NoDupA eqA l -> NoDupA eqA l'.
Proof.
intros l l' Hperm. induction Hperm; intro Hdup.
+ trivial.
+ inversion_clear Hdup. constructor.
    intro Habs. apply H0. now rewrite Hperm, H.
    now apply IHHperm.
+ inversion_clear Hdup. inversion_clear H0. constructor.
    intros Habs. inversion_clear Habs. apply H. now left. contradiction.
    constructor. intro Habs. apply H. now right. assumption.
+ auto.
Qed.

Global Instance PermutationA_NoDupA_compat : Proper (PermutationA eqA ==> iff) (NoDupA eqA).
Proof. now repeat intro; split; apply PermutationA_NoDupA. Qed.

Lemma PermutationA_length1 : forall x l, PermutationA eqA l (x :: nil) -> eqlistA eqA l (x :: nil).
Proof.
intros x l Hperm. destruct l as [| a [| b l]].
- symmetry in Hperm. apply PermutationA_nil in Hperm. discriminate Hperm.
- repeat constructor. apply PermutationA_InA_inside with a _ _ in Hperm; try now left.
  destruct Hperm as [l1 [y [l2 [Heq Hl]]]].
  destruct l1 as [| ? [| ? ?]], l2 as [| ? ?]; try discriminate Hl. inversion_clear Hl. assumption.
- apply PermutationA_length in Hperm. simpl in Hperm. omega.
Qed.

Lemma NoDupA_strengthen : forall l, subrelation eqA eqA' -> NoDupA eqA' l -> NoDupA eqA l.
Proof.
intros l HAB Hl. induction l.
  constructor.
  inversion_clear Hl. constructor.
    intro Habs. apply H. clear -Habs HAB. induction Habs.
      left. now apply (HAB a y).
      now right.
    now apply IHl.
Qed.

Global Instance fold_left_start : forall f, Proper (eqB ==> eqA ==> eqB) f ->
  forall l, Proper (eqB ==> eqB) (fold_left f l).
Proof.
intros f Hf l. induction l; intros i1 i2 Hi; simpl.
  assumption.
  rewrite IHl. reflexivity. now rewrite Hi.
Qed.

Global Instance fold_left_symmetry_PermutationA : forall (f : B -> A -> B),
  Proper (eqB ==> eqA ==> eqB) f -> (forall x y z, eqB (f (f z x) y) (f (f z y) x)) ->
  Proper (PermutationA eqA ==> eqB ==> eqB) (fold_left f).
Proof.
intros f Hfcomm Hf l1 l2 perm. induction perm; simpl.
- now repeat intro.
- intros ? ? Heq. rewrite H, Heq. now apply IHperm.
- intros ? ? Heq. now rewrite Hf, Heq.
- repeat intro. etransitivity. now apply IHperm1. now apply IHperm2.
Qed.

Global Instance fold_left_compat : forall f, Proper (eqB ==> eqA ==> eqB) f ->
  Proper (eqlistA eqA ==> eqB ==> eqB) (fold_left f).
Proof.
intros (*A' B' eqA2 eqB2*) f Hf l1 l2 eq. induction eq as [| ? ? ? ? Hx Hl IHeq].
+ repeat intro. simpl. assumption.
+ intros a b Hab. simpl. apply IHeq. apply Hf; assumption.
Qed.

Global Instance PermutationA_map : forall f, Proper (eqA ==> eqB) f ->
  Proper (PermutationA eqA ==> PermutationA eqB) (map f).
Proof.
intros f Hf l l' perm. induction perm; simpl.
  reflexivity.
  constructor 2. now rewrite H. now apply IHperm.
  now constructor 3.
  now transitivity (map f l₂).
Qed.

Lemma HdRel_app : forall l1 l2 R (a : A), HdRel R a l1 -> HdRel R a l2 -> HdRel R a (l1++l2).
Proof. induction l1; simpl; auto. intros. inversion_clear H. now constructor. Qed.

Lemma sort_app : forall R,
  forall l1 l2 : list A, sort R l1 -> sort R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> sort R (l1 ++ l2).
Proof.
induction l1; simpl in *; intuition. constructor.
+ apply IHl1.
  - now inversion_clear H.
  - assumption.
  - intros. apply H1. now right. assumption.
+ apply HdRel_app.
  - now inversion H.
  - destruct l2; constructor. apply H1; now left.
Qed.

Lemma NoDupA_dec : (forall x y : A, {eqA x y} + {~eqA x y}) -> forall l : list A, {NoDupA eqA l} + {~NoDupA eqA l}.
Proof.
intros eq_dec l. induction l. now left; constructor.
destruct IHl as [Hbad | Hok].
  destruct (InA_dec eq_dec a l).
    right. intro Habs. inversion_clear Habs. contradiction.
    left. now constructor.
  right. intro Habs. inversion_clear Habs. contradiction.
Qed.

Lemma PermutationA_split : forall x l, InA eqA x l -> exists l', PermutationA eqA l (x :: l').
Proof.
intros x l Hin. induction l; inversion_clear Hin.
  exists l. now rewrite H.
  apply IHl in H. destruct H as [l' Hperm]. exists (a :: l'). transitivity (a :: x :: l').
    now rewrite <- Hperm.
    constructor 3.
Qed.

Lemma inclA_app : forall x y l1 l2, eqA x y -> inclA eqA l1 l2 -> inclA eqA (x :: l1) (y :: l2).
Proof.
intros x y l1 l2 Heq Hincl z Hin. inversion_clear Hin.
- left. now transitivity x.
- right. now apply Hincl.
Qed.

Global Instance inclA_PermutationA_compat : Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (inclA eqA).
Proof. intros ? ? Hperm1 ? ? Hperm2. unfold inclA. setoid_rewrite Hperm1. setoid_rewrite Hperm2. reflexivity. Qed.

Lemma inclA_app_inv : forall x y l1 l2,
  ~InA eqA x l1 -> eqA x y -> inclA eqA (x :: l1) (y :: l2) -> inclA eqA l1 l2.
Proof.
intros x y l1 l2 Hx Heq Hincl z Hin.
assert (Hin' : InA eqA z (x :: l1)) by now right. apply Hincl in Hin'.
inversion_clear Hin'; trivial. elim Hx. now rewrite Heq, <- H.
Qed.

Lemma inclA_length : forall l1 l2, NoDupA eqA l1 -> inclA eqA l1 l2 -> length l1 <= length l2.
Proof.
intro l1. induction l1 as [| x l]; intros l2 Hnodup Hle.
+ auto with arith.
+ assert (Hin : InA eqA x l2). { apply Hle. now left. }
  apply PermutationA_split in Hin. destruct Hin as [l' Hin]. rewrite Hin. simpl. apply le_n_S. apply IHl.
  - now inversion Hnodup.
  - intros y Hy. rewrite Hin in Hle. inversion_clear Hnodup. apply inclA_app_inv in Hle; auto. reflexivity.
Qed.

Lemma not_NoDupA : (forall x y, {eqA x y} + {~eqA x y} ) ->
 forall l, ~NoDupA eqA l <-> exists (x : A) l', PermutationA eqA l (x :: x :: l').
Proof.
intros eq_dec l. split; intro Hl.
+ induction l.
    elim Hl. now constructor.
    destruct (InA_dec eq_dec a l) as [Hin | Hnin].
      exists a. apply PermutationA_split in Hin. destruct Hin as [l' Hperm]. exists l'. now rewrite Hperm.
      destruct IHl as [x [l' Hperm]].
        intro Habs. apply Hl. now constructor.
        exists x. exists (a :: l'). rewrite Hperm. transitivity (x :: a :: x :: l').
          now constructor 3.
          apply PermutationA_cons. reflexivity. constructor 3.
+ destruct Hl as [x [l' Hperm]]. rewrite Hperm. intro Habs. inversion_clear Habs. apply H. now left.
Qed.

Theorem PermutationA_rev : forall l, PermutationA eqA l (rev l).
Proof.
induction l; simpl.
+ reflexivity.
+ change (a :: l) with ((a :: Datatypes.nil) ++ l).
  rewrite PermutationA_app_comm; trivial. now apply PermutationA_app.
Qed.

Theorem partition_filter : forall (f : A -> bool) l, partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
intros f l. induction l as [| a l]; simpl.
  reflexivity.
  rewrite IHl. now destruct (f a).
Qed.

Corollary partition_fst_In : forall (x : A) f l, In x (fst (partition f l)) <-> In x l /\ f x = true.
Proof. intros. rewrite partition_filter. apply filter_In. Qed.

Corollary partition_snd_In : forall (x : A) f l, In x (snd (partition f l)) <-> In x l /\ f x = false.
Proof. intros. rewrite partition_filter. rewrite <- negb_true_iff. apply filter_In. Qed.

Theorem partition_length : forall f (l : list A),
  length (fst (partition f l)) + length (snd (partition f l)) = length l.
Proof.
intros f l. rewrite partition_filter in *. induction l; simpl.
+ reflexivity.
+ destruct (f a); simpl.
  - f_equal. apply IHl.
  - rewrite <- plus_n_Sm. f_equal. apply IHl.
Qed.

Corollary filter_length : forall f (l : list A),
  length (filter f l) = length l - length (filter (fun x => negb (f x)) l).
Proof. intros. apply plus_minus. rewrite <- (partition_length f), partition_filter. simpl. apply plus_comm. Qed.

Lemma map_cond_Permutation : forall (f : A -> bool) (g₁ g₂ : A -> B) l,
  Permutation (map (fun x => if f x then g₁ x else g₂ x) l)
              (map g₁ (filter f l) ++ map g₂ (filter (fun x => negb (f x)) l)).
Proof.
intros f ? ? l. induction l; simpl.
+ reflexivity.
+ destruct (f a); simpl.
  - apply Permutation_cons; trivial.
  - rewrite IHl. apply Permutation_middle.
Qed.

Theorem Forall_dec : forall P (Pdec : forall x : A, {P x} + {~P x}), forall l, {Forall P l} + {~Forall P l}.
Proof.
intros P Pdec l. induction l; simpl.
+ left. constructor.
+ destruct (Pdec a) as [Ha | Ha].
  - destruct IHl as [Hok | Hko].
      left. now constructor.
      right. intros Habs. inversion_clear Habs. contradiction.
  - right. intros Habs. inversion_clear Habs. contradiction.
Qed.

Lemma fold_left_map : forall (f : C -> B -> C) (g : A -> B) (l : list A) (x : C),
  fold_left f (map g l) x = fold_left (fun acc x => f acc (g x)) l x.
Proof.
intros f g l. induction l; intro x; simpl.
  reflexivity.
  now rewrite IHl.
Qed.

Lemma fold_left_cons_length_aux : forall (f : A -> B) l1 l2,
  length (fold_left (fun acc x => f x :: acc) l1 l2) = length l1 + length l2.
Proof.
intros f l1. induction l1; intro l2; simpl.
  reflexivity.
  rewrite IHl1. simpl. omega.
Qed.

Corollary fold_left_cons_length : forall (f : A -> B) l,
  length (fold_left (fun acc x => f x :: acc) l nil) = length l.
Proof. intros. rewrite fold_left_cons_length_aux. simpl. omega. Qed.

Lemma NoDupA_inj_map :
  forall (f : A -> B) (l : list A), Proper (eqA ==> eqB) f -> injective eqA eqB f ->
  (NoDupA eqB (map f l) <-> NoDupA eqA l).
Proof.
intros f l Hf Hinj. induction l; simpl.
+ split; constructor.
+ split; intro Hl; constructor.
  - intro Habs. inversion_clear Hl. apply H. rewrite InA_map_iff; try eassumption. exists a. now split.
  - rewrite <- IHl. now inversion_clear Hl.
  - intro Habs. inversion_clear Hl. apply H. rewrite InA_map_iff in Habs; try eassumption.
    destruct Habs as [x [Heq Hin]]. apply Hinj in Heq. now rewrite Heq in Hin.
  - rewrite IHl. now inversion_clear Hl.
Qed.


Lemma NoDupA_app_iff : forall l l' : list A, NoDupA eqA (l ++ l')
  <-> NoDupA eqA l /\ NoDupA eqA l' /\ (forall x : A, InA eqA x l -> InA eqA x l' -> False).
Proof.
intros l l'. split; intro H; try now apply NoDupA_app.
induction l; simpl in *.
  split. constructor. split. assumption. intros ? Habs. now inversion Habs.
  inversion_clear H. apply IHl in H1. destruct H1 as [H1 [H2 H3]]. repeat split; trivial.
    constructor. intro Habs. apply H0. rewrite InA_app_iff; trivial. now left. assumption.
    intros x Hin1 Hin2. inversion_clear Hin1.
      apply H0. rewrite InA_app_iff. right. now rewrite <- H.
      now apply (H3 x).
Qed.

Lemma NoDupA_swap_iff : forall (l l' : list A) (x : A), NoDupA eqA (l ++ x :: l') <-> NoDupA eqA (x :: l ++ l').
Proof.
intros l l'. split; intro H. now apply NoDupA_swap.
inversion_clear H. rewrite InA_app_iff in H0; trivial. 
rewrite NoDupA_app_iff in *; trivial. destruct H1 as [H1 [H2 H3]]. repeat split.
  assumption.
  constructor.
    intro Habs. apply H0. now right.
    assumption.
  intros a Hl Hl'. inversion_clear Hl'.
    apply H0. left. now rewrite <- H.
    now apply (H3 a).
Qed.

Lemma NoDupA_filter_compat : forall f, Proper (eqA ==> eq) f -> forall l, NoDupA eqA l -> NoDupA eqA (filter f l).
Proof.
intros f Hf l Hnodup. induction Hnodup; simpl.
- constructor.
- destruct (f x) eqn:Hfx; trivial. constructor; trivial. rewrite filter_InA; intuition.
Qed.

Global Instance filter_PermutationA_compat : forall f, Proper (eqA ==> eq) f ->
  Proper (PermutationA eqA ==> PermutationA eqA) (filter f).
Proof.
intros f Hf l1 l2 perm. induction perm.
- reflexivity.
- simpl. destruct (f x₁) eqn:Hfx; rewrite H in Hfx; rewrite Hfx; now try constructor.
- simpl. destruct (f x), (f y); try now constructor. reflexivity.
- rewrite IHperm1. apply IHperm2.
Qed.

Global Instance Forall_PermutationA_compat : forall f, Proper (eqA ==> iff) f ->
  Proper (PermutationA eqA ==> iff) (Forall f).
Proof.
intros f Hf l1 l2 perm. induction perm.
- tauto.
- apply Hf in H. split; intro Hrec; inversion_clear Hrec; left + right; tauto.
- split; intro Hrec; inversion_clear Hrec; inversion_clear H0; repeat constructor; assumption.
- tauto.
Qed.

Global Instance Exists_PermutationA_compat : forall f, Proper (eqA ==> iff) f ->
  Proper (PermutationA eqA ==> iff) (Exists f).
Proof.
intros f Hf l1 l2 perm. induction perm.
- tauto.
- apply Hf in H. split; intro Hrec; inversion_clear Hrec; left + right; tauto.
- split; intro Hrec; inversion_clear Hrec; try inversion_clear H; left + right; tauto || (left + right; tauto).
- tauto.
Qed.

End List_results.
