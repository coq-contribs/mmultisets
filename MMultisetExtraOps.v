Require Import Omega.
Require Import Equalities.
Require Import SetoidList.
Require Import MMultisets.Preliminary.
Require Import MMultisets.MMultisetInterface.
Require MMultisets.MMultisetFacts.


Set Implicit Arguments.


Module Make(E : DecidableType)(M : MMultisetsOn E).
  Module MProp := MMultisetFacts.Make(E)(M).
  Include MProp.
  
  (** *  Extra operations  **)
  
  (** **  Function [map] and its properties  **)
  
  Definition map f m := fold (fun x n acc => add (f x) n acc) m empty.
  
  Section map_results.
    Variable f : E.t -> E.t.
    Hypothesis Hf : Proper (E.eq ==> E.eq) f.
    
    Global Instance map_compat : Proper (eq ==> eq) (map f).
    Proof.
    intros m₁ m₂ Hm. unfold map. apply (fold_compat _ _).
    - repeat intro. msetdec.
    - repeat intro. apply add_comm.
    - assumption.
    - reflexivity.
    Qed.
    
    Lemma map_In : forall x m, In x (map f m) <-> exists y, E.eq x (f y) /\ In y m.
    Proof.
    intros x m. unfold In, map. apply fold_rect.
    + intros m₁ m₂ acc Heq Hequiv. rewrite Hequiv. now setoid_rewrite Heq.
    + setoid_rewrite empty_spec. split; try intros [? [_ ?]]; omega.
    + intros y p m' acc Hm Hpos Hin Hrec. destruct (E.eq_dec x (f y)) as [Heq | Hneq]; msetdec.
      - split.
          intros. exists y. split; trivial. now msetdec.
          intros [? [? ?]]. msetdec.
      - rewrite Hrec. split; intros [z [Heq ?]]; exists z; split; msetdec.
    Qed.
    
    Lemma map_empty : map f empty [=] empty.
    Proof. unfold map. now rewrite fold_empty. Qed.
    
    Lemma map_add : forall x n m, map f (add x n m) [=] add (f x) n (map f m).
    Proof.
    intros x n m y. destruct n.
    + now do 2 rewrite add_0.
    + unfold map at 1. rewrite (fold_add_additive _).
      - reflexivity.
      - repeat intro. msetdec.
      - repeat intro. apply add_comm.
      - repeat intro. apply add_merge.
      - omega.
    Qed.
    
    Lemma map_spec : forall x m, multiplicity x (map f m) =
      cardinal (nfilter (fun y _ => if E.eq_dec (f y) x then true else false) m).
    Proof.
    intros x m. pose (g := fun y (_ : nat) => if E.eq_dec (f y) x then true else false). unfold elt. fold g.
    assert (Hg : Proper (E.eq ==> @Logic.eq nat ==> Logic.eq) g). { repeat intro. unfold g. msetdec. }
    pattern m. apply ind; clear m.
    + intros ? ? Hm. now rewrite Hm.
    + intros * Hin Hrec. rewrite map_add, nfilter_add; trivial. unfold g at 2.
      msetdec. rewrite cardinal_add. omega.
    + now rewrite map_empty, nfilter_empty, cardinal_empty, empty_spec.
    Qed.
    
    Global Instance map_sub_compat : Proper (Subset ==> Subset) (map f).
    Proof.
    intro m. pattern m. apply ind; clear m.
    + intros ? ? Hm. now setoid_rewrite Hm.
    + intros m x n Hin Hn Hrec m' Hsub y. setoid_rewrite <- (@add_remove_cancel x n m').
      - do 2 rewrite (map_add _). msetdec.
          apply plus_le_compat; trivial. repeat rewrite map_spec; trivial. apply add_subset_remove in Hsub.
          apply cardinal_sub_compat, nfilter_sub_compat, Hsub; repeat intro; msetdec.
          now apply Hrec, add_subset_remove.
      - specialize (Hsub x). msetdec.
    + intros ? _. rewrite map_empty. apply subset_empty_l.
    Qed.
    
    Lemma map_singleton : forall x n, map f (singleton x n) [=] singleton (f x) n.
    Proof.
    intros x n y. destruct n.
    + repeat rewrite singleton_0. now rewrite map_empty. 
    + unfold map. rewrite (@fold_singleton _ eq); repeat intro; msetdec.
    Qed.
    
    Lemma map_remove1 : forall x n m, n <= multiplicity x m -> map f (remove x n m) [=] remove (f x) n (map f m).
    Proof.
    intros x n m Hle. rewrite <- (add_remove_cancel Hle) at 2. now rewrite (map_add _), remove_add_cancel.
    Qed.
    
    Lemma map_remove2 : forall x n m,
      multiplicity x m <= n -> map f (remove x n m) [=] remove (f x) (multiplicity x m) (map f m).
    Proof. intros x n m Hle. rewrite <- (add_remove_id Hle) at 3. now rewrite (map_add _), remove_add_cancel. Qed.
    
    Lemma fold_map_union : forall m₁ m₂, fold (fun x n acc => add (f x) n acc) m₁ m₂ [=] union (map f m₁) m₂.
    Proof.
    intros m₁ m₂. apply fold_rect with (m := m₁).
    + repeat intro. msetdec.
    + now rewrite map_empty, union_empty_l.
    + intros. now rewrite H2, map_add, union_add_comm_l.
    Qed.
    
    Theorem map_union : forall m₁ m₂, map f (union m₁ m₂) [=] union (map f m₁) (map f m₂).
    Proof.
    intros m₁ m₂. unfold map at 1 2. rewrite (fold_union_additive _).
    + now apply fold_map_union.
    + repeat intro. msetdec.
    + repeat intro. apply add_comm.
    + repeat intro. apply add_merge.
    Qed.
    
    Theorem map_inter : forall m₁ m₂, map f (inter m₁ m₂) [<=] inter (map f m₁) (map f m₂).
    Proof.
    intros m1 m2 x. destruct (multiplicity x (map f (inter m1 m2))) eqn:Hfx.
    + omega.
    + assert (Hin : In x (map f (inter m1 m2))) by msetdec.
      rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite inter_In in Hin.
      destruct Hin as [Hin1 Hin2]. rewrite <- Hfx, Heq. rewrite inter_spec.
      apply Nat.min_glb; apply map_sub_compat; apply inter_subset_l + apply inter_subset_r.
    Qed.
    
    Theorem map_lub : forall m₁ m₂, lub (map f m₁) (map f m₂) [<=] map f (lub m₁ m₂).
    Proof.
    intros m1 m2 x. destruct (multiplicity x (lub (map f m1) (map f m2))) eqn:Hfx.
    + omega.
    + assert (Hin : In x (lub (map f m1) (map f m2))).
      { rewrite lub_spec in *. rewrite lub_In. unfold In.
        destruct (Max.max_dec (multiplicity x (map f m1)) (multiplicity x (map f m2))) as [Heq | Heq];
        rewrite Heq in Hfx; left + right; omega. }
      rewrite lub_In in Hin. rewrite <- Hfx.
      destruct Hin as [Hin | Hin]; rewrite map_In in Hin; destruct Hin as [y [Heq Hin]]; rewrite Heq, lub_spec;
      apply Max.max_lub; apply map_sub_compat; apply lub_subset_l + apply lub_subset_r.
    Qed.
    
    (*
    Lemma map_elements : forall m,
      PermutationA eq_pair (elements (map f m)) (List.map (fun xn => (f (fst xn), snd xn)) (elements m)).
    Proof.
    assert (Proper (eq_pair ==> eq_pair) (fun xn => (f (fst xn), snd xn))). { intros ? ? Heq. now rewrite Heq. }
    apply ind.
    + intros ? ? Hm. now rewrite Hm.
    + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite elements_add_out; trivial.
      - simpl. now constructor.
      - rewrite (map_In _). intros [y [Heq Hy]]. apply Hf2 in Heq. apply Hin. now rewrite Heq.
    + now rewrite map_empty, elements_empty.
    Qed.
    *)
    
    Lemma map_from_elements : 
      forall l, map f (from_elements l) [=] from_elements (List.map (fun xn => (f (fst xn), snd xn)) l).
    Proof.
    induction l as [| [x n] l]; simpl.
    - apply map_empty.
    - rewrite map_add. f_equiv. apply IHl.
    Qed.
    
    Lemma map_support : forall m, inclA E.eq (support (map f m)) (List.map f (support m)).
    Proof.
    apply ind.
    * repeat intro. msetdec.
    * intros m x n Hin Hn Hrec. rewrite map_add; trivial. repeat rewrite support_add; try omega.
      destruct (In_dec x m); try contradiction. destruct (In_dec (f x) (map f m)).
      + intros y Hy. simpl. right. now apply Hrec.
      + intros y Hy. simpl. inversion_clear Hy.
        - left. auto.
        - right. now apply Hrec.
    * now rewrite map_empty, support_empty.
    Qed.
    
    Lemma map_cardinal : forall m, cardinal (map f m) = cardinal m.
    Proof.
    apply ind.
    + repeat intro. msetdec.
    + intros m x n Hin Hn Hrec. rewrite (map_add _). do 2 rewrite cardinal_add. now rewrite Hrec.
    + now rewrite map_empty.
    Qed.
    
    Lemma map_size : forall m, size (map f m) <= size m.
    Proof.
    apply ind.
    + repeat intro. msetdec.
    + intros m x n Hm Hn Hrec. rewrite map_add, size_add, size_add; trivial.
      destruct (In_dec x m) as [Hin | Hin], (In_dec (f x) (map f m)) as [Hinf | Hinf].
      - apply Hrec.
      - elim Hinf. rewrite map_In. now exists x.
      - omega.
      - omega.
    + now rewrite map_empty.
    Qed.
    
    Section map_injective_results.
      Hypothesis Hf2 : injective E.eq E.eq f.
      
      Lemma map_injective_spec : forall x m, multiplicity (f x) (map f m) = multiplicity x m.
      Proof.
      intros x m. unfold map. apply fold_rect.
      + repeat intro. msetdec.
      + now do 2 rewrite empty_spec.
      + intros y n m' acc Hin Hpos Hm Heq. destruct (E.eq_dec x y) as [Hxy | Hxy].
        - msetdec.
        - repeat rewrite add_other; trivial. intro Habs. apply Hxy. now apply Hf2.
      Qed.
      
      Corollary map_injective_In : forall x m, In (f x) (map f m) <-> In x m.
      Proof.
      intros x m. rewrite map_In; trivial. split; intro Hin.
      + destruct Hin as [y [Heq Hin]]. apply Hf2 in Heq. now rewrite Heq.
      + now exists x.
      Qed.
      
      Lemma map_injective_remove : forall x n m, map f (remove x n m) [=] remove (f x) n (map f m).
      Proof.
      intros x n m. destruct (le_dec n (multiplicity x m)) as [Hle | Hlt].
      * now apply map_remove1.
      * intro y. msetdec.
        + repeat rewrite map_injective_spec; trivial. msetdec.
        + destruct (In_dec y (map f m)) as [Hin | Hin].
          - rewrite (map_In _) in Hin. destruct Hin as [z [Heq Hz]]. msetdec.
            repeat rewrite map_injective_spec; trivial. msetdec.
          - rewrite not_In in Hin. rewrite Hin, <- not_In, (map_In _).
            intros [z [Heq Hz]]. msetdec. rewrite map_injective_spec in Hin; trivial. omega.
      Qed.
      
      Theorem map_injective_inter : forall m₁ m₂, map f (inter m₁ m₂) [=] inter (map f m₁) (map f m₂).
      Proof.
      intros m₁ m₂ x. destruct (multiplicity x (inter (map f m₁) (map f m₂))) eqn:Hn.
      + rewrite <- not_In in *. intro Habs. apply Hn. rewrite (map_In _) in Habs. destruct Habs as [y [Heq Hy]].
        msetdec. unfold gt in *. rewrite Nat.min_glb_lt_iff in *. now repeat rewrite map_injective_spec.
      + rewrite inter_spec in Hn.
        assert (Hx : In x (map f m₁)).
        { msetdec. apply lt_le_trans with (S n). omega. rewrite <- Hn. apply Min.le_min_l. }
        rewrite map_In in *; trivial. destruct Hx as [y [Heq Hy]]. msetdec.
        do 2 (rewrite map_injective_spec in *; trivial). msetdec.
      Qed.
      
      Theorem map_injective_diff : forall m₁ m₂, map f (diff m₁ m₂) [=] diff (map f m₁) (map f m₂).
      Proof.
      intros m₁ m₂ x. destruct (multiplicity x (diff (map f m₁) (map f m₂))) eqn:Hn.
      + rewrite <- not_In in *. intro Habs. apply Hn. rewrite (map_In _) in Habs. destruct Habs as [y [Heq Hy]].
        msetdec. now repeat rewrite map_injective_spec.
      + assert (Hx : In x (map f m₁)) by msetdec.
        rewrite map_In in *; trivial. destruct Hx as [y [Heq _]]. msetdec.
        do 2 (rewrite map_injective_spec in *; trivial). msetdec.
      Qed.
      
      Lemma map_injective_lub_wlog : forall x m₁ m₂, multiplicity x (map f m₂) <= multiplicity x (map f m₁) ->
        multiplicity x (map f (lub m₁ m₂)) = multiplicity x (map f m₁).
      Proof.
      intros x m₁ m₂ Hle. destruct (multiplicity x (map f m₁)) eqn:Heq1.
        - apply le_n_0_eq in Hle. symmetry in Hle. destruct (multiplicity x (map f (lub m₁ m₂))) eqn:Heq2; trivial.
          assert (Hin : In x (map f (lub m₁ m₂))). { unfold In. omega. }
          rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite Heq in *. rewrite lub_In in Hin.
          rewrite map_injective_spec in *. unfold In in *. destruct Hin; omega.
        - assert (Hin : In x (map f m₁)). { unfold In. omega. }
          rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite Heq, map_injective_spec in *.
          rewrite lub_spec. rewrite Nat.max_l; omega.
      Qed.
      
      Theorem map_injective_lub : forall m₁ m₂, map f (lub m₁ m₂) [=] lub (map f m₁) (map f m₂).
      Proof.
      intros m₁ m₂ x. rewrite lub_spec. apply Max.max_case_strong; intro Hle.
      - now apply map_injective_lub_wlog.
      - rewrite lub_comm. now apply map_injective_lub_wlog.
      Qed.
      
      Lemma map_injective : injective eq eq (map f).
      Proof. intros ? ? Hm x. specialize (Hm (f x)). repeat (rewrite map_injective_spec in Hm; trivial). Qed.
      
      Lemma map_injective_elements : forall m,
        PermutationA eq_pair (elements (map f m)) (List.map (fun xn => (f (fst xn), snd xn)) (elements m)).
      Proof.
      assert (Proper (eq_pair ==> eq_pair) (fun xn => (f (fst xn), snd xn))). { intros ? ? Heq. now rewrite Heq. }
      apply ind.
      + repeat intro. msetdec.
      + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite elements_add_out; trivial.
        - simpl. now constructor.
        - rewrite (map_In _). intros [y [Heq Hy]]. apply Hf2 in Heq. apply Hin. now rewrite Heq.
      + now rewrite map_empty, elements_empty.
      Qed.
      
      Lemma map_injective_support : forall m, PermutationA E.eq (support (map f m)) (List.map f (support m)).
      Proof.
      apply ind.
      * repeat intro. msetdec.
      * intros m x n Hin Hrec. rewrite map_add; trivial. repeat rewrite support_add; try omega.
        destruct (InA_dec (eqA:=E.eq) E.eq_dec (f x) (support (map f m))) as [Habs | _].
        + rewrite support_spec in Habs. unfold In in *. rewrite map_injective_spec in Habs. contradiction.
        + destruct (InA_dec (eqA:=E.eq) E.eq_dec x (support m)) as [Habs | _].
          - rewrite support_spec in Habs. unfold In in *. contradiction.
          - simpl. destruct (In_dec x m); try contradiction. rewrite <- map_injective_In in Hin; trivial.
            destruct (In_dec (f x) (map f m)); try contradiction. now apply PermutationA_cons.
      * now rewrite map_empty, support_empty.
      Qed.
      
      Lemma map_injective_size : forall m, size (map f m) = size m.
      Proof.
      apply ind.
      + repeat intro. msetdec.
      + intros m x n Hin Hn Hrec. rewrite (map_add _). rewrite size_add, Hrec; trivial.
        destruct (In_dec (f x) (map f m)) as [Hinf | Hinf].
        - rewrite map_In in Hinf; trivial. destruct Hinf as [y [Heq Hiny]].
          apply Hf2 in Heq. rewrite Heq in Hin. contradiction.
        - rewrite size_add; trivial. destruct (In_dec x m); reflexivity || contradiction.
      + now rewrite map_empty.
      Qed.
      
    End map_injective_results.
  End map_results.
  
  Lemma map_extensionality_compat : forall f g, Proper (E.eq ==> E.eq) f ->
    (forall x, g x = f x) -> forall m, map g m [=] map f m.
  Proof.
  intros f g Hf Hext m x.
  assert (Hg : Proper (E.eq ==> E.eq) g). { intros ? ? Heq. do 2 rewrite Hext. now apply Hf. }
  repeat rewrite map_spec; trivial. f_equiv. apply nfilter_extensionality_compat.
  - intros y z Heq _ _ _. destruct (E.eq_dec (g y) x), (E.eq_dec (g z) x); trivial; rewrite Heq in *; contradiction.
  - intros y _. destruct (E.eq_dec (f y) x), (E.eq_dec (g y) x); trivial; rewrite Hext in *; contradiction.
  Qed.
  
  Lemma map_dependent_extensionality_compat : forall f g, Proper (E.eq ==> E.eq) f -> Proper (E.eq ==> E.eq) g ->
    forall m, (forall x, In x m -> g x = f x) -> map g m [=] map f m.
  Proof.
  intros f g Hf Hg m Hext x.
  repeat rewrite map_spec; trivial. f_equiv. apply nfilter_dependent_extensionality_compat.
  - intros y z Heq _ _ _. destruct (E.eq_dec (g y) x), (E.eq_dec (g z) x); trivial; rewrite Heq in *; contradiction.
  - intros y z Heq _ _ _. destruct (E.eq_dec (f y) x), (E.eq_dec (f z) x); trivial; rewrite Heq in *; contradiction.
  - intros y _ Hin. destruct (E.eq_dec (f y) x), (E.eq_dec (g y) x); rewrite Hext in *; trivial; contradiction.
  Qed.
  
  Lemma map_merge : forall f g, Proper (E.eq ==> E.eq) f -> Proper (E.eq ==> E.eq) g ->
    forall m, map f (map g m) [=] map (fun x => f (g x)) m.
  Proof.
  intros f g Hf Hg.
  apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. repeat rewrite map_add; refine _. now rewrite Hrec.
  + now repeat rewrite map_empty.
  Qed.
  
  Theorem map_injective_fold : forall A eqA, Equivalence eqA ->
    forall f g, Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m (i : A), eqA (fold f (map g m) i) (fold (fun x => f (g x)) m i).
  Proof.
  intros A eqA HeqA f g Hf Hf2 Hg Hg2 m.
  assert (Hfg2 : transpose2 eqA (fun x => f (g x))). { repeat intro. apply Hf2. }
  pattern m. apply ind.
  + intros m₁ m₂ Hm. split; intros Heq i; rewrite fold_compat; trivial;
    solve [rewrite Heq; now apply fold_compat; refine _ | now rewrite Hm | reflexivity].
  + intros m' x n Hin Hn Hrec i. rewrite fold_compat; try apply map_add; reflexivity || trivial.
    repeat rewrite fold_add; trivial; refine _.
    - now rewrite Hrec.
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hin. apply Hg2 in Heq. now rewrite Heq.
  + intro. rewrite fold_compat; apply map_empty || reflexivity || trivial. now do 2 rewrite fold_empty.
  Qed.
  
  Lemma map_injective_nfilter : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, nfilter f (map g m) [=] map g (nfilter (fun x => f (g x)) m).
  Proof.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite nfilter_add; trivial.
    - destruct (f (g x) n).
        now rewrite map_add, Hrec.
        apply Hrec.
    - refine _. 
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hg2 in Heq. apply Hin. now rewrite Heq.
  + rewrite map_empty. now rewrite nfilter_empty, nfilter_empty, map_empty; refine _.
  Qed.
  
  Lemma map_injective_npartition_fst : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, fst (npartition f (map g m)) [=] map g (fst (npartition (fun x => f (g x)) m)).
  Proof. intros. repeat rewrite npartition_spec_fst; refine _. now apply map_injective_nfilter. Qed.
  
  Lemma map_npartition_injective_snd : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, snd (npartition f (map g m)) [=] map g (snd (npartition (fun x => f (g x)) m)).
  Proof.
  intros. repeat rewrite npartition_spec_snd; refine _. apply map_injective_nfilter; trivial. repeat intro. msetdec.
  Qed.
  
  Lemma map_injective_for_all : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, for_all f (map g m) = for_all (fun x => f (g x)) m.
  Proof.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite for_all_add; trivial.
    - now rewrite Hrec.
    - refine _.
    - now rewrite map_injective_In.
  + rewrite map_empty. now repeat rewrite for_all_empty; refine _.
  Qed.
  
  Lemma map_injective_exists : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, exists_ f (map g m) = exists_ (fun x => f (g x)) m.
  Proof.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite exists_add; trivial.
    - now rewrite Hrec.
    - refine _. 
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hg2 in Heq. apply Hin. now rewrite Heq.
  + rewrite map_empty. now repeat rewrite exists_empty; refine _.
  Qed.
  
  (** **  Function [max] and its properties  **)
  
  (** ***  Function [max_mult] computing the maximal multiplicity  **)
  
  Definition max_mult m := fold (fun _ => max) m 0.
  
  Instance max_mult_compat : Proper (eq ==> Logic.eq) max_mult.
  Proof.
  unfold max_mult. intros m1 m2 Heq. apply fold_compat; trivial; refine _.
  - repeat intro. now subst.
  - intros _ _ n m p. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
  Qed.
  
  Lemma max_mult_empty : max_mult empty = 0.
  Proof. unfold max_mult. now rewrite fold_empty. Qed.
  
  Lemma max_mult_singleton : forall x n, max_mult (singleton x n) = n.
  Proof.
  intros x n. destruct n.
  - rewrite singleton_0. apply max_mult_empty.
  - unfold max_mult. rewrite fold_singleton; auto with arith.
    repeat intro. now subst.
  Qed.
  
  Lemma max_mult_map_injective_invariant : forall f, Proper (E.eq ==> E.eq) f -> injective E.eq E.eq f ->
    forall m, max_mult (map f m) = max_mult m.
  Proof.
  intros f Hf Hinj. apply ind.
  + intros m1 m2 Hm. now rewrite Hm.
  + intros s x n Hout Hn Hrec. rewrite map_add; try now intros ? ? Heq; rewrite Heq.
    assert (Haux : elt -> elt ->
              forall n m a : nat, Init.Nat.max m (Init.Nat.max n a) = Init.Nat.max n (Init.Nat.max m a)).
    { intros _ _ n' m' p'. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2. }
    unfold max_mult in *. repeat rewrite fold_add; trivial; refine _; try now (hnf; auto).
    intro Habs. apply Hout. apply map_In in Habs.
    - destruct Habs as [y [Heq Hin]]. apply Hinj in Heq. now rewrite Heq.
    - intros ? ? Heq. now rewrite Heq.
  + now rewrite map_empty.
  Qed.
  
  Lemma max_mult_add : forall m x n, n > 0 -> ~In x m ->
    max_mult (add x n m) = Nat.max n (max_mult m).
  Proof.
  intros m x n Hn. unfold max_mult. apply fold_add; trivial.
  - refine _.
  - repeat intro. now subst.
  - repeat intro. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
  Qed.
  
  Theorem max_mult_spec : forall m x, m[x] <= max_mult m.
  Proof.
  intro m. pattern m. apply ind; clear m.
  * intros m1 m2 Hm. now setoid_rewrite Hm.
  * intros m x n Hout Hn Hrec y. rewrite max_mult_add; trivial.
    assert (Hx : m[x] = 0). { rewrite not_In in Hout. assumption. }
    destruct (E.eq_dec y x) as [Hxy | Hxy].
    + rewrite Hxy. rewrite add_spec, Hx. msetdec. apply Max.le_max_l.
    + rewrite add_other; auto. transitivity (max_mult m).
      - apply Hrec.
      - apply Max.le_max_r.
  * intro x. rewrite empty_spec. omega.
  Qed.
  
  Lemma max_mult_0 : forall m, max_mult m = 0 <-> m [=] empty.
  Proof.
  intro m. split; intro Heq.
  + destruct (empty_or_In_dec m) as [? | [x Hin]]; trivial.
    elim (lt_irrefl 0). apply lt_le_trans with m[x].
    - exact Hin.
    - rewrite <- Heq. apply max_mult_spec.
  + rewrite Heq. apply max_mult_empty.
  Qed.
  
  (** ***  Function [max s] returning the elements of a multiset with maximal multiplicity  **)
  
  Definition max m := nfilter (fun _ => beq_nat (max_mult m)) m.
  
  Instance eqb_max_mult_compat m : Proper (E.eq ==> Logic.eq ==> Logic.eq) (fun _ => Nat.eqb (max_mult m)).
  Proof. repeat intro. now subst. Qed.
  
  Instance eqb_max_compat : Proper (E.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) (fun _ : elt => Init.Nat.max).
  Proof. repeat intro. now subst. Qed.
  
  Local Hint Immediate eqb_max_mult_compat eqb_max_compat.
  
  Global Instance max_compat : Proper (eq ==> eq) max.
  Proof.
  intros m1 m2 Heq. unfold max.
  rewrite Heq. apply nfilter_extensionality_compat.
  - repeat intro. now subst.
  - intros _ n. now rewrite Heq.
  Qed.
  
  Lemma max_map_injective : forall f, Proper (E.eq ==> E.eq) f -> injective E.eq E.eq f ->
    forall m, (max (map f m)) [=] (map f (max m)).
  Proof.
  intros f Hf Hinj m. unfold max. rewrite map_injective_nfilter; auto.
  apply map_compat.
  - intros ? ? Heq. now rewrite Heq.
  - apply nfilter_extensionality_compat; repeat intro; subst; trivial.
    now rewrite max_mult_map_injective_invariant.
  Qed.
  
  Lemma max_subset : forall m, max m [<=] m.
  Proof.
  intros m x. unfold max.
  setoid_rewrite nfilter_spec; try now repeat intro; subst.
  destruct (max_mult m =? m[x]); auto. omega.
  Qed.
  
  Theorem max_spec1 : forall m x y, In y (max m) -> m[x] <= (max m)[y].
  Proof.
  intros m x y Hy. unfold max in *.
  unfold In in Hy. rewrite nfilter_spec in *; auto.
  destruct (max_mult m =? m[y]) eqn:Heq; try omega.
  rewrite Nat.eqb_eq in Heq. rewrite <- Heq. apply max_mult_spec.
  Qed.
  
  Theorem max_spec_non_nil : forall m x, In x m -> exists y, In y (max m).
  Proof.
  intro m. pattern m. apply ind; clear m.
  * intros m1 m2 Hm. now setoid_rewrite Hm.
  * intros m x n Hxnotinm Hpos HI x' Hx'.
    destruct (empty_or_In_dec m) as [Hm | [x'' Hx'']].
    + exists x. unfold max. rewrite nfilter_In; auto. split.
      - rewrite add_In. right. split; reflexivity || omega.
      - rewrite Nat.eqb_eq, max_mult_add; trivial.
        rewrite Hm at 2.
        rewrite add_empty, singleton_spec.
        msetdec. rewrite max_mult_empty. apply Max.max_0_r.
    + specialize (HI x'' Hx'').
      destruct HI as [y Hy]. unfold max.
      setoid_rewrite nfilter_In; auto; [].
      rewrite max_mult_add; trivial.
      unfold max in Hy. rewrite nfilter_In in Hy; auto.
      destruct Hy as [Hy Heq]. rewrite Nat.eqb_eq in Heq.
      destruct (le_lt_dec n (m[y])).
      - exists y. split.
        -- msetdec.
        -- rewrite Nat.eqb_eq, Heq, add_other, Max.max_r; trivial. msetdec.
      - exists x. split.
        -- msetdec.
        -- rewrite Nat.eqb_eq, Max.max_l; try omega. msetdec.
  * intros x H. elim (In_empty H).
  Qed.
  
  Lemma max_empty : forall m, max m [=] empty <-> m [=] empty.
  Proof.
  intro m. split; intro H.
  + destruct (empty_or_In_dec m) as [Hm | Hm].
    - intro. now rewrite Hm.
    - destruct Hm as [x Hx].
      destruct (max_spec_non_nil Hx) as [y Hy].
      unfold In in Hy. rewrite H, empty_spec in Hy. omega.
  + rewrite H. unfold max.
    apply nfilter_empty; auto.
  Qed.
  
  Lemma max_singleton : forall x n, max (singleton x n) [=] singleton x n.
  Proof.
  intros x n. destruct n.
  + rewrite singleton_0. now rewrite max_empty.
  + unfold max. rewrite nfilter_singleton_true; try omega.
    - rewrite max_mult_singleton. apply Nat.eqb_refl.
    - repeat intro. now subst.
  Qed.
  
  Lemma max_2_mult : forall m x, (max m)[x] = 0 \/ (max m)[x] = m[x].
  Proof.
  intros m x. destruct (empty_or_In_dec m) as [Hm | Hm].
  + left. rewrite <- max_empty in Hm. rewrite (Hm x). apply empty_spec.
  + unfold max. rewrite nfilter_spec.
    destruct (max_mult m =? m[x]) as [Heq | Heq]; auto.
    repeat intro. now subst.
  Qed.
  
  Lemma max_In_mult : forall m x, In x m -> (In x (max m) <-> (max m)[x] = m[x]).
  Proof. intros m x Hin. unfold In in *. destruct (max_2_mult m x); omega. Qed.
  
  Lemma max_spec_mult : forall m x y, In x (max m) -> (In y (max m) <-> (max m)[y] = (max m)[x]).
  Proof.
  intros m x y Hx. split.
  + intro Hy. destruct (max_2_mult m x) as [Hx' | Hx'], (max_2_mult m y) as [Hy' | Hy'];
    (unfold In in *; omega) || (try congruence); [].
    apply le_antisym; rewrite Hy' + rewrite Hx'; now apply max_spec1.
  + intro Heq. unfold In in *. now rewrite Heq.
  Qed.
  
  Theorem max_spec2 : forall m x y,
    In x (max m) -> ~In y (max m) -> m[y] < m[x].
  Proof.
  intros m x y Hx Hy. apply le_neq_lt.
  + assert (Hx' := Hx). rewrite max_In_mult in Hx.
    - rewrite <- Hx. now apply max_spec1.
    - now rewrite <- max_subset.
  + intro Habs. apply Hy. unfold max. rewrite nfilter_In; try now repeat intro; subst. split.
    - unfold In in *. rewrite Habs. apply lt_le_trans with (max m)[x]; trivial. apply max_subset.
    - rewrite Habs. unfold max in Hx. rewrite nfilter_In in Hx; try now repeat intro; subst.
  Qed.
  
  Lemma max_max_mult : forall m x, ~m [=] empty -> In x (max m) <-> m[x] = max_mult m.
  Proof.
  intros m x Hm. split; intro H.
  + apply nfilter_In in H; auto.
    symmetry. apply beq_nat_true. now destruct H.
  + unfold max. rewrite nfilter_In; auto.
    split.
    - red. cut (m[x]<>0). omega.
      intro Habs. now rewrite H, max_mult_0 in Habs.
    - now rewrite H, <- beq_nat_refl.
  Qed.
  
  Lemma max_max_mult_ex : forall m, ~m [=] empty -> exists x, max_mult m = m[x].
  Proof.
  intros m. pattern m. apply ind; clear m.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m x n Hout Hn Hrec _.
    destruct (empty_or_In_dec m) as [Hm | Hm].
    + exists x. rewrite Hm, add_empty. rewrite max_mult_singleton. msetdec.
    + assert (Hempty : ~m [=] empty) by now rewrite not_empty_In.
      destruct (Hrec Hempty) as [max_m Hmax_m]. rewrite max_mult_add; trivial.
      destruct (Max.max_spec n (max_mult m)) as [[Hmax1 Hmax2] | [Hmax1 Hmax2]].
      - exists max_m. msetdec.
      - exists x. msetdec.
  * intro. msetdec.
  Qed.
  
  Lemma max_spec_max : forall m x, ~m [=] empty -> (forall y, (m[y] <= m[x])) -> max_mult m = m[x].
  Proof.
  intros m x Hm H. apply le_antisym.
  - destruct (@max_max_mult_ex m) as [y Hy]; auto.
    rewrite Hy. apply H.
  - apply max_mult_spec.
  Qed.
  
  Corollary max_spec1_iff : forall m, ~m [=] empty -> forall x, In x (max m) <-> forall y, (m[y] <= m[x]).
  Proof.
  intros m Hm x. assert (Hempty := Hm).
  rewrite <- max_empty, not_empty_In in Hm. destruct Hm as [z Hz].
  split; intro Hx.
  + intro y. assert (Hx' := Hx). rewrite max_In_mult in Hx.
    - rewrite <- Hx. now apply max_spec1.
    - now rewrite <- max_subset.
  + assert (H := max_spec_max Hempty Hx). rewrite max_max_mult; auto.
  Qed.
End Make.
