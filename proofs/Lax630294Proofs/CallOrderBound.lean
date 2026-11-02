import Lax630294Proofs.CallOrderReduce

/-!
# The call lower bound and saturation

* `Admissible.card_F_lower`: the information-flow part of the closed-tree reduction
  (first calls of the non-roots are distinct).
* `Admissible.lower_bound`: `2 r - 4 ≤ |E(H)|` (`cor:characterization-call-lower-bound`).
* `Admissible.saturation`: `lem:characterization-closed-tree-saturated`.
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- Every vertex other than the ends of the last early edge `e` of `X` must take part in a call
outside `I` (it lacks a secret). -/
lemma Admissible.nonroot_need (hA : Admissible H P) {I : Set β} {X : Set α}
    (hR : IsReduced H P I X) {e : β} {x0 x1 : α} (heX : e ∈ edgesIn H I X)
    (hl : H.IsLink e x0 x1) {ℓ : β → ℕ} (hfam : IsFam H P I e ℓ) {v : α} (hv : v ∈ V(H))
    (hv0 : v ≠ x0) (hv1 : v ≠ x1) : ∃ f ∈ E(H), f ∉ I ∧ H.Inc f v := by
  by_contra hnone
  have hnone' : ∀ f ∈ E(H) \ I, ¬ H.Inc f v := fun f hf hinc => hnone ⟨f, hf.1, hf.2, hinc⟩
  obtain ⟨hx0X, hx1X⟩ := heX.2.ends_mem hl
  have hx0V := hl.left_mem
  have hx1V := hl.right_mem
  obtain ⟨X0, X1, hX0, hX1, hdisj, hunion, hx0X0, hx1X1⟩ :=
    tree_split hA.finV hA.finE hR.tree heX hl
  have key := fun s hs => need_conn_last hA hfam.inj hfam.mono hfam.Ifirst heX.1 hfam.elast
    hv hnone' (s := s) hs
  have hincE : ¬ H.Inc e v := by
    intro hinc
    rcases hinc.eq_or_eq_of_isLink hl with h | h
    · exact hv0 h
    · exact hv1 h
  by_cases hvX : v ∈ X
  · rw [← hunion] at hvX
    rcases hvX with hv0' | hv1'
    · rcases key x1 hx1V with hc | hc
      · have : v ∈ X1 := hX1.1.mem_of_conn hx1X1 hc
        exact Set.disjoint_left.1 hdisj hv0' this
      · exact hincE hc
    · rcases key x0 hx0V with hc | hc
      · have : v ∈ X0 := hX0.1.mem_of_conn hx0X0 hc
        exact Set.disjoint_left.1 hdisj this hv1'
      · exact hincE hc
  · rcases key x0 hx0V with hc | hc
    · exact hvX (hR.tree.1.mem_of_conn hx0X (hc.mono (fun g hg => hg.1)))
    · exact hincE hc

/-- A minimal edge outside `I` touches an end of `e` (cover relation). -/
lemma Admissible.minout_touch (hA : Admissible H P) {I : Set β} {e : β} {x0 x1 : α}
    (hemaxI : ∀ c ∈ I, ¬ P e c) (hl : H.IsLink e x0 x1)
    (hP3 : ∀ f ∈ E(H) \ I, P e f) {f : β} (hf : IsMinOut H P I f) :
    H.Inc f x0 ∨ H.Inc f x1 := by
  have hef := hP3 f ⟨hf.1, hf.2.1⟩
  have hcov : ∀ c, P e c → ¬ P c f := fun c hec hcf => hemaxI c (hf.2.2 c hcf) hec
  obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hef hcov
  rcases hy1.eq_or_eq_of_isLink hl with h | h
  · rw [h] at hy2; exact Or.inl hy2
  · rw [h] at hy2; exact Or.inr hy2

/-- The first-call injection. -/
lemma Admissible.first_call_inj [Nonempty β] (hA : Admissible H P) {I : Set β}
    (hI : IsIdeal H P I) {ℓ : β → ℕ} (hinj : Set.InjOn ℓ E(H)) (hP : ∀ a b, P a b → ℓ a < ℓ b)
    {R : Set α} (hneed : ∀ v ∈ V(H), v ∉ R → ∃ f ∈ E(H), f ∉ I ∧ H.Inc f v)
    (hM : ∀ f, IsMinOut H P I f → ∃ y ∈ R, H.Inc f y) :
    ∃ φ : α → β, (∀ v ∈ V(H), v ∉ R → IsFirstAt H I ℓ v (φ v)) ∧ Set.InjOn φ (V(H) \ R) := by
  classical
  have : ∀ v, ∃ f, v ∈ V(H) → v ∉ R → IsFirstAt H I ℓ v f := by
    intro v
    by_cases h : v ∈ V(H) ∧ v ∉ R
    · obtain ⟨f, hf⟩ := exists_first hA hinj (hneed v h.1 h.2)
      exact ⟨f, fun _ _ => hf⟩
    · exact ⟨Classical.arbitrary β, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose φ hφ using this
  refine ⟨φ, fun v hv hvR => hφ v hv hvR, ?_⟩
  intro v hv v' hv' heq
  by_contra hne
  have h1 := hφ v hv.1 hv.2
  have h2 := hφ v' hv'.1 hv'.2
  rw [← heq] at h2
  have hl := link_of_inc_inc h1.2.2.1 h2.2.2.1 hne
  have hmin := isMinOut_of_first hA hI hP hl h1 h2
  obtain ⟨y, hyR, hy⟩ := hM _ hmin
  rcases hy.eq_or_eq_of_isLink hl with h | h
  · exact hv.2 (h ▸ hyR)
  · exact hv'.2 (h ▸ hyR)

lemma Admissible.first_call_card (hA : Admissible H P) {I : Set β}
    (hI : IsIdeal H P I) {ℓ : β → ℕ} (hinj : Set.InjOn ℓ E(H)) (hP : ∀ a b, P a b → ℓ a < ℓ b)
    {R : Set α} (hRfin : R.Finite) (hneed : ∀ v ∈ V(H), v ∉ R → ∃ f ∈ E(H), f ∉ I ∧ H.Inc f v)
    (hM : ∀ f, IsMinOut H P I f → ∃ y ∈ R, H.Inc f y) :
    V(H).ncard ≤ R.ncard + (E(H) \ I).ncard := by
  by_cases hne : (V(H) \ R).Nonempty
  · obtain ⟨v0, hv0⟩ := hne
    obtain ⟨f0, -⟩ := hneed v0 hv0.1 hv0.2
    have : Nonempty β := ⟨f0⟩
    obtain ⟨φ, hφ, hφinj⟩ := hA.first_call_inj hI hinj hP hneed hM
    have h1 : (V(H) \ R).ncard ≤ (E(H) \ I).ncard :=
      Set.ncard_le_ncard_of_injOn φ
        (fun v hv => ⟨(hφ v hv.1 hv.2).1, (hφ v hv.1 hv.2).2.1⟩) hφinj
        (hA.finE.subset Set.sdiff_subset)
    have h2 : V(H).ncard ≤ (V(H) \ R).ncard + R.ncard := by
      calc V(H).ncard ≤ ((V(H) \ R) ∪ R).ncard :=
            Set.ncard_le_ncard (fun v hv => by
              by_cases hvR : v ∈ R
              · exact Or.inr hvR
              · exact Or.inl ⟨hv, hvR⟩) ((hA.finV.subset Set.sdiff_subset).union hRfin)
        _ ≤ _ := Set.ncard_union_le _ _
    omega
  · rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    have := Set.ncard_le_ncard hne hRfin
    omega

/-- The information-flow bounds of the closed-tree reduction lemma:
`|F| ≥ r - 1` if `X` is a singleton and `|F| ≥ r - 2` otherwise. -/
theorem Admissible.card_F_lower (hA : Admissible H P) {I : Set β} {X : Set α}
    (hR : IsReduced H P I X)
    (hP3 : ∀ e ∈ edgesIn H I X, (∀ c ∈ edgesIn H I X, ¬ P e c) → ∀ f ∈ E(H) \ I, P e f) :
    V(H).ncard ≤ (E(H) \ I).ncard + 2 ∧ (X.ncard = 1 → V(H).ncard ≤ (E(H) \ I).ncard + 1) := by
  classical
  have hXfin : X.Finite := hA.finV.subset hR.tree.1.2.1
  by_cases h1 : X.ncard = 1
  · refine ⟨?_, fun _ => ?_⟩ <;>
    · obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 h1
      obtain ⟨ℓ, hinj, hP, hL⟩ := exists_linear_ext hA.finE P hA.irrefl hA.trans
        (fun h => ⟨hA.mem_left h, hA.mem_right h⟩) (fun g => if g ∈ I then 0 else 1) (by
          intro a b hab
          by_cases ha : a ∈ I
          · simp [ha]
          · have hb : b ∉ I := fun hb => ha (hR.ideal.2 a b hab hb)
            simp [ha, hb])
      have hIF : ∀ g ∈ I, ∀ f ∈ E(H) \ I, ℓ g < ℓ f := fun g hg f hf =>
        hL g (hR.ideal.1 hg) f hf.1 (by simp [hg, hf.2])
      have hxX : x ∈ X := hx ▸ rfl
      have hxV : x ∈ V(H) := hR.tree.1.2.1 hxX
      have hcard := hA.first_call_card hR.ideal hinj hP hXfin (R := X) (fun v hv hvX => by
        by_contra hnone
        have hnone' : ∀ f ∈ E(H) \ I, ¬ H.Inc f v := fun f hf hinc => hnone ⟨f, hf.1, hf.2, hinc⟩
        exact hvX (hR.tree.1.mem_of_conn hxX (need_conn hA hinj hP hIF hv hnone' hxV)))
        (fun f hf => by
          obtain ⟨p, q, hl, hp, -⟩ := hR.cross f hf
          exact ⟨p, hp, hl.inc_left⟩)
      omega
  · have hXtwo : 2 ≤ X.ncard := by
      have := (Set.ncard_pos hXfin).2 hR.tree.1.1
      omega
    have hedge : (edgesIn H I X).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := hR.tree.2
      rw [hemp] at this
      simp at this
      omega
    obtain ⟨e, he, hemax⟩ := hA.exists_max (edgesIn_subset I X) hedge
    have hemaxI := hA.max_in_ideal hR.ideal hR.tree.1 he hemax
    obtain ⟨x0, x1, hl, hx0, hx1⟩ := he.2
    obtain ⟨ℓ, hfam⟩ := hA.exists_fam hR.ideal he.1 hemaxI
    have hcard := hA.first_call_card hR.ideal hfam.inj hfam.mono
      (R := {x0, x1}) (Set.toFinite _) (fun v hv hvR => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hvR
        exact hA.nonroot_need hR he hl hfam hv hvR.1 hvR.2)
      (fun f hf => by
        rcases hA.minout_touch hemaxI hl (hP3 e he hemax) hf with h | h
        · exact ⟨x0, Or.inl rfl, h⟩
        · exact ⟨x1, Or.inr rfl, h⟩)
    have h2 : ({x0, x1} : Set α).ncard ≤ 2 :=
      (Set.ncard_insert_le x0 {x1}).trans (by simp)
    exact ⟨by omega, fun h => absurd h h1⟩

/-- If a closed tree component exists in an ideal `J`, then `|J| + r ≤ |E| + 2`. -/
theorem Admissible.closed_card_bound (hA : Admissible H P) {J : Set β} {A : Set α}
    (hJ : IsIdeal H P J) (hAt : IsTreeComp H J A) (hAc : IsClosed H P J A) :
    J.ncard + V(H).ncard ≤ E(H).ncard + 2 := by
  obtain ⟨I, X, hR, hJI, -, hP3⟩ := hA.closed_tree_reduction hJ hAt hAc
  have h := (hA.card_F_lower hR hP3).1
  have hsplit : (E(H) \ I).ncard + I.ncard = E(H).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hR.ideal.1 hA.finE
  omega

/-- **Call lower bound** (`cor:characterization-call-lower-bound`): `|E(H)| ≥ 2 r - 4`. -/
theorem Admissible.lower_bound (hA : Admissible H P) (hr : 4 ≤ V(H).ncard) :
    2 * V(H).ncard - 4 ≤ E(H).ncard := by
  have hne : V(H).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hc := hA.card_vertices_le hne
  obtain ⟨J, hJ, hJc⟩ := hA.exists_ideal_ncard (n := V(H).ncard - 2) (by omega)
  obtain ⟨A, B, hAt, hBt, hAB⟩ := exists_two_tree_comps hA.finV hA.finE hJ.1 (by omega)
  obtain ⟨J', hJ', hJ'c, X, hXt, hXc⟩ := hA.exists_closed hJ hAt hBt hAB
  have := hA.closed_card_bound hJ' hXt hXc
  omega

/-- **Saturation of a closed early tree** (`lem:characterization-closed-tree-saturated`). -/
theorem Admissible.saturation (hA : Admissible H P) (hr : 4 ≤ V(H).ncard)
    (hE : E(H).ncard = 2 * V(H).ncard - 4) {J : Set β} {A : Set α} (hJ : IsIdeal H P J)
    (hJcard : V(H).ncard - 2 ≤ J.ncard) (hAt : IsTreeComp H J A) (hAc : IsClosed H P J A) :
    J.ncard = V(H).ncard - 2 ∧ ∀ f, IsMinOut H P J f → Crosses H A f := by
  have hb := hA.closed_card_bound hJ hAt hAc
  have hJeq : J.ncard = V(H).ncard - 2 := by omega
  refine ⟨hJeq, fun f hf => ?_⟩
  obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hf.1
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
  · exact absurd ⟨x, y, hl, hx, hy⟩ (hAc f hf)
  · exact ⟨x, y, hl, hx, hy⟩
  · exact ⟨y, x, hl.symm, hy, hx⟩
  · exfalso
    obtain ⟨hcomp, hEq⟩ := hAt.1.mono_edges (S' := insert f J) (Set.subset_insert _ _)
      (fun e he heS x' y' hl' => by
        have hef : e = f := he.resolve_right heS
        subst hef
        rcases hl'.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hx, hy⟩
        · exact ⟨hy, hx⟩)
    have hAt' : IsTreeComp H (insert f J) A := ⟨hcomp, by rw [hEq]; exact hAt.2⟩
    have hAc' : IsClosed H P (insert f J) A :=
      (hA.closed_persist hJ (hJ.insert hf) (Set.subset_insert _ _) hcomp hAc).1
    have := hA.closed_card_bound (hJ.insert hf) hAt' hAc'
    rw [Set.ncard_insert_of_notMem hf.2.1 (hA.finE.subset hJ.1)] at this
    omega

end Lax630294Proofs.CallOrder
