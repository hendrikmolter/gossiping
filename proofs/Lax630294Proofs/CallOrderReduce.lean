import Lax630294Proofs.CallOrderFlow

/-!
# Closed-tree reduction, call lower bound and saturation

Formalization of `lem:characterization-closed-tree-reduction`,
`cor:characterization-call-lower-bound` and `lem:characterization-closed-tree-saturated`.
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

lemma Admissible.link_ne (hA : Admissible H P) {e : β} {x y : α} (h : H.IsLink e x y) :
    x ≠ y := by
  have := hA.simple
  exact h.ne

lemma Admissible.link_unique (hA : Admissible H P) {e f : β} {x y : α} (h : H.IsLink e x y)
    (h' : H.IsLink f x y) : e = f := by
  have := hA.simple
  exact Graph.Simple.eq_of_isLink h h'

/-! ### Basic tools about ideals and components -/

/-- Descent along covers: an edge outside `J`, internal to a component `X` of `J'` whose
predecessors outside `J` all lie in `J'`, yields a minimal edge outside `J` internal to `X`. -/
lemma Admissible.desc (hA : Admissible H P) {J J' : Set β} (hJ : IsIdeal H P J) {X : Set α}
    (hX : IsComp H J' X) {f : β} (hfE : f ∈ E(H)) (hfJ : f ∉ J) (hint : Internal H X f)
    (hpred : ∀ g, P g f → g ∉ J → g ∈ J') :
    ∃ f', IsMinOut H P J f' ∧ Internal H X f' := by
  obtain ⟨fs, ⟨hE, hnJ, hints, hpreds⟩, hmin⟩ := hA.exists_min
    (T := {f | f ∈ E(H) ∧ f ∉ J ∧ Internal H X f ∧ ∀ g, P g f → g ∉ J → g ∈ J'})
    (fun f hf => hf.1) ⟨f, hfE, hfJ, hint, hpred⟩
  refine ⟨fs, ⟨hE, hnJ, fun g hg => ?_⟩, hints⟩
  by_contra hgJ
  obtain ⟨g', hg'f, hg'J, hcov⟩ := hA.exists_cover_below hJ ⟨g, hg, hgJ⟩
  have hg'J' : g' ∈ J' := hpreds g' hg'f hg'J
  obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hg'f hcov
  obtain ⟨a, b, hab, ha, hb⟩ := hints
  have hyX : y ∈ X := by
    rcases hy2.eq_or_eq_of_isLink hab with h | h
    · rw [h]; exact ha
    · rw [h]; exact hb
  obtain ⟨z, hz⟩ := hy1
  have hzX : z ∈ X := hX.2.2.1 g' hg'J' y z hz hyX
  exact hmin g' ⟨hA.mem_left hg'f, hg'J, ⟨y, z, hz, hyX, hzX⟩,
    fun h hh hhJ => hpreds h (hA.trans hh hg'f) hhJ⟩ hg'f

/-- A `P`-maximal edge of a component of an ideal is maximal in the ideal. -/
lemma Admissible.max_in_ideal (hA : Admissible H P) {I : Set β} (hI : IsIdeal H P I)
    {X : Set α} (hX : IsComp H I X) {e : β} (he : e ∈ edgesIn H I X)
    (hmax : ∀ c ∈ edgesIn H I X, ¬ P e c) : ∀ c ∈ I, ¬ P e c := by
  intro c hcI hec
  obtain ⟨c', hc'I, hec', hcov⟩ := hA.exists_cover_above hI ⟨c, hcI, hec⟩
  obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hec' hcov
  obtain ⟨a, b, hab, ha, hb⟩ := he.2
  have hyX : y ∈ X := by
    rcases hy1.eq_or_eq_of_isLink hab with h | h
    · rw [h]; exact ha
    · rw [h]; exact hb
  obtain ⟨z, hz⟩ := hy2
  have hzX := hX.2.2.1 c' hc'I y z hz hyX
  exact hmax c' ⟨hc'I, y, z, hz, hyX, hzX⟩ hec'

/-- Closure persists under enlarging the ideal while the component is retained. -/
lemma Admissible.closed_persist (hA : Admissible H P) {J I : Set β} (hJ : IsIdeal H P J)
    (hI : IsIdeal H P I) (hJI : J ⊆ I) {X : Set α} (hX : IsComp H I X)
    (hcl : IsClosed H P J X) : IsClosed H P I X ∧ edgesIn H I X = edgesIn H J X := by
  constructor
  · intro f hf hint
    obtain ⟨f', hf', hint'⟩ := hA.desc hJ hX hf.1 (fun h => hf.2.1 (hJI h)) hint
      (fun g hg hgJ => by
        by_contra hgI
        exact hgI (hf.2.2 g hg))
    exact hcl f' hf' hint'
  · ext e
    constructor
    · rintro ⟨heI, hint⟩
      refine ⟨?_, hint⟩
      by_contra heJ
      obtain ⟨f', hf', hint'⟩ := hA.desc hJ hX (hI.1 heI) heJ hint
        (fun g hg _ => hI.2 g e hg heI)
      exact hcl f' hf' hint'
    · rintro ⟨heJ, hint⟩
      exact ⟨hJI heJ, hint⟩

/-! ### The exchange producing a closed tree component -/

/-- If an ideal has two distinct tree components, size-preserving exchanges produce an ideal
with a closed tree component. -/
lemma Admissible.exists_closed_aux (hA : Admissible H P) :
    ∀ n : ℕ, ∀ (J : Set β) (A B : Set α), IsIdeal H P J → IsTreeComp H J A →
      IsTreeComp H J B → A ≠ B → A.ncard + B.ncard ≤ n →
      ∃ J', IsIdeal H P J' ∧ J'.ncard = J.ncard ∧ ∃ X, IsTreeComp H J' X ∧ IsClosed H P J' X := by
  intro n
  induction n with
  | zero =>
    intro J A B _ hAt _ _ hn
    have := (Set.ncard_pos (hA.finV.subset hAt.1.2.1)).2 hAt.1.1
    omega
  | succ n ih =>
    intro J A B hJ hAt hBt hAB hn
    by_cases hAc : IsClosed H P J A
    · exact ⟨J, hJ, rfl, A, hAt, hAc⟩
    by_cases hBc : IsClosed H P J B
    · exact ⟨J, hJ, rfl, B, hBt, hBc⟩
    simp only [IsClosed, not_forall, not_not] at hAc hBc
    obtain ⟨b', hb'min, hb'int⟩ := hAc
    obtain ⟨b, hbmin, hbint⟩ := hBc
    have hJfin : J.Finite := hA.finE.subset hJ.1
    have hAfin : A.Finite := hA.finV.subset hAt.1.2.1
    have hBfin : B.Finite := hA.finV.subset hBt.1.2.1
    have hBpos : 0 < B.ncard := (Set.ncard_pos hBfin).2 hBt.1.1
    -- A has an edge
    have hedge : (edgesIn H J A).Nonempty := by
      obtain ⟨x, y, hxy, hx, hy⟩ := hb'int
      have hne := hA.link_ne hxy
      have h2 : ({x, y} : Set α).ncard ≤ A.ncard :=
        Set.ncard_le_ncard (Set.insert_subset hx (Set.singleton_subset_iff.2 hy)) hAfin
      rw [Set.ncard_pair hne] at h2
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := hAt.2
      rw [hemp] at this
      simp at this
      omega
    obtain ⟨a, haE, hamax⟩ := hA.exists_max (edgesIn_subset J A) hedge
    have hamaxJ := hA.max_in_ideal hJ hAt.1 haE hamax
    obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet (edgesIn_subset J A haE)
    have haJ : a ∈ J := haE.1
    have hbJ : b ∉ J := hbmin.2.1
    have hnab : ¬ P a b := by
      intro hab
      have hcov : ∀ c, P a c → ¬ P c b := fun c hac hcb => hamaxJ c (hbmin.2.2 c hcb) hac
      obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hab hcov
      obtain ⟨p, q, hpq, hp, hq⟩ := haE.2
      obtain ⟨p', q', hpq', hp', hq'⟩ := hbint
      have hyA : y ∈ A := by
        rcases hy1.eq_or_eq_of_isLink hpq with h | h
        · rw [h]; exact hp
        · rw [h]; exact hq
      have hyB : y ∈ B := by
        rcases hy2.eq_or_eq_of_isLink hpq' with h | h
        · rw [h]; exact hp'
        · rw [h]; exact hq'
      exact Set.disjoint_left.1 (hAt.1.disjoint_of_ne hBt.1 hAB) hyA hyB
    have hnba : ¬ P b a := fun h => hbJ (hJ.2 b a h haJ)
    set J'' : Set β := insert b (J \ {a}) with hJ''
    have hJ''ideal : IsIdeal H P J'' := by
      refine ⟨Set.insert_subset hbmin.1 (Set.sdiff_subset.trans hJ.1), ?_⟩
      intro x y hxy hy
      rcases hy with rfl | ⟨hyJ, hya⟩
      · refine Or.inr ⟨hbmin.2.2 x hxy, ?_⟩
        intro h
        rw [Set.mem_singleton_iff] at h
        subst h
        exact hnab hxy
      · refine Or.inr ⟨hJ.2 x y hxy hyJ, ?_⟩
        intro h
        rw [Set.mem_singleton_iff] at h
        subst h
        exact hamaxJ y hyJ hxy
    have hJ''card : J''.ncard = J.ncard := by
      have hbn : b ∉ J \ {a} := fun h => hbJ h.1
      rw [hJ'', Set.ncard_insert_of_notMem hbn (hJfin.subset Set.sdiff_subset),
        Set.ncard_sdiff_singleton_of_mem haJ]
      have := (Set.ncard_pos hJfin).2 ⟨a, haJ⟩
      omega
    obtain ⟨A1, A2, hA1, hA2, hdisj, hunion, huA1, hvA2⟩ :=
      tree_split hA.finV hA.finE hAt haE hl
    have hnew : ∀ (C : Set α), C ⊆ A → ∀ e ∈ J'', e ∉ J \ {a} →
        ∀ x y, H.IsLink e x y → x ∉ C ∧ y ∉ C := by
      intro C hCA e he heS x y hxy
      have heb : e = b := by
        rcases he with h | h
        · exact h
        · exact absurd h heS
      subst heb
      obtain ⟨p', q', hpq', hp', hq'⟩ := hbint
      have hdAB := Set.disjoint_left.1 (hAt.1.disjoint_of_ne hBt.1 hAB)
      rcases hxy.eq_and_eq_or_eq_and_eq hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun h => hdAB (hCA h) hp', fun h => hdAB (hCA h) hq'⟩
      · exact ⟨fun h => hdAB (hCA h) hq', fun h => hdAB (hCA h) hp'⟩
    have hsub1 : A1 ⊆ A := hunion ▸ Set.subset_union_left
    have hsub2 : A2 ⊆ A := hunion ▸ Set.subset_union_right
    have hA1' : IsTreeComp H J'' A1 := by
      obtain ⟨h1, h2⟩ := hA1.1.mono_edges (S' := J'') (Set.subset_insert _ _)
        (hnew A1 hsub1)
      exact ⟨h1, by rw [h2]; exact hA1.2⟩
    have hA2' : IsTreeComp H J'' A2 := by
      obtain ⟨h1, h2⟩ := hA2.1.mono_edges (S' := J'') (Set.subset_insert _ _)
        (hnew A2 hsub2)
      exact ⟨h1, by rw [h2]; exact hA2.2⟩
    have hne12 : A1 ≠ A2 := by
      intro h
      rw [h, disjoint_self, Set.bot_eq_empty] at hdisj
      exact hA2.1.1.ne_empty hdisj
    have hcardA : A.ncard = A1.ncard + A2.ncard := by
      rw [← hunion, Set.ncard_union_eq hdisj (hA.finV.subset hA1.1.2.1)
        (hA.finV.subset hA2.1.2.1)]
    obtain ⟨J3, hJ3, hc3, X, hX1, hX2⟩ :=
      ih J'' A1 A2 hJ''ideal hA1' hA2' hne12 (by omega)
    exact ⟨J3, hJ3, hc3.trans hJ''card, X, hX1, hX2⟩

lemma Admissible.exists_closed (hA : Admissible H P) {J : Set β} (hJ : IsIdeal H P J)
    {A B : Set α} (hAt : IsTreeComp H J A) (hBt : IsTreeComp H J B) (hAB : A ≠ B) :
    ∃ J', IsIdeal H P J' ∧ J'.ncard = J.ncard ∧ ∃ X, IsTreeComp H J' X ∧ IsClosed H P J' X :=
  hA.exists_closed_aux _ J A B hJ hAt hBt hAB le_rfl

/-! ### Linear extensions placing `I` first and `e` last in `I` -/

/-- `ℓ` is a linear extension of `P` placing the ideal `I` first and `e ∈ I` last within `I`. -/
structure IsFam (H : Graph α β) (P : β → β → Prop) (I : Set β) (e : β) (ℓ : β → ℕ) : Prop where
  inj : Set.InjOn ℓ E(H)
  mono : ∀ a b, P a b → ℓ a < ℓ b
  Ifirst : ∀ g ∈ I, ∀ f ∈ E(H) \ I, ℓ g < ℓ f
  elast : ∀ g ∈ I, g ≠ e → ℓ g < ℓ e

open Classical in
/-- The layering: `I \ {e}` (0), then `e` (1), then everything else (2). -/
noncomputable def layer (I : Set β) (e g : β) : ℕ :=
  if g ∈ I ∧ g ≠ e then 0 else if g = e then 1 else 2

lemma layer_mem {I : Set β} {e g : β} (hg : g ∈ I) (hne : g ≠ e) : layer I e g = 0 := by
  simp [layer, hg, hne]

lemma layer_e (I : Set β) (e : β) : layer I e e = 1 := by
  simp [layer]

lemma layer_out {I : Set β} {e g : β} (hg : g ∉ I) (hne : g ≠ e) : layer I e g = 2 := by
  simp [layer, hg, hne]

lemma layer_le_one {I : Set β} {e g : β} (hg : g ∈ I) (heI : e ∈ I) : layer I e g ≤ 1 := by
  by_cases h : g = e
  · subst h; simp [layer_e]
  · simp [layer_mem hg h]

lemma Admissible.exists_fam_gen (hA : Admissible H P) {I : Set β} {e : β} (hI : IsIdeal H P I)
    (heI : e ∈ I) (Q : β → β → Prop) (hPQ : ∀ a b, P a b → Q a b) (hirr : ∀ a, ¬ Q a a)
    (htr : ∀ {a b c}, Q a b → Q b c → Q a c) (hQE : ∀ {a b}, Q a b → a ∈ E(H) ∧ b ∈ E(H))
    (hlay : ∀ {a b}, Q a b → layer I e a ≤ layer I e b) :
    ∃ ℓ, IsFam H P I e ℓ ∧ ∀ a b, Q a b → ℓ a < ℓ b := by
  obtain ⟨ℓ, hinj, hQ, hL⟩ := exists_linear_ext hA.finE Q hirr htr hQE (layer I e) hlay
  refine ⟨ℓ, ⟨hinj, fun a b h => hQ a b (hPQ a b h), ?_, ?_⟩, hQ⟩
  · intro g hg f hf
    refine hL g (hI.1 hg) f hf.1 ?_
    have hfe : f ≠ e := fun h => hf.2 (h ▸ heI)
    rw [layer_out hf.2 hfe]
    have := layer_le_one hg heI
    omega
  · intro g hg hge
    refine hL g (hI.1 hg) e (hI.1 heI) ?_
    rw [layer_mem hg hge, layer_e]
    omega

lemma Admissible.layer_mono (hA : Admissible H P) {I : Set β} {e : β} (hI : IsIdeal H P I)
    (heI : e ∈ I) (hemax : ∀ c ∈ I, ¬ P e c) {a b : β} (h : P a b) :
    layer I e a ≤ layer I e b := by
  by_cases haI : a ∈ I
  · by_cases hae : a = e
    · subst hae
      have hbI : b ∉ I := fun hb => hemax b hb h
      have hbe : b ≠ a := fun hh => hA.irrefl _ (hh ▸ h)
      rw [layer_e, layer_out hbI hbe]; omega
    · rw [layer_mem haI hae]; omega
  · have hbI : b ∉ I := fun hb => haI (hI.2 a b h hb)
    have hae : a ≠ e := fun hh => haI (hh ▸ heI)
    have hbe : b ≠ e := fun hh => hbI (hh ▸ heI)
    rw [layer_out haI hae, layer_out hbI hbe]

lemma Admissible.exists_fam (hA : Admissible H P) {I : Set β} {e : β} (hI : IsIdeal H P I)
    (heI : e ∈ I) (hemax : ∀ c ∈ I, ¬ P e c) : ∃ ℓ, IsFam H P I e ℓ := by
  obtain ⟨ℓ, h, -⟩ := hA.exists_fam_gen hI heI P (fun _ _ h => h) hA.irrefl hA.trans
    (fun h => ⟨hA.mem_left h, hA.mem_right h⟩) (fun h => hA.layer_mono hI heI hemax h)
  exact ⟨ℓ, h⟩

/-- Two incomparable edges outside `I` can be ordered either way by such an extension. -/
lemma Admissible.exists_fam_pair (hA : Admissible H P) {I : Set β} {e : β}
    (hI : IsIdeal H P I) (heI : e ∈ I) (hemax : ∀ c ∈ I, ¬ P e c) {f g : β}
    (hf : f ∈ E(H)) (hfI : f ∉ I) (hg : g ∈ E(H)) (hgI : g ∉ I) (hfg : f ≠ g)
    (h1 : ¬ P f g) (h2 : ¬ P g f) : ∃ ℓ, IsFam H P I e ℓ ∧ ℓ f < ℓ g := by
  let Q : β → β → Prop := fun a b => P a b ∨ ((a = f ∨ P a f) ∧ (b = g ∨ P g b))
  have hirr : ∀ a, ¬ Q a a := by
    intro a ha
    rcases ha with ha | ⟨ha1, ha2⟩
    · exact hA.irrefl a ha
    · rcases ha1 with rfl | ha1 <;> rcases ha2 with ha2 | ha2
      · exact hfg ha2
      · exact h2 ha2
      · subst ha2; exact h2 ha1
      · exact h2 (hA.trans ha2 ha1)
  have htr : ∀ {a b c}, Q a b → Q b c → Q a c := by
    intro a b c hab hbc
    rcases hab with hab | ⟨ha1, hb2⟩
    · rcases hbc with hbc | ⟨hb1, hc2⟩
      · exact Or.inl (hA.trans hab hbc)
      · refine Or.inr ⟨?_, hc2⟩
        rcases hb1 with rfl | hb1
        · exact Or.inr hab
        · exact Or.inr (hA.trans hab hb1)
    · rcases hbc with hbc | ⟨hb1, hc2⟩
      · refine Or.inr ⟨ha1, ?_⟩
        rcases hb2 with rfl | hb2
        · exact Or.inr hbc
        · exact Or.inr (hA.trans hb2 hbc)
      · exfalso
        rcases hb2 with hb2 | hb2 <;> rcases hb1 with hb1 | hb1
        · exact hfg (hb1.symm.trans hb2)
        · subst hb2; exact h2 hb1
        · subst hb1; exact h2 hb2
        · exact h2 (hA.trans hb2 hb1)
  have hQE : ∀ {a b}, Q a b → a ∈ E(H) ∧ b ∈ E(H) := by
    intro a b hab
    rcases hab with hab | ⟨ha1, hb2⟩
    · exact ⟨hA.mem_left hab, hA.mem_right hab⟩
    · refine ⟨?_, ?_⟩
      · rcases ha1 with rfl | ha1
        · exact hf
        · exact hA.mem_left ha1
      · rcases hb2 with rfl | hb2
        · exact hg
        · exact hA.mem_right hb2
  have hlay : ∀ {a b}, Q a b → layer I e a ≤ layer I e b := by
    intro a b hab
    rcases hab with hab | ⟨ha1, hb2⟩
    · exact hA.layer_mono hI heI hemax hab
    · have hbI : b ∉ I := by
        rcases hb2 with rfl | hb2
        · exact hgI
        · exact fun hb => hgI (hI.2 g b hb2 hb)
      have hbe : b ≠ e := fun hh => hbI (hh ▸ heI)
      rw [layer_out hbI hbe]
      by_cases haI : a ∈ I
      · have := layer_le_one haI heI; omega
      · have hae : a ≠ e := fun hh => haI (hh ▸ heI)
        rw [layer_out haI hae]
  obtain ⟨ℓ, hfam, hQ⟩ := hA.exists_fam_gen hI heI Q (fun _ _ h => Or.inl h) hirr htr hQE hlay
  exact ⟨ℓ, hfam, hQ f g (Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)⟩

/-! ### Exchange argument of the closed-tree reduction -/

/-- The core exchange: replacing the maximal edge `e` of `X` by a minimal edge `f` outside `I`
that does not follow `e` leaves a closed tree component `B ⊊ X`. -/
lemma Admissible.exchange_closed (hA : Admissible H P) {I : Set β} (hI : IsIdeal H P I)
    {X B : Set α} {e f : β} (heI : e ∈ I) (hemax : ∀ c ∈ I, ¬ P e c)
    (hf : IsMinOut H P I f) (hnot : ¬ P e f)
    (hcross : ∀ g, IsMinOut H P I g → Crosses H X g) {y z : α} (hfl : H.IsLink f y z)
    (hyX : y ∈ X) (hzX : z ∉ X) (hB : IsTreeComp H (I \ {e}) B) (hBX : B ⊆ X) (hyB : y ∉ B)
    (hnotint : ¬ Internal H B e) :
    IsIdeal H P (insert f (I \ {e})) ∧ (insert f (I \ {e})).ncard = I.ncard ∧
      IsTreeComp H (insert f (I \ {e})) B ∧ IsClosed H P (insert f (I \ {e})) B := by
  have hIfin : I.Finite := hA.finE.subset hI.1
  have hzB : z ∉ B := fun h => hzX (hBX h)
  have hideal : IsIdeal H P (insert f (I \ {e})) := by
    refine ⟨Set.insert_subset hf.1 (Set.sdiff_subset.trans hI.1), ?_⟩
    intro a b hab hb
    rcases hb with rfl | ⟨hbI, hbe⟩
    · refine Or.inr ⟨hf.2.2 a hab, ?_⟩
      intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hnot hab
    · refine Or.inr ⟨hI.2 a b hab hbI, ?_⟩
      intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hemax b hbI hab
  have hfn : f ∉ I \ {e} := fun h => hf.2.1 h.1
  have hcard : (insert f (I \ {e})).ncard = I.ncard := by
    rw [Set.ncard_insert_of_notMem hfn (hIfin.subset Set.sdiff_subset),
      Set.ncard_sdiff_singleton_of_mem heI]
    have := (Set.ncard_pos hIfin).2 ⟨e, heI⟩
    omega
  have htree : IsTreeComp H (insert f (I \ {e})) B := by
    obtain ⟨h1, h2⟩ := hB.1.mono_edges (S' := insert f (I \ {e})) (Set.subset_insert _ _) (by
      intro g hg hgS x y' hxy
      have hgf : g = f := by
        rcases hg with h | h
        · exact h
        · exact absurd h hgS
      subst hgf
      rcases hxy.eq_and_eq_or_eq_and_eq hfl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hyB, hzB⟩
      · exact ⟨hzB, hyB⟩)
    exact ⟨h1, by rw [h2]; exact hB.2⟩
  refine ⟨hideal, hcard, htree, ?_⟩
  intro g hg hint
  by_cases hge : g = e
  · subst hge
    exact hnotint hint
  have hgI : g ∉ I := fun h => hg.2.1 (Or.inr ⟨h, hge⟩)
  have hgf : g ≠ f := fun h => hg.2.1 (Or.inl h)
  by_cases hgmin : IsMinOut H P I g
  · obtain ⟨p, q, hpq, hp, hq⟩ := hcross g hgmin
    obtain ⟨p', q', hpq', hp', hq'⟩ := hint
    rcases hpq.eq_and_eq_or_eq_and_eq hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hq (hBX hq')
    · exact hq (hBX hp')
  · have hex : ∃ h, P h g ∧ h ∉ I := by
      by_contra hcon
      push Not at hcon
      exact hgmin ⟨hg.1, hgI, fun h hh => by
        by_contra hhI
        exact absurd (hcon h hh) (by simpa using hhI)⟩
    obtain ⟨h, hhg, hhI⟩ := hex
    have hhmem := hg.2.2 h hhg
    have hhf : h = f := by
      rcases hhmem with h' | h'
      · exact h'
      · exact absurd h'.1 hhI
    subst hhf
    have hcov : ∀ c, P h c → ¬ P c g := by
      intro c hhc hcg
      have hcI : c ∉ I := fun hc => hhI (hI.2 h c hhc hc)
      have hcmem := hg.2.2 c hcg
      have hch : c = h := by
        rcases hcmem with h' | h'
        · exact h'
        · exact absurd h'.1 hcI
      subst hch
      exact hA.irrefl _ hhc
    obtain ⟨w, hw1, hw2⟩ := hA.cover_adj hhg hcov
    obtain ⟨p', q', hpq', hp', hq'⟩ := hint
    have hwB : w ∈ B := by
      rcases hw2.eq_or_eq_of_isLink hpq' with h' | h'
      · rw [h']; exact hp'
      · rw [h']; exact hq'
    rcases hw1.eq_or_eq_of_isLink hfl with h' | h'
    · rw [h'] at hwB; exact hyB hwB
    · rw [h'] at hwB; exact hzB hwB

/-! ### The closed-tree reduction lemma -/

/-- `(I, X)`: `I` is an ideal, `X` a closed tree component of `H[I]`, and every minimal edge
outside `I` crosses the boundary of `X` (has exactly one end in `X`). -/
structure IsReduced (H : Graph α β) (P : β → β → Prop) (I : Set β) (X : Set α) : Prop where
  ideal : IsIdeal H P I
  tree : IsTreeComp H I X
  closed : IsClosed H P I X
  cross : ∀ f, IsMinOut H P I f → Crosses H X f

/-- **Closed-tree reduction** (`lem:characterization-closed-tree-reduction`), the part not
involving information flow: from a closed tree component `A` of an ideal `J` we get an ideal
`I` with `|I| ≥ |J|` and a closed tree component `X ⊆ A` such that every minimal edge outside
`I` crosses the boundary of `X`, and every maximal edge of `X` precedes all edges outside `I`.
(The bounds `|F| ≥ r - 1` resp. `r - 2` are in `Admissible.card_F_lower`.) -/
theorem Admissible.closed_tree_reduction (hA : Admissible H P) {J : Set β} {A : Set α}
    (hJ : IsIdeal H P J) (hAt : IsTreeComp H J A) (hAc : IsClosed H P J A) :
    ∃ I X, IsReduced H P I X ∧ J.ncard ≤ I.ncard ∧ X ⊆ A ∧
      ∀ e ∈ edgesIn H I X, (∀ c ∈ edgesIn H I X, ¬ P e c) → ∀ f ∈ E(H) \ I, P e f := by
  classical
  let Fm : Set β → Set α → Prop := fun I X =>
    IsIdeal H P I ∧ J.ncard ≤ I.ncard ∧ IsTreeComp H I X ∧ IsClosed H P I X ∧ X ⊆ A
  have hFm0 : Fm J A := ⟨hJ, le_rfl, hAt, hAc, subset_rfl⟩
  have hex : ∃ n, ∃ I X, Fm I X ∧ X.ncard = n := ⟨_, J, A, hFm0, rfl⟩
  obtain ⟨I0, X, hFm, hXn⟩ := Nat.find_spec hex
  have hmin : ∀ I' X', Fm I' X' → X.ncard ≤ X'.ncard := fun I' X' h => by
    rw [hXn]; exact Nat.find_min' hex ⟨I', X', h, rfl⟩
  obtain ⟨hI0, hJI0, hXt0, hXc0, hXA⟩ := hFm
  let S : Set (Set β) := {I' | IsIdeal H P I' ∧ I0 ⊆ I' ∧ IsComp H I' X}
  have hSfin : S.Finite := hA.finE.finite_subsets.subset fun I' hI' => hI'.1.1
  obtain ⟨I, hIS, hImax⟩ := Set.exists_max_image S Set.ncard hSfin ⟨I0, hI0, subset_rfl, hXt0.1⟩
  obtain ⟨hI, hI0I, hXcomp⟩ := hIS
  obtain ⟨hclosed, hEeq⟩ := hA.closed_persist hI0 hI hI0I hXcomp hXc0
  have hXt : IsTreeComp H I X := ⟨hXcomp, by rw [hEeq]; exact hXt0.2⟩
  have hIfin : I.Finite := hA.finE.subset hI.1
  have hJI : J.ncard ≤ I.ncard := hJI0.trans (Set.ncard_le_ncard hI0I hIfin)
  have hcross : ∀ f, IsMinOut H P I f → Crosses H X f := by
    intro f hf
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hf.1
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
    · exact absurd ⟨x, y, hl, hx, hy⟩ (hclosed f hf)
    · exact ⟨x, y, hl, hx, hy⟩
    · exact ⟨y, x, hl.symm, hy, hx⟩
    · exfalso
      have hins : insert f I ∈ S := by
        refine ⟨hI.insert hf, hI0I.trans (Set.subset_insert _ _), ?_⟩
        refine (hXcomp.mono_edges (Set.subset_insert _ _) (fun e he heS x' y' hl' => ?_)).1
        have hef : e = f := he.resolve_right heS
        subst hef
        rcases hl'.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hx, hy⟩
        · exact ⟨hy, hx⟩
      have := hImax _ hins
      rw [Set.ncard_insert_of_notMem hf.2.1 hIfin] at this
      omega
  have hP3 : ∀ e ∈ edgesIn H I X, (∀ c ∈ edgesIn H I X, ¬ P e c) → ∀ f ∈ E(H) \ I, P e f := by
    intro e he hemax f hf
    suffices h : ∀ f, IsMinOut H P I f → P e f by
      obtain ⟨f', hf'min, hf'⟩ := hA.exists_minOut_le (I := I) hf.1 hf.2
      rcases hf' with rfl | h'
      · exact h _ hf'min
      · exact hA.trans (h f' hf'min) h'
    intro f hfmin
    by_contra hnot
    have hemaxI := hA.max_in_ideal hI hXcomp he hemax
    have heI : e ∈ I := he.1
    obtain ⟨x0, x1, hl, hx0, hx1⟩ := he.2
    obtain ⟨X0, X1, hX0, hX1, hdisj, hunion, hx0X0, hx1X1⟩ :=
      tree_split hA.finV hA.finE hXt he hl
    obtain ⟨y, z, hfl, hyX, hzX⟩ := hcross f hfmin
    have hX0fin : X0.Finite := hA.finV.subset hX0.1.2.1
    have hX1fin : X1.Finite := hA.finV.subset hX1.1.2.1
    have hcardX : X.ncard = X0.ncard + X1.ncard := by
      rw [← hunion, Set.ncard_union_eq hdisj hX0fin hX1fin]
    have hpos0 : 0 < X0.ncard := (Set.ncard_pos hX0fin).2 hX0.1.1
    have hpos1 : 0 < X1.ncard := (Set.ncard_pos hX1fin).2 hX1.1.1
    have hsub0 : X0 ⊆ X := hunion ▸ Set.subset_union_left
    have hsub1 : X1 ⊆ X := hunion ▸ Set.subset_union_right
    have hyU : y ∈ X0 ∪ X1 := hunion ▸ hyX
    have hfinal : ∃ B, ∃ I', IsIdeal H P I' ∧ I'.ncard = I.ncard ∧ IsTreeComp H I' B ∧
        IsClosed H P I' B ∧ B ⊆ X ∧ B.ncard < X.ncard := by
      rcases hyU with hy0 | hy1
      · have hyB : y ∉ X1 := fun h => Set.disjoint_left.1 hdisj hy0 h
        have hnotint : ¬ Internal H X1 e := fun h => by
          have := (h.ends_mem hl).1
          exact Set.disjoint_left.1 hdisj hx0X0 this
        obtain ⟨h1, h2, h3, h4⟩ := hA.exchange_closed hI heI hemaxI hfmin hnot
          hcross hfl hyX hzX hX1 hsub1 hyB hnotint
        exact ⟨X1, _, h1, h2, h3, h4, hsub1, by omega⟩
      · have hyB : y ∉ X0 := fun h => Set.disjoint_left.1 hdisj h hy1
        have hnotint : ¬ Internal H X0 e := fun h => by
          have := (h.ends_mem hl).2
          exact Set.disjoint_left.1 hdisj this hx1X1
        obtain ⟨h1, h2, h3, h4⟩ := hA.exchange_closed hI heI hemaxI hfmin hnot
          hcross hfl hyX hzX hX0 hsub0 hyB hnotint
        exact ⟨X0, _, h1, h2, h3, h4, hsub0, by omega⟩
    obtain ⟨B, I', hI', hI'c, hI't, hI'cl, hBX, hBlt⟩ := hfinal
    have := hmin I' B ⟨hI', by rw [hI'c]; exact hJI, hI't, hI'cl, hBX.trans hXA⟩
    omega
  exact ⟨I, X, ⟨hI, hXt, hclosed, hcross⟩, hJI, hXA, hP3⟩

end Lax630294Proofs.CallOrder
