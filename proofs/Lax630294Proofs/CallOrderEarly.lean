import Lax630294Proofs.CallOrderCanonical

/-!
# The other early components are unicyclic (`cor:characterization-early-components`)
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- **Early components** (`cor:characterization-early-components`).  Let `I` be an ideal with
`|I| = r - 2` having a tree component `X` such that every minimal edge outside `I` crosses the
boundary of `X` (this holds for the ideal of the canonical lemma).  Then `H[I]` has exactly two
tree components, `X` and a second one `Y`, which is closed; all other components are unicyclic;
and every minimal edge of `F = E(H) \ I` has one end in `X` and the other in `Y`. -/
theorem Admissible.early_components (hA : Admissible H P) (hr : 4 ≤ V(H).ncard)
    (hE : E(H).ncard = 2 * V(H).ncard - 4) {I : Set β} {X : Set α} (hI : IsIdeal H P I)
    (hcard : I.ncard + 2 = V(H).ncard) (hX : IsTreeComp H I X)
    (hcross : ∀ f, IsMinOut H P I f → Crosses H X f) :
    ∃ Y, IsTreeComp H I Y ∧ Y ≠ X ∧ (∀ A, IsTreeComp H I A → A = X ∨ A = Y) ∧
      IsClosed H P I Y ∧ (∀ f, IsMinOut H P I f → ∃ x y, H.IsLink f x y ∧ x ∈ X ∧ y ∈ Y) ∧
      ∀ D, IsComp H I D → D ≠ X → D ≠ Y → IsUnicyclicComp H I D := by
  obtain ⟨A, B, hAt, hBt, hAB⟩ := exists_two_tree_comps hA.finV hA.finE hI.1 hcard
  obtain ⟨Y, hY, hYX⟩ : ∃ Y, IsTreeComp H I Y ∧ Y ≠ X := by
    by_cases h : A = X
    · exact ⟨B, hBt, fun hh => hAB (h.trans hh.symm)⟩
    · exact ⟨A, hAt, h⟩
  have hdisj : ∀ Z, IsTreeComp H I Z → Z ≠ X → Disjoint Z X := fun Z hZ hZX =>
    hZ.1.disjoint_of_ne hX.1 hZX
  have hclosedZ : ∀ Z, IsTreeComp H I Z → Z ≠ X → IsClosed H P I Z := by
    intro Z hZ hZX f hf hint
    obtain ⟨p, q, hpq, hp, hq⟩ := hcross f hf
    exact Set.disjoint_left.1 (hdisj Z hZ hZX) (hint.ends_mem hpq).1 hp
  have hsat : ∀ Z, IsTreeComp H I Z → Z ≠ X → ∀ f, IsMinOut H P I f → Crosses H Z f :=
    fun Z hZ hZX => (hA.saturation hr hE hI (by omega) hZ (hclosedZ Z hZ hZX)).2
  have hXY : ∀ f, IsMinOut H P I f → ∃ x y, H.IsLink f x y ∧ x ∈ X ∧ y ∈ Y := by
    intro f hf
    obtain ⟨p, q, hpq, hp, hq⟩ := hcross f hf
    obtain ⟨p', q', hpq', hp', hq'⟩ := hsat Y hY hYX f hf
    rcases hpq.eq_and_eq_or_eq_and_eq hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hp (fun h => Set.disjoint_left.1 (hdisj Y hY hYX) hp' h)
    · exact ⟨p, q, hpq, hp, hp'⟩
  have hall : ∀ Z, IsTreeComp H I Z → Z = X ∨ Z = Y := by
    intro Z hZ
    by_contra hcon
    push Not at hcon
    obtain ⟨hZX, hZY⟩ := hcon
    have hsplit : (E(H) \ I).ncard + I.ncard = E(H).ncard :=
      Set.ncard_sdiff_add_ncard_of_subset hI.1 hA.finE
    obtain ⟨g, hg⟩ : (E(H) \ I).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨f, hf, -⟩ := hA.exists_minOut_le (I := I) hg.1 hg.2
    obtain ⟨x, y, hxy, hx, hy⟩ := hXY f hf
    obtain ⟨p, q, hpq, hp, hq⟩ := hsat Z hZ hZX f hf
    rcases hxy.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Set.disjoint_left.1 (hdisj Z hZ hZX) hp hx
    · exact Set.disjoint_left.1 (hZ.1.disjoint_of_ne hY.1 hZY) hp hy
  refine ⟨Y, hY, hYX, hall, hclosedZ Y hY hYX, hXY, ?_⟩
  intro D hD hDX hDY
  exact unicyclic_of_two_trees hA.finV hA.finE hI.1 (by omega) hX hY (Ne.symm hYX) hall hD hDX hDY

/-- `cor:characterization-early-components` for the ideal of the canonical lemma. -/
theorem Admissible.early_components_of_canonical (hA : Admissible H P) (hr : 4 ≤ V(H).ncard)
    (hE : E(H).ncard = 2 * V(H).ncard - 4) {I : Set β} {X : Set α} {e : β} {x0 x1 : α}
    (hC : IsCanonical H P I X e x0 x1) :
    ∃ Y, IsTreeComp H I Y ∧ Y ≠ X ∧ (∀ A, IsTreeComp H I A → A = X ∨ A = Y) ∧
      IsClosed H P I Y ∧ (∀ f, IsMinOut H P I f → ∃ x y, H.IsLink f x y ∧ x ∈ X ∧ y ∈ Y) ∧
      ∀ D, IsComp H I D → D ≠ X → D ≠ Y → IsUnicyclicComp H I D :=
  hA.early_components hr hE hC.ideal hC.card_I hC.tree hC.cross

end Lax630294Proofs.CallOrder
