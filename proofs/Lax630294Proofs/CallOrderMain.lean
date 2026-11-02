import Lax630294Proofs.CallOrderEarly
import Lax630294Proofs.CallOrderBridge

/-!
# Causal orders and canonical form: summary of the main statements

With `hA : Admissible H P` and `hr : 4 ≤ V(H).ncard`:

* `Admissible.lower_bound` (`cor:characterization-call-lower-bound`);
* `Admissible.canonical_ideal` (`lem:characterization-canonical-ideal`);
* `IsCanonical.isSpanningForest` : `IsSpanningForest H (E(H) \ I) 2`;
* `Admissible.early_components_of_canonical` (`cor:characterization-early-components`);
* `Admissible.saturation`, `Admissible.closed_tree_reduction`, `Admissible.card_F_lower`.
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping Lax630294.SpanningStructures

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- The canonical form gives a spanning forest of `H` with two components. -/
theorem IsCanonical.isSpanningForest [hH : H.Simple] {I : Set β} {X : Set α} {e : β}
    {x0 x1 : α} (hC : IsCanonical H P I X e x0 x1) : IsSpanningForest H (E(H) \ I) 2 := by
  obtain ⟨par, pe, hfor⟩ := hC.forest
  exact hfor.isSpanningForest Set.sdiff_subset hC.e_link.left_mem hC.e_link.right_mem
    hC.e_link.ne

/-- The paper's definition of a closed tree component. -/
def IsClosedPaper (H : Graph α β) (P : β → β → Prop) (J : Set β) (A : Set α) : Prop :=
  ¬ ∃ J', IsIdeal H P J' ∧ J ⊂ J' ∧ IsComp H J' A ∧ ∃ f ∈ J' \ J, Internal H A f

/-- The criterion used for `IsClosed` is equivalent to the paper's definition. -/
theorem Admissible.isClosed_iff (hA : Admissible H P) {J : Set β} {A : Set α}
    (hJ : IsIdeal H P J) (hAc : IsComp H J A) : IsClosed H P J A ↔ IsClosedPaper H P J A := by
  constructor
  · rintro hcl ⟨J', hJ', -, hcomp, f, hf, hint⟩
    obtain ⟨f', hf', hint'⟩ := hA.desc hJ hcomp (hJ'.1 hf.1) hf.2 hint
      (fun g hg _ => hJ'.2 g f hg hf.1)
    exact hcl f' hf' hint'
  · intro hp f hf hint
    apply hp
    refine ⟨insert f J, hJ.insert hf, ?_, ⟨hAc.1, hAc.2.1, ?_, ?_⟩, f,
      ⟨Set.mem_insert _ _, hf.2.1⟩, hint⟩
    · exact Set.ssubset_insert hf.2.1
    · intro e he x y hl hx
      rcases he with rfl | he
      · exact (hint.ends_mem hl).2
      · exact hAc.2.2.1 e he x y hl hx
    · exact fun x hx y hy => (hAc.2.2.2 x hx y hy).mono (Set.subset_insert _ _)

end Lax630294Proofs.CallOrder
