import Lax630294Proofs.QuotientBlocks
import Mathlib.Combinatorics.Graph.Maps

/-!
# The quotient graph `Q`

`contract G f` identifies vertices along `f`, deletes the edges internal to a fibre and keeps every
other edge, with its identity and its original ends.  `quotient G = contract G (blk G)` has the
blocks (maximal two-tree sets) as vertices.
-/

namespace Lax630294Proofs.QuotientDef

open Graph Lax630294Proofs.QuotientBlocks

variable {α β γ : Type*}

/-- Contract the fibres of `f`; edges inside a fibre are deleted, all others are kept. -/
def contract (G : Graph α β) (f : α → γ) : Graph γ β :=
  (G.map f).restrict {e | ∃ x y, G.IsLink e x y ∧ f x ≠ f y}

lemma contract_isLink {G : Graph α β} {f : α → γ} {e : β} {U W : γ} :
    (contract G f).IsLink e U W ↔ ∃ x y, G.IsLink e x y ∧ f x = U ∧ f y = W ∧ U ≠ W := by
  constructor
  · rintro ⟨⟨x0, y0, hl0, hne0⟩, x, y, hl, hx, hy⟩
    refine ⟨x, y, hl, hx, hy, ?_⟩
    rcases hl0.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hx, ← hy]; exact hne0
    · rw [← hx, ← hy]; exact fun h => hne0 h.symm
  · rintro ⟨x, y, hl, hx, hy, hne⟩
    exact ⟨⟨x, y, hl, by rw [hx, hy]; exact hne⟩, x, y, hl, hx, hy⟩

/-- The quotient of `G` by its blocks (maximal two-tree sets): vertices are the blocks. -/
def quotient (G : Graph α β) : Graph (Set α) β := contract G (blk G)

lemma quotient_isLink {G : Graph α β} {e : β} {U W : Set α} :
    (quotient G).IsLink e U W ↔
      ∃ x y, G.IsLink e x y ∧ blk G x = U ∧ blk G y = W ∧ U ≠ W := contract_isLink

end Lax630294Proofs.QuotientDef
