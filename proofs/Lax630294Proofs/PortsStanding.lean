import Lax630294Proofs.PortsMain

/-!
# Port selection under the standing hypotheses

Entry points for the final assembly (`cor:characterization-optimal-quotient-lift`):

* `compatible_actual_cycle_of_canonical`: for canonical data `(I, X, e, x0, x1)` of the causal order
  of `(G, ℓ)` on the quotient, and the second early tree `Y`, `CompatibleCycle G I Y e x0 x1` holds;
* `port_selection`: under the standing hypotheses (`G` finite, `ℓ` temporally connecting,
  `r ≥ 4`, `|E(Q)| = 2r - 4`), the canonical data exist and `CompatibleCycle` holds for them.

DEVIATION: neither injectivity of `ℓ` on `E(G)` nor `r ≥ 4`, `|E(Q)| = 2r-4` is used by the port
selection itself; they enter only through the existence of the canonical data
(`Admissible.canonical_ideal`, `Admissible.early_components_of_canonical`).
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.CallOrder Lax630294Proofs.CausalQuotient
  Lax630294Proofs.Quotient2Quotient Lax630294Proofs.QuotientDef Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- Build the standing context from canonical data. -/
theorem PCtx.of_canonical (hV : V(G).Finite) (hE : E(G).Finite)
    (hℓ : IsTemporallyConnected G ℓ) {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
    (hC : IsCanonical (quotient G) (causalQ G ℓ) I X e x0 x1)
    (hY : IsTreeComp (quotient G) I Y) (hYX : Y ≠ X) : PCtx G ℓ I X Y e x0 x1 :=
  ⟨hV, hE, hℓ, ⟨admissible hV hE (quotient_simple hV hE) hℓ, hC, hY, hYX⟩⟩

/-- **Compatible four-cycle** for given canonical data. -/
theorem compatible_actual_cycle_of_canonical (hV : V(G).Finite) (hE : E(G).Finite)
    (hℓ : IsTemporallyConnected G ℓ) {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
    (hC : IsCanonical (quotient G) (causalQ G ℓ) I X e x0 x1)
    (hY : IsTreeComp (quotient G) I Y) (hYX : Y ≠ X) : CompatibleCycle G I Y e x0 x1 :=
  (PCtx.of_canonical hV hE hℓ hC hY hYX).compatible_actual_cycle

/-- **Port selection under the standing hypotheses.** -/
theorem port_selection (hV : V(G).Finite) (hE : E(G).Finite)
    (hℓ : IsTemporallyConnected G ℓ) (hr : 4 ≤ V(quotient G).ncard)
    (hcard : E(quotient G).ncard = 2 * V(quotient G).ncard - 4) :
    ∃ (I : Set β) (X Y : Set (Set α)) (e : β) (x0 x1 : Set α),
      IsCanonical (quotient G) (causalQ G ℓ) I X e x0 x1 ∧ IsTreeComp (quotient G) I Y ∧
        Y ≠ X ∧ (∀ A, IsTreeComp (quotient G) I A → A = X ∨ A = Y) ∧
        CompatibleCycle G I Y e x0 x1 := by
  have hA := admissible hV hE (quotient_simple hV hE) hℓ
  obtain ⟨I, X, e, x0, x1, hC⟩ := hA.canonical_ideal hr hcard
  obtain ⟨Y, hY, hYX, hall, -⟩ := hA.early_components_of_canonical hr hcard hC
  exact ⟨I, X, Y, e, x0, x1, hC, hY, hYX, hall,
    compatible_actual_cycle_of_canonical hV hE hℓ hC hY hYX⟩

end Lax630294Proofs.Ports
