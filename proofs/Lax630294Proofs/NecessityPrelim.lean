import Lax630294Proofs.QuotientCore
import Mathlib.Data.Fintype.EquivFin

namespace Lax630294Proofs.NecessityPrelim

open Graph Lax630294.Gossiping Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore

variable {α β : Type*} {G : Graph α β}

/-- Completeness gives connectivity: consecutive vertices of a temporal path are linked by edges. -/
theorem connected_of_complete {ℓ : β → ℕ} (h : IsTemporallyConnected G ℓ) :
    ∀ x ∈ V(G), ∀ y ∈ V(G), Reach G E(G) x y := by
  intro x hx y hy
  obtain ⟨k, p, e, h0, hk, -, hl, -⟩ := h x hx y hy
  have key : ∀ i : ℕ, (hi : i ≤ k) → Reach G E(G) x (p ⟨i, by omega⟩) := by
    intro i
    induction i with
    | zero => intro _; rw [← h0]; exact .refl
    | succ i ih =>
      intro hi
      exact (ih (by omega)).tail ⟨e ⟨i, by omega⟩, (hl ⟨i, by omega⟩).edge_mem, hl ⟨i, by omega⟩⟩
  rw [← hk]
  exact key k le_rfl

/-- A complete labeling can be replaced by one that is injective on the edges (ties are broken
by an arbitrary enumeration of the finitely many edges). -/
theorem tie_break (hE : E(G).Finite) {ℓ : β → ℕ} (h : IsTemporallyConnected G ℓ) :
    ∃ ℓ' : β → ℕ, Set.InjOn ℓ' E(G) ∧ IsTemporallyConnected G ℓ' := by
  classical
  have : Finite E(G) := hE
  let n := Nat.card E(G)
  let eq : E(G) ≃ Fin n := Finite.equivFin E(G)
  let ι : β → ℕ := fun e => if hh : e ∈ E(G) then (eq ⟨e, hh⟩).val else 0
  have hι : ∀ e, ι e < n + 1 := by
    intro e
    by_cases hh : e ∈ E(G)
    · simp only [ι, dif_pos hh]; have := (eq ⟨e, hh⟩).2; omega
    · simp [ι, dif_neg hh]
  have hιinj : Set.InjOn ι E(G) := by
    intro a ha b hb hab
    simp only [ι, dif_pos ha, dif_pos hb] at hab
    have := eq.injective (Fin.ext hab)
    simpa using congrArg Subtype.val this
  have hN : 0 < n + 1 := Nat.succ_pos n
  refine ⟨fun e => (n + 1) * ℓ e + ι e, ?_, ?_⟩
  · intro a ha b hb hab
    simp only at hab
    have h1 : ι a = ι b := by
      have h2 := congrArg (· % (n + 1)) hab
      simp only [Nat.mul_add_mod] at h2
      rwa [Nat.mod_eq_of_lt (hι a), Nat.mod_eq_of_lt (hι b)] at h2
    exact hιinj ha hb h1
  · intro u hu v hv
    obtain ⟨k, p, e, h0, hk, hinj, hl, hmono⟩ := h u hu v hv
    refine ⟨k, p, e, h0, hk, hinj, hl, fun i j hij => ?_⟩
    have hlt : ℓ (e i) < ℓ (e j) := hmono hij
    have h3 : (n + 1) * (ℓ (e i) + 1) ≤ (n + 1) * ℓ (e j) := Nat.mul_le_mul_left _ hlt
    rw [mul_add_one] at h3
    have := hι (e i)
    show (n + 1) * ℓ (e i) + ι (e i) < (n + 1) * ℓ (e j) + ι (e j)
    omega

end Lax630294Proofs.NecessityPrelim
