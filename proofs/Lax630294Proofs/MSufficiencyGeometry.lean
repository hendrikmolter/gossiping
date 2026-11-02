import Lax630294Proofs.MSufficiencySchedule
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The cycle schedule of an `M`-witness (index form)

The cycle is given as a linear sequence of vertices `u 0, …, u (n-1)` and edges `f 0, …, f (n-1)`
with `f k` joining `u k` and `u (k+1)` for `k+1 < n` and `f (n-1)` joining `u (n-1)` and `u 0`.
The four cut edges are `f c1, f c2, f c3, f (n-1)` (`c1 < c2 < c3 < n - 1`).  The four intervals
are `[0,c1]`, `[c1+1,c2]`, `[c2+1,c3]`, `[c3+1,n-1]`; the essential edges are
`b₁ = f c1`, `b₂ = f c2`, `b₃ = f c3`, `b₄ = f (n-1)`.  The roots for the gathering forest are
the endpoints of `b₁, b₃` (`p`), the roots for the distributing forest the endpoints of `b₂, b₄`
(`q`).
-/

namespace Lax630294Proofs.MSufficiencyGeometry

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal Lax630294Proofs.ThreePhase
  Lax630294Proofs.MSufficiencySchedule

variable {α β : Type*} {G : Graph α β}

section walks

variable {n : ℕ} {u : ℕ → α} {f : ℕ → β} {L : ℕ → ℕ} {lm : β → ℕ}

lemma walk_fwd (hlink : ∀ k, k + 1 < n → G.IsLink (f k) (u k) (u (k + 1)))
    (hlm : ∀ k, k < n → lm (f k) = L k) :
    ∀ d s, s + d < n → (∀ k k', s ≤ k → k < k' → k' < s + d → L k < L k') →
      ∃ vs es, TW G lm (u s) (u (s + d)) vs es ∧
        ∀ g ∈ es, ∃ k, s ≤ k ∧ k < s + d ∧ g = f k := by
  intro d
  induction d with
  | zero => intro s _ _; exact ⟨[], [], .nil _, by simp⟩
  | succ d ih =>
    intro s hs hmono
    obtain ⟨vs, es, hw, hg⟩ := ih (s + 1) (by omega)
      (fun k k' hk hkk' hk' => hmono k k' (by omega) hkk' (by omega))
    have e : s + (d + 1) = s + 1 + d := by omega
    rw [e]
    refine ⟨u s :: vs, f s :: es, .cons (hlink s (by omega)) hw ?_, ?_⟩
    · intro g hgm
      obtain ⟨k, hk1, hk2, rfl⟩ := hg g hgm
      rw [hlm s (by omega), hlm k (by omega)]
      exact hmono s k le_rfl (by omega) (by omega)
    · intro g hgm
      rcases List.mem_cons.1 hgm with rfl | hgm
      · exact ⟨s, le_rfl, by omega, rfl⟩
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hgm
        exact ⟨k, by omega, by omega, rfl⟩

lemma walk_bwd (hlink : ∀ k, k + 1 < n → G.IsLink (f k) (u k) (u (k + 1)))
    (hlm : ∀ k, k < n → lm (f k) = L k) :
    ∀ d s, s + d < n → (∀ k k', s ≤ k → k < k' → k' < s + d → L k' < L k) →
      ∃ vs es, TW G lm (u (s + d)) (u s) vs es ∧
        ∀ g ∈ es, ∃ k, s ≤ k ∧ k < s + d ∧ g = f k := by
  intro d
  induction d with
  | zero => intro s _ _; exact ⟨[], [], .nil _, by simp⟩
  | succ d ih =>
    intro s hs hmono
    obtain ⟨vs, es, hw, hg⟩ := ih s (by omega)
      (fun k k' hk hkk' hk' => hmono k k' hk hkk' (by omega))
    have e : s + (d + 1) = s + d + 1 := rfl
    rw [e]
    refine ⟨u (s + d + 1) :: vs, f (s + d) :: es, .cons (hlink (s + d) (by omega)).symm hw ?_, ?_⟩
    · intro g hgm
      obtain ⟨k, hk1, hk2, rfl⟩ := hg g hgm
      rw [hlm (s + d) (by omega), hlm k (by omega)]
      exact hmono k (s + d) hk1 hk2 (by omega)
    · intro g hgm
      rcases List.mem_cons.1 hgm with rfl | hgm
      · exact ⟨s + d, by omega, by omega, rfl⟩
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hgm
        exact ⟨k, by omega, by omega, rfl⟩

end walks

lemma rtg_chain {R : α → α → Prop} (u : ℕ → α) (a : ℕ) :
    ∀ d, (∀ k, a ≤ k → k < a + d → Relation.ReflTransGen R (u k) (u (k + 1))) →
      Relation.ReflTransGen R (u a) (u (a + d)) := by
  intro d
  induction d with
  | zero => intro _; exact .refl
  | succ d ih =>
    intro h
    exact (ih (fun k hk hk' => h k hk (by omega))).trans (h (a + d) (by omega) (by omega))

lemma rtg_between {R : α → α → Prop} (u : ℕ → α) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → Relation.ReflTransGen R (u k) (u (k + 1))) :
    Relation.ReflTransGen R (u a) (u b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact rtg_chain u a d h

end Lax630294Proofs.MSufficiencyGeometry
