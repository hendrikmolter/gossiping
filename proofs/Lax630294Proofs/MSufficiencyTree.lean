import Lax630294Proofs.MSufficiencyCyc
import Lax630294Proofs.MSufficiencyForest
import Lax630294.MGraph

/-!
# Completing a four-component forest to a spanning tree by cycle edges

Graph-level version of the "quotient multigraph `Q_j`" argument of `lem:constructive-cross-bases`:
instead of contracting the components of `F_j`, we work directly in `G` and extend the
acyclic simple graph underlying `F_j` to a spanning tree inside `F_j ∪ {cycle edges}`.
-/

namespace Lax630294Proofs.MSufficiencyTree

open Graph Lax630294.SpanningStructures Lax630294.MGraph Lax630294Proofs.MSufficiencyCyc

variable {α β : Type*} {G : Graph α β} {n : ℕ} [NeZero n] (c : Cyc G n)

-- DEVIATION: the paper shows that Q_j is connected and bridgeless via "every cut of a cycle is
-- even".  We only need: after deleting any single edge of the cycle the remaining cycle edges still
-- connect all cycle vertices (the rest of the cycle is a path), which gives connectivity of
-- F_j ∪ (C \ {e_i}) directly.
include c in
/-- Walking along the cycle (avoiding the single edge `i0`) connects all cycle vertices. -/
lemma cyc_reach {F : Set β} {X : Set (ZMod n)} (i0 : ZMod n) (hX : ∀ k, k ≠ i0 → k ∈ X)
    (m : ZMod n) :
    (underlying G (F ∪ c.e '' X)).Reachable (c.vv (i0 + 1)) (c.vv m) := by
  have key : ∀ t : ℕ, t < n →
      (underlying G (F ∪ c.e '' X)).Reachable (c.vv (i0 + 1)) (c.vv (i0 + 1 + (t : ZMod n))) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro hlt
      refine (ih (by omega)).trans ?_
      set k : ZMod n := i0 + 1 + (t : ZMod n) with hk
      have hki : k ≠ i0 := by
        intro h
        have h1 : ((t + 1 : ℕ) : ZMod n) = 0 := by
          push_cast
          rw [hk] at h
          have h2 : i0 + ((t : ZMod n) + 1) = i0 + 0 := by
            rw [add_zero]
            calc i0 + ((t : ZMod n) + 1) = i0 + 1 + (t : ZMod n) := by ring
              _ = i0 := h
          exact add_left_cancel h2
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd (by omega) h1
        omega
      have hadj := adj_of_isLink (T := F ∪ c.e '' X) (Or.inr ⟨k, hX k hki, rfl⟩) (c.link k)
        (c.v_succ_ne k).symm
      have hq : i0 + 1 + ((t + 1 : ℕ) : ZMod n) = k + 1 := by
        rw [hk]; push_cast; ring
      rw [hq]
      exact hadj.reachable
  have hm : m = i0 + 1 + (((m - (i0 + 1)).val : ℕ) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]; ring
  rw [hm]
  exact key _ (ZMod.val_lt _)

include c in
/-- The simple graph underlying `F ∪ {cycle edges ≠ i0}` is connected, when every vertex is
joined by `F` to a cycle vertex. -/
lemma conn_of_avoid {C F : Set β} (hC : Set.range c.e = C)
    (hF : ∀ x : V(G), ∃ c' : V(G), (c' : α) ∈ incidentVertices G C ∧
      (underlying G F).Reachable x c')
    {X : Set (ZMod n)} (i0 : ZMod n) (hX : ∀ k, k ≠ i0 → k ∈ X) :
    (underlying G (F ∪ c.e '' X)).Connected := by
  have key : ∀ x : V(G), (underlying G (F ∪ c.e '' X)).Reachable x (c.vv (i0 + 1)) := by
    intro x
    obtain ⟨c', hc', hr⟩ := hF x
    obtain ⟨f, hfC, hinc⟩ := hc'
    rw [← hC] at hfC
    obtain ⟨m, rfl⟩ := hfC
    obtain ⟨y, hy⟩ := hinc
    have hc'm : c' = c.vv m ∨ c' = c.vv (m + 1) := by
      rcases (c.link m).isLink_iff.1 hy with ⟨h1, -⟩ | ⟨-, h2⟩
      · left; exact Subtype.ext h1.symm
      · right; exact Subtype.ext h2.symm
    have hrA : (underlying G (F ∪ c.e '' X)).Reachable x c' :=
      hr.mono (underlying_mono Set.subset_union_left)
    have hc'r : (underlying G (F ∪ c.e '' X)).Reachable c' (c.vv (i0 + 1)) := by
      rcases hc'm with rfl | rfl
      · exact (cyc_reach c i0 hX m).symm
      · exact (cyc_reach c i0 hX (m + 1)).symm
    exact hrA.trans hc'r
  exact { preconnected := fun x y => (key x).trans (key y).symm
          nonempty := ⟨c.vv (i0 + 1)⟩ }

end Lax630294Proofs.MSufficiencyTree
