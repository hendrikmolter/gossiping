import Lax630294Proofs.FourIntervals
import Lax630294Proofs.MSufficiencyCutSchedule
import Mathlib.Data.Finset.Sort
import Lax630294Proofs.TSufficiency

/-!
# Sufficiency for `M`-graphs

`mGraph_sufficiency`: a finite `M`-graph is label-connected.

Proof: by `FourIntervals.four_intervals` (derived from `MSufficiencyDichotomy.dichotomy`) the cycle has four cut edges;
after rotating the cycle so that one cut edge is the last one and sorting the cuts, the schedule
of `MSufficiencyCutSchedule.schedule_from_cuts` applies.
-/

namespace Lax630294Proofs.MSufficiency

open Graph Lax630294.Gossiping Lax630294.SpanningStructures Lax630294.MGraph Lax630294.TGraph
  Lax630294Proofs.MSufficiencyCyc Lax630294Proofs.FourIntervals
  Lax630294Proofs.MSufficiencyCutSchedule Lax630294Proofs.ThreePhase

/-- Reachability in the simple graph underlying `F` gives a chain of `F`-edges. -/
lemma rtg_of_reachable {α β : Type*} {G : Graph α β} {F : Set β} {x y : V(G)}
    (h : (underlying G F).Reachable x y) :
    Relation.ReflTransGen (step G F) x.1 y.1 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine h.lift Subtype.val (fun a b hab => ?_)
  obtain ⟨-, e, he, hl⟩ := hab
  exact ⟨e, he, hl⟩

-- DEVIATION: the hypothesis hE : E(G).Finite is not needed (only V(G).Finite is used).
-- Proof chain: dichotomy -> FourIntervals.four_intervals (lem:four-intervals) -> the cut data
-- (`FourIntervals.reach_of_four_intervals`: only the "common intervals" part of the lemma is
-- consumed) -> schedule_from_cuts.
-- DEVIATION: the schedule (MSufficiencyCutSchedule) does not use the matchings B_1, B_2 nor the
-- roots p_i, q_i of the paper by name: its labels are explicit index functions on the cycle
-- rotated so that the last cut edge b_4 is the last edge; it needs only that consecutive
-- vertices of an interval are connected in both forests (which follows from the common
-- intervals) and that every vertex is connected to the cycle.  The rotation and the sorting of
-- the four cuts are done here, not in the paper.
/-- **Sufficiency for `M`-graphs.** A finite `M`-graph is label-connected. -/
theorem mGraph_sufficiency {α β : Type*} {G : Graph α β}
    (hV : V(G).Finite) (_hE : E(G).Finite) (h : Lax630294.MGraph.IsMGraph G) :
    Lax630294.Gossiping.IsLabelConnected G := by
  classical
  obtain ⟨⟨C, F1, F2, hW⟩, hnT⟩ := h
  obtain ⟨n, hn, c, k, hrange, hk, hk3, -, -, -, -, hcomp, -⟩ := four_intervals hV hW hnT
  obtain ⟨W, hWdef⟩ : ∃ W : Finset (ZMod n),
      W = Finset.univ.image (fun j : Fin 4 => ((k j : ℕ) : ZMod n)) := ⟨_, rfl⟩
  have hWc : W.card = 4 := hWdef ▸ cut_card k hk hk3
  have hreach : ∀ i, i ∉ W → (underlying G F1).Reachable (c.vv i) (c.vv (i + 1)) ∧
      (underlying G F2).Reachable (c.vv i) (c.vv (i + 1)) := fun i hi =>
    ⟨reach_of_four_intervals c k hk hk3 hrange (hcomp F1 (Or.inl rfl)).1 i (hWdef ▸ hi),
      reach_of_four_intervals c k hk hk3 hrange (hcomp F2 (Or.inr rfl)).1 i (hWdef ▸ hi)⟩
  obtain ⟨hCyc, h4, hF1, hF2, hCF1, hCF2, hF12⟩ := hW
  have hW0 : W.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w0, hw0⟩ := hW0
  set s : ZMod n := w0 + 1 with hs
  let u : ℕ → α := fun k => c.v ((k : ZMod n) + s)
  let f : ℕ → β := fun k => c.e ((k : ZMod n) + s)
  have hu_succ : ∀ k : ℕ, u (k + 1) = c.v ((k : ZMod n) + s + 1) := by
    intro k
    simp only [u]
    congr 1
    push_cast
    ring
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn.out
  have hwr : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hn_pos, ZMod.natCast_self]
  -- the cut set in rotated coordinates
  let Wn : Finset ℕ := W.image (fun w => (w - s).val)
  have hcardWn : Wn.card = 4 := by
    rw [Finset.card_image_of_injective _ (fun a b hab => sub_left_injective (ZMod.val_injective n hab))]
    exact hWc
  have hWn_lt : ∀ k ∈ Wn, k < n := by
    intro k hk
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hk
    exact ZMod.val_lt _
  have hmemWn : ∀ k, k < n → (k ∈ Wn ↔ ((k : ZMod n) + s) ∈ W) := by
    intro k hk
    constructor
    · intro hk'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk'
      rw [ZMod.natCast_zmod_val, sub_add_cancel]
      exact hw
    · intro hk'
      exact Finset.mem_image.2 ⟨_, hk', by rw [add_sub_cancel_right, ZMod.val_natCast_of_lt hk]⟩
  have hn1 : n - 1 ∈ Wn := by
    have h2 : ((n - 1 : ℕ) : ZMod n) = -1 := eq_neg_of_add_eq_zero_left hwr
    refine Finset.mem_image.2 ⟨w0, hw0, ?_⟩
    have h3 : w0 - s = ((n - 1 : ℕ) : ZMod n) := by rw [h2, hs]; ring
    rw [h3, ZMod.val_natCast_of_lt (by have := hn.out; omega)]
  let emb := Wn.orderEmbOfFin hcardWn
  have hembmem : ∀ i, emb i ∈ Wn := fun i => Finset.orderEmbOfFin_mem Wn hcardWn i
  have hembsurj : ∀ k ∈ Wn, ∃ i, emb i = k := by
    intro k hk
    have : k ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hk
    exact this
  have hlast : emb 3 = n - 1 := by
    obtain ⟨j, hj⟩ := hembsurj (n - 1) hn1
    have hj3 : j ≤ 3 := by fin_cases j <;> decide
    have h1 : emb j ≤ emb 3 := emb.monotone hj3
    have h2 : emb 3 < n := hWn_lt _ (hembmem 3)
    omega
  have h01 : emb 0 < emb 1 := emb.strictMono (by decide)
  have h12 : emb 1 < emb 2 := emb.strictMono (by decide)
  have h23 : emb 2 < emb 3 := emb.strictMono (by decide)
  have hcut : ∀ k : ℕ, k + 1 < n → k ≠ emb 0 → k ≠ emb 1 → k ≠ emb 2 →
      ((k : ZMod n) + s) ∉ W := by
    intro k hk h0 h1 h2 hW'
    obtain ⟨i, hi⟩ := hembsurj k ((hmemWn k (by omega)).2 hW')
    fin_cases i
    · exact h0 hi.symm
    · exact h1 hi.symm
    · exact h2 hi.symm
    · simp only [Fin.reduceFinMk] at hi
      omega
  -- vertices of the cycle
  have hcycv : ∀ c' : α, c' ∈ incidentVertices G C → ∃ i : ZMod n, c' = c.v i := by
    intro c' ⟨f', hfC, hinc⟩
    rw [← hrange] at hfC
    obtain ⟨m, rfl⟩ := hfC
    obtain ⟨y, hy⟩ := hinc
    rcases (c.link m).isLink_iff.1 hy with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ⟨m, h1.symm⟩
    · exact ⟨m + 1, h2.symm⟩
  have hu_of : ∀ i : ZMod n, ∃ m, m < n ∧ u m = c.v i := by
    intro i
    refine ⟨(i - s).val, ZMod.val_lt _, ?_⟩
    simp only [u]
    rw [ZMod.natCast_zmod_val, sub_add_cancel]
  have hmeet : ∀ F : Set β, (∀ x : V(G), ∃ c' : V(G), (c' : α) ∈ incidentVertices G C ∧
      (underlying G F).Reachable x c') →
      ∀ x ∈ V(G), ∃ m, m < n ∧ Relation.ReflTransGen (step G F) x (u m) := by
    intro F hF x hx
    obtain ⟨c', hc', hr⟩ := hF ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hcycv _ hc'
    obtain ⟨m, hm, hum⟩ := hu_of i
    refine ⟨m, hm, ?_⟩
    rw [hum, ← hi]
    exact rtg_of_reachable hr
  have hr : ∀ F : Set β, (∀ i : ZMod n, i ∉ W →
      (underlying G F).Reachable (c.vv i) (c.vv (i + 1))) →
      ∀ k : ℕ, k + 1 < n → k ≠ emb 0 → k ≠ emb 1 → k ≠ emb 2 →
        Relation.ReflTransGen (step G F) (u k) (u (k + 1)) := by
    intro F hF k hk h0 h1 h2
    have := rtg_of_reachable (hF _ (hcut k hk h0 h1 h2))
    rw [hu_succ]
    exact this
  refine schedule_from_cuts hV (F1 := F1) (F2 := F2) (n := n) (u := u) (f := f) ?_ ?_ ?_
    (c1 := emb 0) (c2 := emb 1) (c3 := emb 2) h01 h12 (by omega)
    (hr F1 (fun i hi => (hreach i hi).1)) (hr F2 (fun i hi => (hreach i hi).2))
    (hmeet F1 hF1.2) (hmeet F2 hF2.2) hF12 ?_ ?_
  · intro k _
    have := c.link ((k : ZMod n) + s)
    rw [hu_succ]
    exact this
  · have := c.link (((n - 1 : ℕ) : ZMod n) + s)
    have h2 : ((n - 1 : ℕ) : ZMod n) + s + 1 = ((0 : ℕ) : ZMod n) + s := by
      calc ((n - 1 : ℕ) : ZMod n) + s + 1 = (((n - 1 : ℕ) : ZMod n) + 1) + s := by ring
        _ = ((0 : ℕ) : ZMod n) + s := by rw [hwr]; simp
    rw [h2] at this
    exact this
  · intro k k' hk hk' hkk'
    have := c.einj hkk'
    have h3 : (k : ZMod n) = (k' : ZMod n) := add_right_cancel this
    rw [← ZMod.val_natCast_of_lt hk, ← ZMod.val_natCast_of_lt hk', h3]
  · intro k _ hk
    exact Set.disjoint_left.1 hCF1 (hrange ▸ (⟨_, rfl⟩ : f k ∈ Set.range c.e)) hk
  · intro k _ hk
    exact Set.disjoint_left.1 hCF2 (hrange ▸ (⟨_, rfl⟩ : f k ∈ Set.range c.e)) hk

end Lax630294Proofs.MSufficiency
