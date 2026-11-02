import Lax630294Proofs.PortsQ

/-!
# Shape of increasing trails in the quotient

Consequences of the last assertion of `lem:characterization-canonical-ideal` (a trail ending at a
root contains at most one call of `F ∪ {e}`, and only as its last call) for trails that start in
the second early tree `Y`, or run between the roots.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.SpanningStructures Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder

variable {γ β : Type*} {H : Graph γ β} {P : β → β → Prop} {I : Set β} {X Y : Set γ} {e : β}
  {x0 x1 : γ}

-- DEVIATION: the paper's "early prefix starting in `Y` cannot reach `X`" and "cannot use `e`" are
-- both consequences of component closure of `H[I]`; the last assertion of the canonical lemma is
-- only used through `QCtx.hC.trail`.
/-- Trails with edges in `I` starting in a component of `H[I]` stay in it. -/
lemma trail_in_comp {A : Set γ} (hAc : IsComp H I A) {u v : γ} {L : List β}
    (htr : IncTrail H P u v L) (hL : ∀ c ∈ L, c ∈ I) (hu : u ∈ A) :
    v ∈ A ∧ ∀ c ∈ L, c ∈ edgesIn H I A := by
  induction htr with
  | nil => exact ⟨hu, by simp⟩
  | @cons u w v f L hl h2 hp ih =>
    have hw : w ∈ A := hAc.link_mem (hL f (by simp)) hl hu
    obtain ⟨hv, hall⟩ := ih (fun c hc => hL c (by simp [hc])) hw
    refine ⟨hv, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨hL c (by simp), u, w, hl, hu, hw⟩
    · exact hall c hc

/-- The last edge of a nonempty trail. -/
lemma trail_last {u v : γ} {ts : List β} (htr : IncTrail H P u v ts) (hne : ts ≠ []) :
    ∃ L t m, ts = L ++ [t] ∧ IncTrail H P u m L ∧ H.IsLink t m v := by
  obtain ⟨L, t, rfl⟩ : ∃ L t, ts = L ++ [t] :=
    ⟨ts.dropLast, ts.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨m, h1, h2⟩ := htr.split
  obtain ⟨w, hl, h3, -⟩ := h2.mem_cons_inv
  cases h3
  exact ⟨L, t, m, rfl, h1, hl⟩

namespace QCtx

variable (c : QCtx H P I X Y e x0 x1)
include c

/-- A trail from `Y` to a root: an early path in `Y` followed by a single future call. -/
lemma trail_Y_root {u r : γ} {ts : List β} (hu : u ∈ Y) (hr : r = x0 ∨ r = x1)
    (htr : IncTrail H P u r ts) :
    ∃ L t V, ts = L ++ [t] ∧ (∀ g ∈ L, g ∈ edgesIn H I Y) ∧ t ∈ E(H) \ I ∧ H.IsLink t V r ∧
      V ∈ Y ∧ IncTrail H P u V L := by
  have hrX : r ∈ X := by rcases hr with rfl | rfl; exacts [c.x0_mem, c.x1_mem]
  have hne : ts ≠ [] := by
    rintro rfl
    cases htr
    exact c.mem_Y_not_X hu hrX
  obtain ⟨L, t, m, rfl, h1, hl⟩ := trail_last htr hne
  have h5 := c.hC.trail u r (L ++ [t]) hr htr
  simp only [List.dropLast_concat] at h5
  have hLI : ∀ g ∈ L, g ∈ I := by
    intro g hg
    by_contra hgI
    exact h5 g hg (Or.inl ⟨h1.edge_mem g hg, hgI⟩)
  obtain ⟨hmY, hLY⟩ := trail_in_comp c.hYc h1 hLI hu
  refine ⟨L, t, m, rfl, hLY, ⟨hl.edge_mem, fun htI => ?_⟩, hl, hmY, h1⟩
  exact c.mem_Y_not_X (c.hYc.link_mem htI hl hmY) hrX

/-- A trail from a vertex of `X` to a vertex of `Y` ends with a future call. -/
lemma trail_X_Y {u v : γ} {ts : List β} (hu : u ∈ X) (hv : v ∈ Y) (htr : IncTrail H P u v ts) :
    ∃ L t m, ts = L ++ [t] ∧ IncTrail H P u m L ∧ H.IsLink t m v ∧ t ∈ E(H) \ I := by
  have hne : ts ≠ [] := by
    rintro rfl
    cases htr
    exact c.mem_Y_not_X hv hu
  obtain ⟨L, t, m, rfl, h1, hl⟩ := trail_last htr hne
  refine ⟨L, t, m, rfl, h1, hl, hl.edge_mem, fun htI => ?_⟩
  have hpw := htr.pairwise c.trans
  have hall : ∀ g ∈ L ++ [t], g ∈ I := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact c.hI.2 g t ((List.pairwise_append.1 hpw).2.2 g hg t (by simp)) htI
    · rw [List.mem_singleton] at hg; exact hg ▸ htI
  obtain ⟨hvX, -⟩ := trail_in_comp c.hX htr hall hu
  exact c.mem_Y_not_X hv hvX

/-- A trail between the two roots starts with an early call. -/
lemma trail_roots_first {u v : γ} {ts : List β} (hu : u = x0 ∨ u = x1) (hv : v = x0 ∨ v = x1)
    (huv : u ≠ v) (htr : IncTrail H P u v ts) :
    ∃ a ts', ts = a :: ts' ∧ a ∈ edgesIn H I X := by
  have hne : ts ≠ [] := by
    rintro rfl
    cases htr
    exact huv rfl
  obtain ⟨a, ts', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨a, ts', rfl, ?_⟩
  obtain ⟨w, hl, h2, -⟩ := htr.mem_cons_inv
  have huX : u ∈ X := by rcases hu with rfl | rfl; exacts [c.x0_mem, c.x1_mem]
  have haI : a ∈ I := by
    by_contra haI
    have haF : a ∈ E(H) \ I := ⟨hl.edge_mem, haI⟩
    have hpw := htr.pairwise c.trans
    have hall : ∀ g ∈ a :: ts', g ∈ E(H) \ I := by
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact haF
      · exact c.mid_future haF g ((List.pairwise_cons.1 hpw).1 g hg)
    have hreach : Reach H (E(H) \ I) u v := htr.reach hall
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact huv rfl
    · exact c.not_reach_F hreach
    · exact c.not_reach_F hreach.symm'
    · exact huv rfl
  exact ⟨haI, u, w, hl, huX, c.hX.link_mem haI hl huX⟩

end QCtx

end Lax630294Proofs.Ports
