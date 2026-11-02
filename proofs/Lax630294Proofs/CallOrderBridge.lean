import Lax630294Proofs.CallOrderCanonical
import Lax630294.SpanningStructures

/-!
# Bridge: a rooted forest is a spanning forest with two components

`IsRootedForest H P F x0 x1 par pe` (item 4 of the canonical form) implies the frozen concept
`IsSpanningForest H F 2`.
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.SpanningStructures

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

lemma underlying_adj {F : Set β} {u v : V(H)} :
    (underlying H F).Adj u v ↔ u ≠ v ∧ ∃ e ∈ F, H.IsLink e u.1 v.1 := by
  simp only [underlying]
  constructor
  · rintro ⟨h, e, he, hl⟩
    exact ⟨h, e, he, hl⟩
  · rintro ⟨h, e, he, hl⟩
    exact ⟨h, e, he, hl⟩

section Bridge

variable {F : Set β} {x0 x1 : α} {par : α → α} {pe : α → β}

lemma IsRootedForest.adj_data (hfor : IsRootedForest H P F x0 x1 par pe) {u v : V(H)}
    (hadj : (underlying H F).Adj u v) :
    ∃ w, w ∈ V(H) ∧ w ≠ x0 ∧ w ≠ x1 ∧
      ((u.1 = w ∧ v.1 = par w) ∨ (u.1 = par w ∧ v.1 = w)) := by
  obtain ⟨-, e, he, hl⟩ := underlying_adj.1 hadj
  obtain ⟨w, hw, hwe⟩ := hfor.bij.surjOn he
  have hw0 : w ≠ x0 := fun h => hw.2 (Or.inl h)
  have hw1 : w ≠ x1 := fun h => hw.2 (Or.inr h)
  have hlw := (hfor.edge_mem w hw.1 hw0 hw1).2
  rw [hwe] at hlw
  refine ⟨w, hw.1, hw0, hw1, ?_⟩
  rcases hlw.eq_and_eq_or_eq_and_eq hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

lemma IsRootedForest.par_mem (hfor : IsRootedForest H P F x0 x1 par pe) {v : α} (hv : v ∈ V(H)) :
    par v ∈ V(H) := by
  by_cases h0 : v = x0
  · rw [h0, hfor.par_x0]; rw [h0] at hv; exact hv
  by_cases h1 : v = x1
  · rw [h1, hfor.par_x1]; rw [h1] at hv; exact hv
  exact (hfor.edge_mem v hv h0 h1).2.right_mem

lemma IsRootedForest.iterate_mem (hfor : IsRootedForest H P F x0 x1 par pe) {v : α}
    (hv : v ∈ V(H)) (n : ℕ) : par^[n] v ∈ V(H) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hfor.par_mem ih

/-- Following the parent pointers stays in one component. -/
lemma IsRootedForest.reachable_iterate [H.Loopless] (hfor : IsRootedForest H P F x0 x1 par pe) {v : α}
    (hv : v ∈ V(H)) (n : ℕ) :
    (underlying H F).Reachable ⟨v, hv⟩ ⟨par^[n] v, hfor.iterate_mem hv n⟩ := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    refine ih.trans ?_
    set u := par^[n] v with hu
    have huV : u ∈ V(H) := hfor.iterate_mem hv n
    have hsucc : par^[n + 1] v = par u := by
      rw [Function.iterate_succ_apply']
    have hmem : par^[n + 1] v ∈ V(H) := hfor.iterate_mem hv (n + 1)
    by_cases h0 : u = x0
    · have : par u = u := by rw [h0, hfor.par_x0]
      have heq : (⟨par^[n] v, huV⟩ : V(H)) = ⟨par^[n + 1] v, hmem⟩ := by
        apply Subtype.ext
        simp only
        rw [hsucc, this]
      rw [← heq]
    by_cases h1 : u = x1
    · have : par u = u := by rw [h1, hfor.par_x1]
      have heq : (⟨par^[n] v, huV⟩ : V(H)) = ⟨par^[n + 1] v, hmem⟩ := by
        apply Subtype.ext
        simp only
        rw [hsucc, this]
      rw [← heq]
    · refine SimpleGraph.Adj.reachable ?_
      have hl := (hfor.edge_mem u huV h0 h1).2
      refine underlying_adj.2 ⟨?_, pe u, (hfor.edge_mem u huV h0 h1).1, ?_⟩
      · intro h
        have := congrArg Subtype.val h
        simp only at this
        rw [hsucc] at this
        exact hl.ne this
      · simpa [hsucc] using hl

lemma iterate_step_iff {par : α → α} {v w : α} (hw : w ≠ v) :
    (∃ n, par^[n] w = v) ↔ ∃ n, par^[n] (par w) = v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact absurd hn hw
    | succ n =>
      rw [Function.iterate_succ_apply] at hn
      exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- A non-root is not an iterated parent of its own parent. -/
lemma IsRootedForest.not_cycle (hfor : IsRootedForest H P F x0 x1 par pe) {w : α}
    (hwV : w ∈ V(H)) (hw0 : w ≠ x0) (hw1 : w ≠ x1) : ¬ ∃ n, par^[n] (par w) = w := by
  rintro ⟨n, hn⟩
  have hper : par^[n + 1] w = w := by
    rw [Function.iterate_succ_apply]; exact hn
  obtain ⟨m, hm⟩ := hfor.reach w hwV
  have hfix : ∀ r, (r = x0 ∨ r = x1) → ∀ k, par^[k] r = r := by
    intro r hr k
    rcases hr with rfl | rfl
    · exact Function.iterate_fixed hfor.par_x0 k
    · exact Function.iterate_fixed hfor.par_x1 k
  have hmul : par^[(n + 1) * m] w = w := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hper m
  have hle : m ≤ (n + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos n)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, Function.iterate_add_apply] at hmul
  have hr : ∃ r, (r = x0 ∨ r = x1) ∧ par^[m] w = r := ⟨_, hm, rfl⟩
  obtain ⟨r, hr, hrm⟩ := hr
  rw [hrm, hfix r hr k] at hmul
  rcases hr with rfl | rfl
  · exact hw0 hmul.symm
  · exact hw1 hmul.symm

end Bridge

/-- **Item 4 as a frozen concept**: a rooted forest ordered outward is a spanning forest with
exactly two components. -/
theorem IsRootedForest.isSpanningForest [hH : H.Simple] {F : Set β} {x0 x1 : α}
    {par : α → α} {pe : α → β} (hF : F ⊆ E(H))
    (hfor : IsRootedForest H P F x0 x1 par pe) (hx0 : x0 ∈ V(H)) (hx1 : x1 ∈ V(H))
    (hne : x0 ≠ x1) : IsSpanningForest H F 2 := by
  refine ⟨hF, Graph.Simple.anti Graph.restrict_le, ?_, ?_⟩
  · -- acyclic
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro a b hab
    obtain ⟨w, hwV, hw0, hw1, hcase⟩ := hfor.adj_data hab
    have hpV : par w ∈ V(H) := hfor.par_mem hwV
    -- the bridge `w -- par w`
    have key : (underlying H F).IsBridge s((⟨w, hwV⟩ : V(H)), ⟨par w, hpV⟩) := by
      rw [SimpleGraph.isBridge_iff]
      intro hreach
      let T : V(H) → Prop := fun x => ∃ n, par^[n] x.1 = w
      have hinv : ∀ x y, ((underlying H F).deleteEdges {s((⟨w, hwV⟩ : V(H)), ⟨par w, hpV⟩)}).Adj x y →
          (T x ↔ T y) := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj] at hxy
        obtain ⟨hxy, hnot⟩ := hxy
        obtain ⟨w', hw'V, hw'0, hw'1, hc⟩ := hfor.adj_data hxy
        have hw'w : w' ≠ w := by
          intro h
          subst h
          apply hnot
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hx : x = ⟨w', hwV⟩ := Subtype.ext h1
            have hy : y = ⟨par w', hpV⟩ := Subtype.ext h2
            rw [hx, hy]; exact Set.mem_singleton _
          · have hx : x = ⟨par w', hpV⟩ := Subtype.ext h1
            have hy : y = ⟨w', hwV⟩ := Subtype.ext h2
            rw [hx, hy, Sym2.eq_swap]; exact Set.mem_singleton _
        have hstep := iterate_step_iff (par := par) hw'w
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · show (∃ n, par^[n] x.1 = w) ↔ ∃ n, par^[n] y.1 = w
          rw [h1, h2]; exact hstep
        · show (∃ n, par^[n] x.1 = w) ↔ ∃ n, par^[n] y.1 = w
          rw [h1, h2]; exact hstep.symm
      have hT : ∀ x y, ((underlying H F).deleteEdges
          {s((⟨w, hwV⟩ : V(H)), ⟨par w, hpV⟩)}).Reachable x y → (T x ↔ T y) := by
        intro x y hr
        rw [SimpleGraph.reachable_iff_reflTransGen] at hr
        induction hr with
        | refl => exact Iff.rfl
        | tail _ hbc ih => exact ih.trans (hinv _ _ hbc)
      have h1 := (hT _ _ hreach).1 ⟨0, rfl⟩
      exact hfor.not_cycle hwV hw0 hw1 h1
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : a = ⟨w, hwV⟩ := Subtype.ext h1
      have hy : b = ⟨par w, hpV⟩ := Subtype.ext h2
      rw [hx, hy]; exact key
    · have hx : a = ⟨par w, hpV⟩ := Subtype.ext h1
      have hy : b = ⟨w, hwV⟩ := Subtype.ext h2
      rw [hx, hy, Sym2.eq_swap]; exact key
  · -- exactly two components
    have hinv : ∀ x y : V(H), (underlying H F).Adj x y →
        ((∃ n, par^[n] x.1 = x0) ↔ ∃ n, par^[n] y.1 = x0) := by
      intro x y hxy
      obtain ⟨w', hw'V, hw'0, hw'1, hc⟩ := hfor.adj_data hxy
      have hstep := iterate_step_iff (par := par) (v := x0) hw'0
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hstep
      · rw [h1, h2]; exact hstep.symm
    have hwalk : ∀ {x y : V(H)} (p : (underlying H F).Walk x y),
        ((∃ n, par^[n] x.1 = x0) ↔ ∃ n, par^[n] y.1 = x0) := by
      intro x y p
      induction p with
      | nil => exact Iff.rfl
      | cons h _ ih => exact (hinv _ _ h).trans ih
    classical
    let f : (underlying H F).ConnectedComponent → Bool :=
      SimpleGraph.ConnectedComponent.lift (fun v => decide (∃ n, par^[n] v.1 = x0))
        (fun v w p _ => by
          have := hwalk p
          simp only [decide_eq_decide]
          exact this)
    have hfix : ∀ r, (r = x0 ∨ r = x1) → ∀ k, par^[k] r = r := by
      intro r hr k
      rcases hr with rfl | rfl
      · exact Function.iterate_fixed hfor.par_x0 k
      · exact Function.iterate_fixed hfor.par_x1 k
    have hf_mk : ∀ v : V(H), f ((underlying H F).connectedComponentMk v) =
        decide (∃ n, par^[n] v.1 = x0) := fun v => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro c d
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h v =>
        induction d using SimpleGraph.ConnectedComponent.ind with
        | h w =>
        rw [hf_mk, hf_mk]
        intro hvw
        rw [decide_eq_decide] at hvw
        apply SimpleGraph.ConnectedComponent.sound
        by_cases hv0 : ∃ n, par^[n] v.1 = x0
        · obtain ⟨n, hn⟩ := hv0
          obtain ⟨m, hm⟩ := hvw.1 ⟨n, hn⟩
          have r1 := hfor.reachable_iterate v.2 n
          have r2 := hfor.reachable_iterate w.2 m
          have e1 : (⟨par^[n] v.1, hfor.iterate_mem v.2 n⟩ : V(H)) = ⟨x0, hx0⟩ :=
            Subtype.ext hn
          have e2 : (⟨par^[m] w.1, hfor.iterate_mem w.2 m⟩ : V(H)) = ⟨x0, hx0⟩ :=
            Subtype.ext hm
          rw [e1] at r1
          rw [e2] at r2
          exact r1.trans r2.symm
        · have hw0 : ¬ ∃ n, par^[n] w.1 = x0 := fun h => hv0 (hvw.2 h)
          obtain ⟨n, hn⟩ := hfor.reach v.1 v.2
          obtain ⟨m, hm⟩ := hfor.reach w.1 w.2
          have hn' : par^[n] v.1 = x1 := hn.resolve_left (fun h => hv0 ⟨n, h⟩)
          have hm' : par^[m] w.1 = x1 := hm.resolve_left (fun h => hw0 ⟨m, h⟩)
          have r1 := hfor.reachable_iterate v.2 n
          have r2 := hfor.reachable_iterate w.2 m
          have e1 : (⟨par^[n] v.1, hfor.iterate_mem v.2 n⟩ : V(H)) = ⟨x1, hx1⟩ :=
            Subtype.ext hn'
          have e2 : (⟨par^[m] w.1, hfor.iterate_mem w.2 m⟩ : V(H)) = ⟨x1, hx1⟩ :=
            Subtype.ext hm'
          rw [e1] at r1
          rw [e2] at r2
          exact r1.trans r2.symm
      · intro b
        cases b
        · refine ⟨(underlying H F).connectedComponentMk ⟨x1, hx1⟩, ?_⟩
          rw [hf_mk]
          simp only [decide_eq_false_iff_not]
          rintro ⟨n, hn⟩
          rw [hfix x1 (Or.inr rfl)] at hn
          exact hne hn.symm
        · refine ⟨(underlying H F).connectedComponentMk ⟨x0, hx0⟩, ?_⟩
          rw [hf_mk]
          simp only [decide_eq_true_eq]
          exact ⟨0, rfl⟩
    have e := Equiv.ofBijective f hbij
    rw [ENat.card_congr e, ENat.card_eq_coe_fintype_card, Fintype.card_bool]

end Lax630294Proofs.CallOrder
