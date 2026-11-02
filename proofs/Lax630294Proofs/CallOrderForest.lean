import Lax630294Proofs.CallOrderBound

/-!
# Rooted forests ordered outward, increasing trails

The combinatorial shape of the future calls `F = E(H) \ I` in the canonical ideal
(`lem:characterization-canonical-ideal`, items 4 and 5).
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- A `P`-increasing trail from `u` to `v`, given by its list of edges: a walk
`u = v₀, e₁, v₁, …, e_k, v_k = v` (vertices may repeat) such that `P e_i e_{i+1}` for all `i`
(so the edges are pairwise distinct). -/
inductive IncTrail (H : Graph α β) (P : β → β → Prop) : α → α → List β → Prop
  | nil (u : α) : IncTrail H P u u []
  | cons {u w v : α} {e : β} {es : List β} : H.IsLink e u w → IncTrail H P w v es →
      (∀ f, es.head? = some f → P e f) → IncTrail H P u v (e :: es)

/-- `F` is a spanning forest with exactly two trees, rooted at `x0` and `x1` (distinct), whose
edges are ordered outward in `P`.  Encoded by parent data: every non-root `v` has a parent edge
`pe v ∈ F` linking `v` to its parent `par v`; `pe` is a bijection from the non-roots onto `F`;
every non-root reaches a root by iterating `par`; and if the parent of a non-root `v` is itself a
non-root then the parent edge of the parent precedes the parent edge of `v` in `P`. -/
structure IsRootedForest (H : Graph α β) (P : β → β → Prop) (F : Set β) (x0 x1 : α)
    (par : α → α) (pe : α → β) : Prop where
  edge_mem : ∀ v ∈ V(H), v ≠ x0 → v ≠ x1 → pe v ∈ F ∧ H.IsLink (pe v) v (par v)
  bij : Set.BijOn pe (V(H) \ {x0, x1}) F
  reach : ∀ v ∈ V(H), ∃ n : ℕ, par^[n] v = x0 ∨ par^[n] v = x1
  outward : ∀ v ∈ V(H), v ≠ x0 → v ≠ x1 → par v ≠ x0 → par v ≠ x1 → P (pe (par v)) (pe v)
  par_x0 : par x0 = x0
  par_x1 : par x1 = x1

/-- Last two edges of an increasing trail ending at a root: the second to last edge is neither
in `F` nor equal to `e`. -/
lemma Admissible.last_two (hA : Admissible H P) {I : Set β} {e : β} {x0 x1 : α}
    {par : α → α} {pe : α → β} (hI : IsIdeal H P I) (heI : e ∈ I)
    (hemax : ∀ c ∈ I, ¬ P e c) (hl : H.IsLink e x0 x1)
    (hfor : IsRootedForest H P (E(H) \ I) x0 x1 par pe) {g' g : β} {u w v : α}
    (h1 : H.IsLink g' u w) (h2 : H.IsLink g w v) (hv : v = x0 ∨ v = x1) (hP : P g' g) :
    g' ∉ (E(H) \ I) ∪ {e} := by
  intro hg'
  have hgF : g ∈ E(H) \ I := by
    refine ⟨hA.mem_right hP, fun hgI => ?_⟩
    rcases hg' with hg' | hg'
    · exact hg'.2 (hI.2 g' g hP hgI)
    · rw [Set.mem_singleton_iff] at hg'
      subst hg'
      exact hemax g hgI hP
  obtain ⟨c, hc, hcg⟩ := hfor.bij.surjOn hgF
  have hc0 : c ≠ x0 := fun h => hc.2 (Or.inl h)
  have hc1 : c ≠ x1 := fun h => hc.2 (Or.inr h)
  have hcl := (hfor.edge_mem c hc.1 hc0 hc1).2
  rw [hcg] at hcl
  -- g links c and par c, and also w and v
  have hwc : w = c := by
    rcases hcl.eq_and_eq_or_eq_and_eq h2 with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact h.symm
    · -- c = v, par c = w : but c is a non-root and v is a root
      exfalso
      rcases hv with rfl | rfl
      · exact hc0 h
      · exact hc1 h
  rcases hg' with hg' | hg'
  · -- g' ∈ F, so g' = pe c' for a non-root c'
    obtain ⟨c', hc', hc'g⟩ := hfor.bij.surjOn hg'
    have hc'0 : c' ≠ x0 := fun h => hc'.2 (Or.inl h)
    have hc'1 : c' ≠ x1 := fun h => hc'.2 (Or.inr h)
    have hc'l := (hfor.edge_mem c' hc'.1 hc'0 hc'1).2
    rw [hc'g] at hc'l
    -- g' links c' and par c', and also u and w = c
    rcases hc'l.eq_and_eq_or_eq_and_eq h1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · -- c' = u, par c' = w
      have hout := hfor.outward c' hc'.1 hc'0 hc'1 (by rw [h', hwc]; exact hc0)
        (by rw [h', hwc]; exact hc1)
      rw [h', hwc, hcg, hc'g] at hout
      exact hA.asymm hP hout
    · -- c' = w, so g' = pe w = g
      have : g' = g := by
        calc g' = pe c' := hc'g.symm
          _ = pe c := by rw [h, hwc]
          _ = g := hcg
      exact hA.irrefl g (this ▸ hP)
  · rw [Set.mem_singleton_iff] at hg'
    subst hg'
    -- e links x0 x1 and has the end w, a non-root
    rcases h1.right_eq_or_eq hl with h | h
    · exact hc0 (hwc.symm.trans h)
    · exact hc1 (hwc.symm.trans h)

/-- Item 5 of the canonical form: an increasing trail ending at a root contains no edge of
`F ∪ {e}` except possibly its last edge. -/
lemma Admissible.trail_dropLast (hA : Admissible H P) {I : Set β} {e : β} {x0 x1 : α}
    {par : α → α} {pe : α → β} (hI : IsIdeal H P I) (heI : e ∈ I)
    (hemax : ∀ c ∈ I, ¬ P e c) (hl : H.IsLink e x0 x1)
    (hfor : IsRootedForest H P (E(H) \ I) x0 x1 par pe) {u v : α} {es : List β}
    (ht : IncTrail H P u v es) :
    (v = x0 ∨ v = x1) → ∀ g ∈ es.dropLast, g ∉ (E(H) \ I) ∪ {e} := by
  induction ht with
  | nil u => intro _ g hg; simp at hg
  | @cons u w v' e0 es' hl1 ht hhead ih =>
    intro hv g hg
    cases es' with
    | nil => simp at hg
    | cons h es'' =>
      rw [List.dropLast_cons_of_ne_nil (by simp)] at hg
      rcases List.mem_cons.1 hg with rfl | hg
      · -- g is the first edge e0
        by_cases hes'' : es'' = []
        · subst hes''
          cases ht with
          | cons hl2 ht2 hhead2 =>
            cases ht2
            exact hA.last_two hI heI hemax hl hfor hl1 hl2 hv (hhead h rfl)
        · have hhmem : h ∈ (h :: es'').dropLast := by
            rw [List.dropLast_cons_of_ne_nil hes'']
            exact List.mem_cons_self
          have hh := ih hv h hhmem
          intro hg'
          apply hh
          have hPh := hhead h rfl
          left
          refine ⟨hA.mem_right hPh, fun hhI => ?_⟩
          rcases hg' with hg' | hg'
          · exact hg'.2 (hI.2 _ _ hPh hhI)
          · rw [Set.mem_singleton_iff] at hg'
            subst hg'
            exact hemax _ hhI hPh
      · exact ih hv g hg

end Lax630294Proofs.CallOrder
