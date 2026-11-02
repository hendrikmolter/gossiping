import Lax630294Proofs.MSufficiencyCompletion
import Lax630294Proofs.MSufficiencyRank3
import Lax630294.TGraph

/-!
# Dichotomy for an `M`-witness (`lem:constructive-cross-bases`)

For an `M`-witness `(C, F₁, F₂)` of a graph that is not a `T`-graph there are four cycle edges
`W` such that all other cycle edges join vertices that are connected in `F₁` and in `F₂`.
-/

namespace Lax630294Proofs.MSufficiencyDichotomy

open Graph Lax630294.SpanningStructures Lax630294.MGraph Lax630294.TGraph
  Lax630294Proofs.MSufficiencyCyc Lax630294Proofs.MSufficiencyTree
  Lax630294Proofs.MSufficiencyCompletion

variable {α β : Type*} {G : Graph α β} {n : ℕ} [NeZero n] (c : Cyc G n)

/-- The "bases" of the `j`-th quotient: three-element sets of cycle indices completing `F` to a
spanning tree. -/
def Bases (F : Set β) : Set (Finset (ZMod n)) :=
  {S | S.card = 3 ∧ IsSpanningTree G (F ∪ c.e '' (S : Set (ZMod n)))}

include c in
/-- No coloops: for each cycle edge there is a completion avoiding it. -/
lemma bases_avoid (hV : V(G).Finite) {C F : Set β} (hC : Set.range c.e = C)
    (hF : IsFourComponentForestMeeting G C F) (i : ZMod n) : ∃ S ∈ Bases c F, i ∉ S := by
  obtain ⟨S, hSX, -, hcard, hT⟩ := tree_completion c hV hF.1
    (X := {k | k ≠ i}) (conn_of_avoid c hC hF.2 i (fun k hk => hk))
    (H0 := underlying G F) le_rfl (MSufficiencyCyc.underlying_mono Set.subset_union_left)
    hF.1.2.2.1 (J := ∅) (by simp) (by simp)
  exact ⟨S, ⟨hcard, hT⟩, fun h => hSX h rfl⟩

include c in
/-- A cycle edge joining two different components of `F` lies in some completion. -/
lemma bases_contain (hV : V(G).Finite) {C F : Set β} (hC : Set.range c.e = C)
    (hF : IsFourComponentForestMeeting G C F) (i : ZMod n)
    (hnr : ¬ (underlying G F).Reachable (c.vv i) (c.vv (i + 1))) : ∃ S ∈ Bases c F, i ∈ S := by
  have hle : SimpleGraph.edge (c.vv i) (c.vv (i + 1)) ≤
      underlying G (F ∪ c.e '' (Set.univ : Set (ZMod n))) := by
    intro x y hxy
    rw [SimpleGraph.edge_adj] at hxy
    obtain ⟨h | h, -⟩ := hxy
    · obtain ⟨rfl, rfl⟩ := h
      exact adj_of_isLink (T := F ∪ c.e '' Set.univ) (Or.inr ⟨i, Set.mem_univ _, rfl⟩) (c.link i)
        (c.v_succ_ne i).symm
    · obtain ⟨rfl, rfl⟩ := h
      exact (adj_of_isLink (T := F ∪ c.e '' Set.univ) (Or.inr ⟨i, Set.mem_univ _, rfl⟩) (c.link i)
        (c.v_succ_ne i).symm).symm
  obtain ⟨S, -, hJS, hcard, hT⟩ := tree_completion c hV hF.1
    (X := Set.univ) (conn_of_avoid c hC hF.2 i (fun k _ => Set.mem_univ k))
    (H0 := underlying G F ⊔ SimpleGraph.edge (c.vv i) (c.vv (i + 1))) le_sup_left
    (sup_le (MSufficiencyCyc.underlying_mono Set.subset_union_left) hle)
    (hF.1.2.2.1.sup_edge_of_not_reachable hnr) (J := {i}) (Set.subset_univ _)
    (by
      intro j hj
      rw [Set.mem_singleton_iff] at hj
      subst hj
      refine ⟨(SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ((SimpleGraph.edge_adj _ _ _ _).2
        ⟨Or.inl ⟨rfl, rfl⟩, c.vv_ne j⟩)), fun h => hnr h.reachable⟩)
  exact ⟨S, ⟨hcard, hT⟩, hJS rfl⟩

omit [NeZero n] in
include c in
/-- Two completions of `F₁`, `F₂` sharing at most one cycle edge give a `T`-witness. -/
lemma tWitness_of_bases {C F₁ F₂ : Set β} (hC : Set.range c.e = C)
    (h1C : Disjoint C F₁) (h2C : Disjoint C F₂) (h12 : Disjoint F₁ F₂)
    {S₁ S₂ : Finset (ZMod n)} (hS₁ : S₁ ∈ Bases c F₁) (hS₂ : S₂ ∈ Bases c F₂)
    (hcard : (S₁ ∩ S₂).card ≤ 1) :
    IsTGraph G := by
  refine ⟨F₁ ∪ c.e '' (S₁ : Set (ZMod n)), F₂ ∪ c.e '' (S₂ : Set (ZMod n)), hS₁.2, hS₂.2, ?_⟩
  have hsub : (F₁ ∪ c.e '' (S₁ : Set (ZMod n))) ∩ (F₂ ∪ c.e '' (S₂ : Set (ZMod n))) ⊆
      c.e '' ((S₁ ∩ S₂ : Finset (ZMod n)) : Set (ZMod n)) := by
    rintro z ⟨hz1, hz2⟩
    have hF1C : ∀ z ∈ F₁, z ∉ Set.range c.e := fun z hz hr =>
      Set.disjoint_left.1 h1C (hC ▸ hr) hz
    have hF2C : ∀ z ∈ F₂, z ∉ Set.range c.e := fun z hz hr =>
      Set.disjoint_left.1 h2C (hC ▸ hr) hz
    rcases hz1 with hz1 | ⟨i, hi, rfl⟩
    · rcases hz2 with hz2 | ⟨k, hk, rfl⟩
      · exact (Set.disjoint_left.1 h12 hz1 hz2).elim
      · exact (hF1C _ hz1 ⟨k, rfl⟩).elim
    · rcases hz2 with hz2 | ⟨k, hk, hk'⟩
      · exact (hF2C _ hz2 ⟨i, rfl⟩).elim
      · have : k = i := c.einj hk'
        subst this
        exact ⟨k, by simp_all, rfl⟩
  refine (Set.encard_le_encard hsub).trans ?_
  rw [c.einj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast hcard

/-- Build the cycle data from `IsCycle` and `4 ≤ C.encard`. -/
lemma exists_cyc {C : Set β} (hC : IsCycle G C) (h4 : 4 ≤ C.encard) :
    ∃ (n : ℕ) (_ : NeZero n) (c : Cyc G n), Set.range c.e = C := by
  obtain ⟨n, hn, v, e, vinj, einj, hlink, hrange⟩ := hC
  have : NeZero n := ⟨hn.ne'⟩
  have hn4 : 4 ≤ n := by
    have h1 : (Set.range e).encard = (Set.univ : Set (ZMod n)).encard := by
      rw [← Set.image_univ, einj.encard_image]
    rw [← hrange, h1, Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_zmod] at h4
    exact_mod_cast h4
  exact ⟨n, ⟨hn.ne'⟩, ⟨v, e, hn4, vinj, einj, hlink⟩, hrange⟩

-- DEVIATION: this is lem:constructive-cross-bases (non-constructive, no running time) in a
-- matroid-free form.  The paper forms the quotient graphs Q_j and their graphic matroids M_j and
-- applies lem:rank-three to matroids; here "bases" are 3-sets S of cycle indices with F_j + S a
-- spanning tree of G (MSufficiencyCompletion) and MSufficiencyRank3.rank_three is stated for
-- families of 3-sets.  The conclusion is the weak form: four cut edges W such that the ends of
-- every other cycle edge are connected in F_1 and in F_2.  The step "the four arcs lie in
-- distinct components, hence the intervals" and the matchings are in FourIntervals.four_intervals
-- (lem:four-intervals), derived from this theorem.
/-- **Dichotomy.** For an `M`-witness of a graph that is not a `T`-graph, there are four cycle
edges `W` such that all other cycle edges join vertices in the same component of `F₁` and of
`F₂`. -/
theorem dichotomy (hV : V(G).Finite) {C F₁ F₂ : Set β} (hW : IsMWitness G C F₁ F₂)
    (hnT : ¬ IsTGraph G) :
    ∃ (n : ℕ) (_ : NeZero n) (c : Cyc G n) (W : Finset (ZMod n)),
      Set.range c.e = C ∧ W.card = 4 ∧
      ∀ i, i ∉ W → (underlying G F₁).Reachable (c.vv i) (c.vv (i + 1)) ∧
        (underlying G F₂).Reachable (c.vv i) (c.vv (i + 1)) := by
  obtain ⟨hC, h4, hF1, hF2, hCF1, hCF2, hF12⟩ := hW
  obtain ⟨n, hn, c, hrange⟩ := exists_cyc hC h4
  have hP : ∀ A ∈ Bases c F₁, A.card = 3 := fun A hA => hA.1
  have hQ : ∀ B ∈ Bases c F₂, B.card = 3 := fun B hB => hB.1
  have hP' := bases_avoid c hV hrange hF1
  have hQ' := bases_avoid c hV hrange hF2
  rcases MSufficiencyRank3.rank_three (Bases c F₁) (Bases c F₂) hP hQ hP' hQ' with
    ⟨A, hA, B, hB, hAB⟩ | ⟨W, hWc, hWP, hWQ⟩
  · exact (hnT (tWitness_of_bases c hrange hCF1 hCF2 hF12 hA hB hAB)).elim
  · refine ⟨n, hn, c, W, hrange, hWc, fun i hi => ⟨?_, ?_⟩⟩
    · by_contra hnr
      obtain ⟨S, hS, hiS⟩ := bases_contain c hV hrange hF1 i hnr
      exact hi (hWP S hS hiS)
    · by_contra hnr
      obtain ⟨S, hS, hiS⟩ := bases_contain c hV hrange hF2 i hnr
      exact hi (hWQ S hS hiS)

end Lax630294Proofs.MSufficiencyDichotomy
