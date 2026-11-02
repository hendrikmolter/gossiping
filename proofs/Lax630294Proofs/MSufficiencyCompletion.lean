import Lax630294Proofs.MSufficiencyTree

/-!
# Tree completion

Given a spanning forest `F` of `G` with four components and a cycle `c`, any acyclic simple graph
`H0` between the graph underlying `F` and the graph underlying `F ∪ c.e '' X` (with `F ∪ c.e '' X`
connected) can be completed to a spanning tree `F ∪ c.e '' S` with exactly three cycle edges.
-/

namespace Lax630294Proofs.MSufficiencyCompletion

open Graph Lax630294.SpanningStructures Lax630294.MGraph Lax630294Proofs.MSufficiencyCyc
  Lax630294Proofs.MSufficiencyTree

variable {α β : Type*} {G : Graph α β} {n : ℕ} [NeZero n] (c : Cyc G n)

-- DEVIATION: the paper (lem:constructive-cross-bases) forms the quotient multigraph Q_j by
-- identifying the vertices of C in the same component of F_j, takes its graphic matroid M_j
-- (rank three) and calls a basis of M_j a completion of F_j to a spanning tree.  We never form
-- Q_j: a "basis" is a set S of three cycle edges such that F_j ∪ S is a spanning tree of G
-- itself, and the needed facts about bases (no coloop; non-loop edges lie in a basis) are obtained
-- from this lemma: Mathlib's extension of an acyclic subgraph to a spanning tree of a connected
-- graph (Connected.exists_isTree_le_of_le_of_isAcyclic), applied to the simple graph underlying
-- F_j ∪ (cycle edges), plus a count of the extra edges via the forest edge count.
-- This also verifies that the result is a spanning tree in the sense of the concept
-- IsSpanningTree (simple, i.e. no loops/parallel edges, and the underlying simple graph is a tree).
include c in
theorem tree_completion (hV : V(G).Finite) {F : Set β} (hF : IsSpanningForest G F 4)
    {X : Set (ZMod n)} (hconn : (underlying G (F ∪ c.e '' X)).Connected)
    {H0 : SimpleGraph V(G)} (hA0 : underlying G F ≤ H0)
    (hH0X : H0 ≤ underlying G (F ∪ c.e '' X)) (hH0ac : H0.IsAcyclic)
    {J : Set (ZMod n)} (hJX : J ⊆ X)
    (hJ : ∀ i ∈ J, H0.Adj (c.vv i) (c.vv (i + 1)) ∧
      ¬ (underlying G F).Adj (c.vv i) (c.vv (i + 1))) :
    ∃ S : Finset (ZMod n), (↑S ⊆ X) ∧ J ⊆ ↑S ∧ S.card = 3 ∧
      IsSpanningTree G (F ∪ c.e '' (S : Set (ZMod n))) := by
  classical
  have : Finite V(G) := hV.to_subtype
  obtain ⟨H, hH0H, hHU, hHt⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic hH0X hH0ac
  have hAH : underlying G F ≤ H := hA0.trans hH0H
  -- the extra edges of `H`
  let E' : Set (Sym2 V(G)) := H.edgeSet \ (underlying G F).edgeSet
  let S' : Set (ZMod n) := {i | i ∈ X ∧ c.pair i ∈ E'}
  have hreal : ∀ ε ∈ E', ∃ i ∈ S', c.pair i = ε := by
    intro ε hε
    induction ε using Sym2.ind with | h a b =>
    have hHab : H.Adj a b := (SimpleGraph.mem_edgeSet _).1 hε.1
    have hnA : ¬ (underlying G F).Adj a b := fun h => hε.2 ((SimpleGraph.mem_edgeSet _).2 h)
    obtain ⟨hne, f, hf, hl⟩ := underlying_adj.1 (hHU hHab)
    rcases hf with hf | ⟨i, hiX, rfl⟩
    · exact absurd (underlying_adj.2 ⟨hne, f, hf, hl⟩) hnA
    · refine ⟨i, ⟨hiX, ?_⟩, (c.pair_of_link hl).symm⟩
      rw [← c.pair_of_link hl]; exact hε
  have himg : c.pair '' S' = E' := by
    ext ε
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi.2
    · intro hε
      obtain ⟨i, hi, h⟩ := hreal ε hε
      exact ⟨i, hi, h⟩
  have hS'card : S'.ncard = E'.ncard := by
    rw [← himg, Set.ncard_image_of_injective _ c.pair_inj]
  have hE'card : E'.ncard = 3 := by
    have hsub : (underlying G F).edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hAH
    have h1 : E'.ncard = H.edgeSet.ncard - (underlying G F).edgeSet.ncard :=
      Set.ncard_sdiff hsub (Set.toFinite _)
    have h2 : H.edgeSet.ncard + 1 = Nat.card V(G) := by
      have := (SimpleGraph.isTree_iff_connected_and_card.1 hHt).2
      rwa [Nat.card_coe_set_eq] at this
    have h3 := MSufficiencyForest.ncard_edgeSet_add_card_cc' (underlying G F) hF.2.2.1
    have h4 : Nat.card (underlying G F).ConnectedComponent = 4 := by
      have := hF.2.2.2
      rw [ENat.card_eq_coe_natCard] at this
      exact_mod_cast this
    omega
  have hS'fin : S'.Finite := Set.toFinite _
  have hcross : ∀ f ∈ F, ∀ i ∈ S', ∀ x y : α, G.IsLink f x y → G.IsLink (c.e i) x y → False := by
    intro f hf i hi x y hl1 hl2
    have hne : x ≠ y := by
      rintro rfl; exact c.not_loop i x hl2
    have hpair := c.pair_of_link (a := ⟨x, hl1.left_mem⟩) (b := ⟨y, hl1.right_mem⟩) hl2
    have hmem : s((⟨x, hl1.left_mem⟩ : V(G)), ⟨y, hl1.right_mem⟩) ∈ E' := by
      rw [hpair]; exact hi.2
    exact hmem.2 ((SimpleGraph.mem_edgeSet _).2 (adj_of_isLink hf hl1 hne))
  have hUT : underlying G (F ∪ c.e '' S') = H := by
    ext a b
    rw [underlying_adj]
    constructor
    · rintro ⟨hne, f, hf, hl⟩
      rcases hf with hf | ⟨i, hi, rfl⟩
      · exact hAH (underlying_adj.2 ⟨hne, f, hf, hl⟩)
      · have h1 := c.pair_of_link hl
        have hmem : c.pair i ∈ E' := hi.2
        rw [← h1] at hmem
        exact (SimpleGraph.mem_edgeSet _).1 hmem.1
    · intro hab
      by_cases hA : (underlying G F).Adj a b
      · obtain ⟨hne, f, hf, hl⟩ := underlying_adj.1 hA
        exact ⟨hne, f, Or.inl hf, hl⟩
      · have hε : s(a, b) ∈ E' := ⟨(SimpleGraph.mem_edgeSet _).2 hab,
          fun h => hA ((SimpleGraph.mem_edgeSet _).1 h)⟩
        obtain ⟨i, hi, hpi⟩ := hreal _ hε
        exact ⟨hab.ne, c.e i, Or.inr ⟨i, hi, rfl⟩, c.link_of_pair hpi.symm⟩
  have hSimple : (G.restrict (F ∪ c.e '' S')).Simple := by
    refine { not_isLoopAt := ?_, eq_of_isLink := ?_ }
    · intro f x hx
      obtain ⟨hf, hl⟩ := hx
      rcases hf with hf | ⟨i, hi, rfl⟩
      · exact hF.2.1.not_isLoopAt f x ⟨hf, hl⟩
      · exact c.not_loop i x hl
    · intro f g x y hf hg
      obtain ⟨hf1, hf2⟩ := hf
      obtain ⟨hg1, hg2⟩ := hg
      rcases hf1 with hf1 | ⟨i, hi, rfl⟩ <;> rcases hg1 with hg1 | ⟨k, hk, rfl⟩
      · exact hF.2.1.eq_of_isLink ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
      · exact (hcross f hf1 k hk x y hf2 hg2).elim
      · exact (hcross g hg1 i hi x y hg2 hf2).elim
      · rw [c.index_unique hf2 hg2]
  have hT : IsSpanningTree G (F ∪ c.e '' S') := by
    refine ⟨?_, hSimple, ?_⟩
    · rintro f (hf | ⟨i, -, rfl⟩)
      · exact hF.1 hf
      · exact c.edge_mem i
    · rw [hUT]; exact hHt
  refine ⟨hS'fin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Set.Finite.coe_toFinset] at hi
    exact hi.1
  · intro j hj
    rw [Set.Finite.coe_toFinset]
    refine ⟨hJX hj, ?_, ?_⟩
    · exact (SimpleGraph.mem_edgeSet _).2 (hH0H (hJ j hj).1)
    · intro h
      exact (hJ j hj).2 ((SimpleGraph.mem_edgeSet _).1 h)
  · rw [← Set.ncard_eq_toFinset_card S' hS'fin, hS'card, hE'card]
  · rw [Set.Finite.coe_toFinset]; exact hT

end Lax630294Proofs.MSufficiencyCompletion
