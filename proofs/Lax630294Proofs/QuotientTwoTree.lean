import Lax630294Proofs.QuotientCore

/-!
# Two-tree sets

A nonempty vertex set `X` is a *two-tree set* of `G` if `G[X]` has two edge-disjoint spanning
trees (paper, Section "Necessity: Two-Tree Blocks and Their Quotient").  This file contains the
definition, the reformulation by *connected* (instead of tree) edge sets, and the union lemma
`lem:characterization-union`.
-/

namespace Lax630294Proofs.QuotientTwoTree

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore

variable {α β : Type*} {G : Graph α β} {X Y : Set α} {A B : Set β} {e : β} {x y : α}

/-- The edges of `G` with both ends in `X` (the edge set of `G[X]`). -/
def Ins (G : Graph α β) (X : Set α) : Set β := {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X}

lemma mem_ins_of_link (hl : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : e ∈ Ins G X :=
  ⟨x, y, hl, hx, hy⟩

lemma ins_of_link (h : e ∈ Ins G X) (hl : G.IsLink e x y) : x ∈ X ∧ y ∈ X := by
  obtain ⟨x', y', hl', hx', hy'⟩ := h
  rcases hl'.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hx', hy'⟩
  · exact ⟨hy', hx'⟩

lemma ins_mono (h : X ⊆ Y) : Ins G X ⊆ Ins G Y := fun _ ⟨x, y, hl, hx, hy⟩ => ⟨x, y, hl, h hx, h hy⟩

lemma ins_subset_edgeSet : Ins G X ⊆ E(G) := fun _ ⟨_, _, hl, _, _⟩ => hl.edge_mem

lemma reach_induce_iff (h : A ⊆ Ins G X) : Reach (G.induce X) A x y ↔ Reach G A x y := by
  constructor
  · intro hr
    induction hr with
    | refl => exact reach_refl
    | tail _ hs ih =>
      obtain ⟨f, hf, hl⟩ := hs
      exact ih.trans' (reach_of_isLink hf hl.1)
  · intro hr
    induction hr with
    | refl => exact reach_refl
    | tail _ hs ih =>
      obtain ⟨f, hf, hl⟩ := hs
      obtain ⟨hx, hy⟩ := ins_of_link (h hf) hl
      exact ih.trans' (reach_of_isLink hf ⟨hl, hx, hy⟩)

lemma induce_induce (h : Y ⊆ X) : (G.induce X).induce Y = G.induce Y := by
  refine Graph.ext rfl (fun e x y => ?_)
  simp only [Graph.induce_isLink]
  constructor
  · rintro ⟨⟨hl, _, _⟩, hx, hy⟩; exact ⟨hl, hx, hy⟩
  · rintro ⟨hl, hx, hy⟩; exact ⟨⟨hl, h hx, h hy⟩, hx, hy⟩

/-- `X` is a *two-tree set* of `G`: `X` is a nonempty set of vertices and `G[X]` has two
edge-disjoint spanning trees.  Singletons are two-tree sets (with two empty trees). -/
def IsTwoTreeSet (G : Graph α β) (X : Set α) : Prop :=
  X.Nonempty ∧ X ⊆ V(G) ∧ ∃ A B : Set β,
    IsSpanningTree (G.induce X) A ∧ IsSpanningTree (G.induce X) B ∧ Disjoint A B

lemma finite_induce (hV : V(G).Finite) (hE : E(G).Finite) (hX : X ⊆ V(G)) :
    V(G.induce X).Finite ∧ E(G.induce X).Finite :=
  ⟨hV.subset hX, hE.subset ins_subset_edgeSet⟩

/-- Reformulation of two-tree sets: two edge-disjoint *connected* spanning edge sets of `G[X]`
(a connected spanning edge set contains a spanning tree). -/
theorem isTwoTreeSet_iff (hV : V(G).Finite) (hE : E(G).Finite) :
    IsTwoTreeSet G X ↔ X.Nonempty ∧ X ⊆ V(G) ∧ ∃ A B : Set β, A ⊆ Ins G X ∧ B ⊆ Ins G X ∧
      Disjoint A B ∧ (∀ x ∈ X, ∀ y ∈ X, Reach G A x y) ∧ (∀ x ∈ X, ∀ y ∈ X, Reach G B x y) := by
  constructor
  · rintro ⟨hne, hXV, A, B, hA, hB, hAB⟩
    obtain ⟨hVf, hEf⟩ := finite_induce hV hE hXV
    rw [isSpanningTree_iff hVf hEf] at hA hB
    refine ⟨hne, hXV, A, B, hA.1, hB.1, hAB, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
    · exact (reach_induce_iff hA.1).1 (hA.2.2.1 x hx y hy)
    · exact (reach_induce_iff hB.1).1 (hB.2.2.1 x hx y hy)
  · rintro ⟨hne, hXV, A, B, hA, hB, hAB, hcA, hcB⟩
    obtain ⟨hVf, hEf⟩ := finite_induce hV hE hXV
    obtain ⟨A', hA', hA't⟩ := exists_spanning_tree_subset hVf hEf _ A rfl hA hne
      (fun x hx y hy => (reach_induce_iff hA).2 (hcA x hx y hy))
    obtain ⟨B', hB', hB't⟩ := exists_spanning_tree_subset hVf hEf _ B rfl hB hne
      (fun x hx y hy => (reach_induce_iff hB).2 (hcB x hx y hy))
    exact ⟨hne, hXV, A', B', hA't, hB't, Set.disjoint_of_subset hA' hB' hAB⟩

end Lax630294Proofs.QuotientTwoTree
