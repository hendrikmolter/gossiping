import Lax630294Proofs.QuotientExchange
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Maximal two-tree sets (blocks)

`lem:characterization-union` and `cor:characterization-partition`: the inclusion-maximal two-tree
sets partition `V(G)`.  The block of a vertex `x` is `blk G x`, the union of all two-tree sets
containing `x`; the blocks are exactly the maximal two-tree sets.
-/

namespace Lax630294Proofs.QuotientBlocks

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange

variable {α β : Type*} {G : Graph α β} {X Y : Set α} {x y z : α} {e : β}

lemma conn_union {P Q' Rm : Set β} {z : α} (hz : z ∈ X ∩ Y)
    (hRm : Rm ⊆ Ins G X) (hP : ∀ u ∈ X, ∀ v ∈ X, Reach G P u v)
    (hQ : ∀ u ∈ Y, ∀ v ∈ Y, Reach G Q' u v) :
    ∀ u ∈ X ∪ Y, Reach G (P ∪ (Q' \ Rm)) u z := by
  intro u hu
  rcases hu with hu | hu
  · exact reach_mono Set.subset_union_left (hP u hu z hz.1)
  · refine reach_of_forall_step (fun g hg s t hl => ?_) (hQ u hu z hz.2)
    by_cases hgR : g ∈ Rm
    · obtain ⟨hs, ht⟩ := ins_of_link (hRm hgR) hl
      exact reach_mono Set.subset_union_left (hP s hs t ht)
    · exact reach_of_isLink (Set.mem_union_right _ ⟨hg, hgR⟩) hl

/-- **Union lemma** (`lem:characterization-union`): two intersecting two-tree sets have a
two-tree union. -/
theorem isTwoTreeSet_union (hV : V(G).Finite) (hE : E(G).Finite) (hX : IsTwoTreeSet G X)
    (hY : IsTwoTreeSet G Y) (hXY : (X ∩ Y).Nonempty) : IsTwoTreeSet G (X ∪ Y) := by
  rw [isTwoTreeSet_iff hV hE] at hX hY ⊢
  obtain ⟨hXne, hXV, AX, BX, hAX, hBX, hABX, hcAX, hcBX⟩ := hX
  obtain ⟨hYne, hYV, AY, BY, hAY, hBY, hABY, hcAY, hcBY⟩ := hY
  obtain ⟨z, hzX, hzY⟩ := hXY
  have hz : z ∈ X ∩ Y := ⟨hzX, hzY⟩
  refine ⟨hXne.mono Set.subset_union_left, Set.union_subset hXV hYV, AX ∪ (AY \ BX),
    BX ∪ (BY \ AX), ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.union_subset (hAX.trans (ins_mono Set.subset_union_left))
      (Set.sdiff_subset.trans (hAY.trans (ins_mono Set.subset_union_right)))
  · exact Set.union_subset (hBX.trans (ins_mono Set.subset_union_left))
      (Set.sdiff_subset.trans (hBY.trans (ins_mono Set.subset_union_right)))
  · rw [Set.disjoint_left]
    intro g hg hg'
    rcases hg with hg | ⟨hg1, hg2⟩ <;> rcases hg' with hg' | ⟨hg1', hg2'⟩
    · exact Set.disjoint_left.1 hABX hg hg'
    · exact hg2' hg
    · exact hg2 hg'
    · exact Set.disjoint_left.1 hABY hg1 hg1'
  · have := conn_union hz hBX hcAX hcAY
    intro u hu v hv
    exact (this u hu).trans' (this v hv).symm'
  · have := conn_union hz hAX hcBX hcBY
    intro u hu v hv
    exact (this u hu).trans' (this v hv).symm'

lemma isTwoTreeSet_singleton (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) :
    IsTwoTreeSet G {x} := by
  rw [isTwoTreeSet_iff hV hE]
  refine ⟨⟨x, rfl⟩, Set.singleton_subset_iff.2 hx, ∅, ∅, Set.empty_subset _, Set.empty_subset _,
    Set.disjoint_empty _, ?_, ?_⟩ <;>
  · intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact reach_refl

/-- The *block* of `x`: the union of all two-tree sets containing `x`. -/
def blk (G : Graph α β) (x : α) : Set α := {y | ∃ X, IsTwoTreeSet G X ∧ x ∈ X ∧ y ∈ X}

lemma subset_blk (hX : IsTwoTreeSet G X) (hx : x ∈ X) : X ⊆ blk G x :=
  fun _ hy => ⟨X, hX, hx, hy⟩

/-- The block of a vertex is a two-tree set. -/
theorem isTwoTreeSet_blk (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) :
    IsTwoTreeSet G (blk G x) := by
  let 𝓕 : Set (Set α) := {X | IsTwoTreeSet G X ∧ x ∈ X}
  have hfin : 𝓕.Finite := hV.finite_subsets.subset (fun X hX => hX.1.2.1)
  have hne : 𝓕.Nonempty := ⟨{x}, isTwoTreeSet_singleton hV hE hx, rfl⟩
  obtain ⟨X0, hX0, hmax⟩ := Set.exists_max_image 𝓕 Set.ncard hfin hne
  have hsub : ∀ Y ∈ 𝓕, Y ⊆ X0 := by
    intro Y hY
    have hU : X0 ∪ Y ∈ 𝓕 :=
      ⟨isTwoTreeSet_union hV hE hX0.1 hY.1 ⟨x, hX0.2, hY.2⟩, Or.inl hX0.2⟩
    have hle := hmax _ hU
    have hfinU : (X0 ∪ Y).Finite := hV.subset (Set.union_subset hX0.1.2.1 hY.1.2.1)
    have heq := Set.eq_of_subset_of_ncard_le (Set.subset_union_left : X0 ⊆ X0 ∪ Y) hle hfinU
    exact heq ▸ Set.subset_union_right
  have hblk : blk G x = X0 := by
    ext y
    constructor
    · rintro ⟨X, hX, hxX, hyX⟩
      exact hsub X ⟨hX, hxX⟩ hyX
    · intro hy
      exact ⟨X0, hX0.1, hX0.2, hy⟩
  rw [hblk]
  exact hX0.1

lemma mem_blk_self (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) : x ∈ blk G x :=
  ⟨{x}, isTwoTreeSet_singleton hV hE hx, rfl, rfl⟩

lemma blk_subset (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) : blk G x ⊆ V(G) :=
  (isTwoTreeSet_blk hV hE hx).2.1

lemma blk_eq_of_mem (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) (hy : y ∈ blk G x) :
    blk G y = blk G x := by
  have hyV : y ∈ V(G) := blk_subset hV hE hx hy
  apply Set.Subset.antisymm
  · have hU := isTwoTreeSet_union hV hE (isTwoTreeSet_blk hV hE hyV) (isTwoTreeSet_blk hV hE hx)
      ⟨y, mem_blk_self hV hE hyV, hy⟩
    intro z hz
    exact subset_blk hU (Or.inr (mem_blk_self hV hE hx)) (Or.inl hz)
  · intro z hz
    exact subset_blk (isTwoTreeSet_blk hV hE hx) hy hz

lemma blk_eq_or_disjoint (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    blk G x = blk G y ∨ Disjoint (blk G x) (blk G y) := by
  by_cases h : (blk G x ∩ blk G y).Nonempty
  · obtain ⟨z, hzx, hzy⟩ := h
    left
    rw [← blk_eq_of_mem hV hE hx hzx, ← blk_eq_of_mem hV hE hy hzy]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2
      (Set.not_nonempty_iff_eq_empty.1 h)

/-- `X` is a maximal two-tree set. -/
def IsMaxTwoTree (G : Graph α β) (X : Set α) : Prop :=
  IsTwoTreeSet G X ∧ ∀ Y, IsTwoTreeSet G Y → X ⊆ Y → Y = X

lemma isMaxTwoTree_blk (hV : V(G).Finite) (hE : E(G).Finite) (hx : x ∈ V(G)) :
    IsMaxTwoTree G (blk G x) := by
  refine ⟨isTwoTreeSet_blk hV hE hx, fun Y hY hsub => ?_⟩
  apply Set.Subset.antisymm _ hsub
  have hxY : x ∈ Y := hsub (mem_blk_self hV hE hx)
  exact fun z hz => subset_blk hY hxY hz |> fun h => h

/-- The maximal two-tree sets are exactly the blocks `blk G x`. -/
lemma isMaxTwoTree_iff (hV : V(G).Finite) (hE : E(G).Finite) :
    IsMaxTwoTree G X ↔ ∃ x ∈ V(G), X = blk G x := by
  constructor
  · intro ⟨hX, hmax⟩
    obtain ⟨x, hx⟩ := hX.1
    refine ⟨x, hX.2.1 hx, ?_⟩
    symm
    exact hmax _ (isTwoTreeSet_blk hV hE (hX.2.1 hx)) (subset_blk hX hx) |> fun h => h ▸ rfl
  · rintro ⟨x, hx, rfl⟩
    exact isMaxTwoTree_blk hV hE hx

/-- **`cor:characterization-partition`.** The inclusion-maximal two-tree sets form a partition of
`V(G)`: every vertex lies in one, distinct ones are disjoint, and they consist of vertices of `G`. -/
theorem maxTwoTree_partition (hV : V(G).Finite) (hE : E(G).Finite) :
    (∀ x ∈ V(G), ∃ X, IsMaxTwoTree G X ∧ x ∈ X) ∧
    (∀ X Y, IsMaxTwoTree G X → IsMaxTwoTree G Y → X ≠ Y → Disjoint X Y) ∧
    (∀ X, IsMaxTwoTree G X → X ⊆ V(G)) := by
  refine ⟨fun x hx => ⟨blk G x, isMaxTwoTree_blk hV hE hx, mem_blk_self hV hE hx⟩, ?_,
    fun X hX => hX.1.2.1⟩
  intro X Y hX hY hne
  obtain ⟨x, hx, rfl⟩ := (isMaxTwoTree_iff hV hE).1 hX
  obtain ⟨y, hy, rfl⟩ := (isMaxTwoTree_iff hV hE).1 hY
  exact (blk_eq_or_disjoint hV hE hx hy).resolve_left hne


end Lax630294Proofs.QuotientBlocks
