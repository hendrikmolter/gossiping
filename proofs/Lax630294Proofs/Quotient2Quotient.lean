import Lax630294Proofs.Quotient2Family
import Lax630294.MGraph

/-!
# The quotient by blocks: `lem:characterization-quotient`, `lem:characterization-t-lift`,
`cor:characterization-t-case` (for `G`)

All statements are for a graph `G` with `V(G)` and `E(G)` finite.

DEVIATION: looplessness of `G` is not needed anywhere (loops of `G` are internal to a block and are
deleted in the quotient; spanning trees never contain loops).
-/

namespace Lax630294Proofs.Quotient2Quotient

open Graph Lax630294.SpanningStructures Lax630294.TGraph Lax630294Proofs.ThreePhase
  Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange
  Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef Lax630294Proofs.Quotient2Contract
  Lax630294Proofs.Quotient2Family

variable {α β : Type*} {G : Graph α β} {x y z : α} {e : β}

lemma quotient_finite (hV : V(G).Finite) (hE : E(G).Finite) :
    V(quotient G).Finite ∧ E(quotient G).Finite := contract_finite hV hE

lemma quotient_edgeSet_subset : E(quotient G) ⊆ E(G) := contract_edgeSet_subset

lemma mem_edgeSet_quotient :
    e ∈ E(quotient G) ↔ ∃ x y, G.IsLink e x y ∧ blk G x ≠ blk G y := mem_edgeSet_contract

lemma quotient_loopless (e : β) (x : Set α) : ¬ (quotient G).IsLink e x x := by
  intro h
  obtain ⟨_, _, _, _, _, hne⟩ := quotient_isLink.1 h
  exact hne rfl

/-- **`lem:characterization-quotient`** (vertices): the vertices of the quotient are exactly the
maximal two-tree sets, i.e. the blocks of `cor:characterization-partition`. -/
theorem quotient_vertexSet_eq (hV : V(G).Finite) (hE : E(G).Finite) :
    V(quotient G) = {X | QuotientBlocks.IsMaxTwoTree G X} := by
  ext X
  change X ∈ blk G '' V(G) ↔ QuotientBlocks.IsMaxTwoTree G X
  rw [QuotientBlocks.isMaxTwoTree_iff hV hE]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- The set of vertices of `G` lying in the blocks of `Y`. -/
def liftSet (G : Graph α β) (Y : Set (Set α)) : Set α := {x | x ∈ V(G) ∧ blk G x ∈ Y}

lemma lift_closed (_hV : V(G).Finite) (_hE : E(G).Finite) {Y : Set (Set α)} {A' I : Set β}
    (hA' : A' ⊆ Ins (quotient G) Y) (hI : Fib G (blk G) I) :
    Closed G (A' ∪ I) (liftSet G Y) := by
  rintro g (hg | hg) a b hl ⟨haV, haY⟩
  · have hne : blk G a ≠ blk G b :=
      contract_ext (f := blk G) (ins_subset_edgeSet (hA' hg)) hl
    have hl' : (quotient G).IsLink g (blk G a) (blk G b) := quotient_isLink.2 ⟨a, b, hl, rfl, rfl, hne⟩
    exact ⟨hl.right_mem, (ins_of_link (hA' hg) hl').2⟩
  · have := hI.internal g hg a b hl
    exact ⟨hl.right_mem, this ▸ haY⟩

lemma lift_conn (hV : V(G).Finite) (hE : E(G).Finite) {Y : Set (Set α)} {A' I : Set β}
    (hA' : A' ⊆ Ins (quotient G) Y) (hI : Fib G (blk G) I)
    (hc : ∀ U ∈ Y, ∀ U' ∈ Y, Reach (quotient G) A' U U') :
    ∀ x ∈ liftSet G Y, ∀ y ∈ liftSet G Y, Reach G ((A' ∪ I) ∩ Ins G (liftSet G Y)) x y := by
  rintro x ⟨hxV, hxY⟩ y ⟨hyV, hyY⟩
  have h1 : Reach (contract G (blk G)) A' (blk G x) (blk G y) := hc _ hxY _ hyY
  have h2 := (reach_contract_iff hI (fun e he => ins_subset_edgeSet (hA' he)) hxV hyV).1 h1
  exact (reach_closed (lift_closed hV hE hA' hI) ⟨hxV, hxY⟩ h2).2

/-- `lem:characterization-quotient` (second part): the quotient has no two-tree set of size at
least two. -/
theorem quotient_no_twoTree (hV : V(G).Finite) (hE : E(G).Finite) {Y : Set (Set α)}
    (hYV : Y ⊆ V(quotient G)) (hY2 : 2 ≤ Y.ncard) : ¬ IsTwoTreeSet (quotient G) Y := by
  intro hY
  obtain ⟨hVQ, hEQ⟩ := quotient_finite hV hE
  rw [isTwoTreeSet_iff hVQ hEQ] at hY
  obtain ⟨hYne, _, A', B', hA', hB', hAB', hcA, hcB⟩ := hY
  obtain ⟨A, B, hA, hB, hABd⟩ := exists_AB hV hE
  have hW : IsTwoTreeSet G (liftSet G Y) := by
    rw [isTwoTreeSet_iff hV hE]
    obtain ⟨U, hU⟩ := hYne
    obtain ⟨x, hx, rfl⟩ := hYV hU
    refine ⟨⟨x, hx, hU⟩, fun x hx => hx.1, (A' ∪ A) ∩ Ins G (liftSet G Y),
      (B' ∪ B) ∩ Ins G (liftSet G Y), Set.inter_subset_right, Set.inter_subset_right, ?_,
      lift_conn hV hE hA' hA hcA, lift_conn hV hE hB' hB hcB⟩
    refine Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left ?_
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    refine ⟨⟨hAB', ?_⟩, ?_, hABd⟩
    · exact (hB.disjoint_ext.symm).mono_left (fun e he => ins_subset_edgeSet (hA' he))
    · exact (hA.disjoint_ext.symm).mono_left (fun e he => ins_subset_edgeSet (hB' he)) |>.symm
  have hfin : Y.Finite := hVQ.subset hYV
  obtain ⟨U1, U2, hU1, hU2, hne⟩ := (Set.one_lt_ncard_iff hfin).1 (by omega)
  obtain ⟨x1, hx1, rfl⟩ := hYV hU1
  obtain ⟨x2, hx2, rfl⟩ := hYV hU2
  have hsub : blk G x1 ⊆ liftSet G Y := by
    intro y hy
    refine ⟨blk_subset hV hE hx1 hy, ?_⟩
    rw [blk_eq_of_mem hV hE hx1 hy]
    exact hU1
  have hmax := (isMaxTwoTree_blk hV hE hx1).2 _ hW hsub
  have hx2W : x2 ∈ liftSet G Y := ⟨hx2, hU2⟩
  rw [hmax] at hx2W
  exact hne (blk_eq_of_mem hV hE hx1 hx2W).symm

/-- `lem:characterization-quotient` (third part): the quotient is simple. -/
theorem quotient_simple (hV : V(G).Finite) (hE : E(G).Finite) : (quotient G).Simple := by
  obtain ⟨hVQ, hEQ⟩ := quotient_finite hV hE
  refine { not_isLoopAt := fun e x h => quotient_loopless e x h, eq_of_isLink := ?_ }
  intro e f U W he hf
  by_contra hef
  have hUW : U ≠ W := by
    rintro rfl; exact quotient_loopless e U he
  have hYV : ({U, W} : Set (Set α)) ⊆ V(quotient G) := by
    rintro Z (rfl | rfl)
    · exact he.left_mem
    · exact he.right_mem
  refine quotient_no_twoTree hV hE hYV (by rw [Set.ncard_pair hUW]) ?_
  rw [isTwoTreeSet_iff hVQ hEQ]
  refine ⟨⟨U, Or.inl rfl⟩, hYV, {e}, {f}, ?_, ?_, Set.disjoint_singleton.2 hef, ?_, ?_⟩
  · intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact mem_ins_of_link he (Or.inl rfl) (Or.inr rfl)
  · intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact mem_ins_of_link hf (Or.inl rfl) (Or.inr rfl)
  · rintro u (rfl | rfl) v (rfl | rfl)
    · exact reach_refl
    · exact reach_of_isLink (Set.mem_singleton e) he
    · exact (reach_of_isLink (Set.mem_singleton e) he).symm'
    · exact reach_refl
  · rintro u (rfl | rfl) v (rfl | rfl)
    · exact reach_refl
    · exact reach_of_isLink (Set.mem_singleton f) hf
    · exact (reach_of_isLink (Set.mem_singleton f) hf).symm'
    · exact reach_refl

/-- `lem:characterization-quotient` (fourth part): connectivity passes to the quotient. -/
theorem quotient_connected (hconn : ∀ x ∈ V(G), ∀ y ∈ V(G), Reach G E(G) x y) :
    ∀ U ∈ V(quotient G), ∀ W ∈ V(quotient G), Reach (quotient G) E(quotient G) U W := by
  have key : ∀ {x y : α}, Reach G E(G) x y → Reach (quotient G) E(quotient G) (blk G x) (blk G y) := by
    intro x y h
    induction h with
    | refl => exact reach_refl
    | @tail w z _ hs ih =>
      obtain ⟨g, _, hl⟩ := hs
      by_cases hwz : blk G w = blk G z
      · rw [← hwz]; exact ih
      · exact ih.trans' (reach_of_isLink (mem_edgeSet_quotient.2 ⟨w, z, hl, hwz⟩)
          (quotient_isLink.2 ⟨w, z, hl, rfl, rfl, hwz⟩))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact key (hconn x hx y hy)

/-- `lem:characterization-t-lift`, first part. -/
theorem tLift (hV : V(G).Finite) (hE : E(G).Finite) {T₁ T₂ : Set β}
    (h : IsTWitness (quotient G) T₁ T₂) : IsTGraph G := by
  obtain ⟨A, B, hA, hB, hABd⟩ := exists_AB hV hE
  obtain ⟨h1, h2, h12⟩ := h
  have hT1 : T₁ ⊆ E(quotient G) := h1.1
  have hT2 : T₂ ⊆ E(quotient G) := h2.1
  refine ⟨T₁ ∪ A, T₂ ∪ B, (lift_spanningTree hV hE hA hT1).1 h1,
    (lift_spanningTree hV hE hB hT2).1 h2, ?_⟩
  refine (Set.encard_le_encard ?_).trans h12
  rintro e ⟨he1, he2⟩
  rcases he1 with he1 | he1 <;> rcases he2 with he2 | he2
  · exact ⟨he1, he2⟩
  · exact absurd (hT1 he1) (Set.disjoint_left.1 hB.disjoint_ext he2)
  · exact absurd (hT2 he2) (Set.disjoint_left.1 hA.disjoint_ext he1)
  · exact absurd he2 (Set.disjoint_left.1 hABd he1)

/-- `lem:characterization-t-lift`, second part: a one-vertex quotient means `G` is itself a block,
so it has two edge-disjoint spanning trees. -/
theorem one_vertex (hV : V(G).Finite) (hE : E(G).Finite) (h : V(quotient G).ncard = 1) :
    ∃ T₁ T₂ : Set β, IsSpanningTree G T₁ ∧ IsSpanningTree G T₂ ∧ Disjoint T₁ T₂ := by
  obtain ⟨U, hU⟩ := Set.ncard_eq_one.1 h
  have hUm : U ∈ V(quotient G) := by rw [hU]; exact rfl
  obtain ⟨x, hx, rfl⟩ := hUm
  have hblk : blk G x = V(G) := by
    apply Set.Subset.antisymm (blk_subset hV hE hx)
    intro y hy
    have : blk G y ∈ V(quotient G) := ⟨y, hy, rfl⟩
    rw [hU, Set.mem_singleton_iff] at this
    rw [← this]
    exact mem_blk_self hV hE hy
  obtain ⟨_, _, A, B, hA, hB, hAB⟩ := isTwoTreeSet_blk hV hE hx
  rw [hblk, Graph.induce_vertexSet] at hA hB
  exact ⟨A, B, hA, hB, hAB⟩

/-- `cor:characterization-t-case` for `G`. -/
theorem tCase (hV : V(G).Finite) (hE : E(G).Finite)
    (hconn : ∀ x ∈ V(G), ∀ y ∈ V(G), Reach G E(G) x y)
    (hr : 2 ≤ V(quotient G).ncard)
    (hcard : E(quotient G).ncard + 3 = 2 * V(quotient G).ncard) : IsTGraph G := by
  obtain ⟨hVQ, hEQ⟩ := quotient_finite hV hE
  obtain ⟨T₁, T₂, hw⟩ := exists_tWitness_of_card_eq (H := quotient G) hVQ hEQ
    (fun e x h => quotient_loopless e x h)
    (fun X hX h2 => quotient_no_twoTree hV hE hX h2) hr (quotient_connected hconn) hcard
  exact tLift hV hE hw

end Lax630294Proofs.Quotient2Quotient
