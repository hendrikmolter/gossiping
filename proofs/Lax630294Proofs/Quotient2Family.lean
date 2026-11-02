import Lax630294Proofs.Quotient2Contract

/-!
# Families of internal trees, one per block

`TreeLike G X A`: `A` is (the edge set of) a spanning tree of `G[X]`, seen inside `G`.
A *family* assigns such a tree to every block; its union is a fibre forest for `blk G`
(`fam_fib`).  `exists_AB` : two disjoint fibre forests `A, B` for `blk G`.
-/

namespace Lax630294Proofs.Quotient2Family

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs.QuotientBlocks
  Lax630294Proofs.QuotientDef Lax630294Proofs.Quotient2Contract

variable {α β : Type*} {G : Graph α β} {X : Set α} {A B : Set β} {x y z : α} {e : β}
  {tr : Set α → Set β}

/-- `A` is a spanning tree of `G[X]`, expressed inside `G`. -/
def TreeLike (G : Graph α β) (X : Set α) (A : Set β) : Prop :=
  A ⊆ Ins G X ∧ IsForest G A ∧ ∀ x ∈ X, ∀ y ∈ X, Reach G A x y

lemma treeLike_of_spanningTree (hV : V(G).Finite) (hE : E(G).Finite) (hX : X ⊆ V(G))
    (hA : IsSpanningTree (G.induce X) A) : TreeLike G X A := by
  obtain ⟨hVf, hEf⟩ := finite_induce hV hE hX
  obtain ⟨hAE, _, hconn, _⟩ := (isSpanningTree_iff hVf hEf).1 hA
  refine ⟨hAE, ?_, fun x hx y hy => (reach_induce_iff hAE).1 (hconn x hx y hy)⟩
  have : IsForest (G.induce X) A := ⟨hA.2.1, hA.2.2.isAcyclic⟩
  exact (isForest_induce_iff hE hAE).1 this

lemma exists_treeLike_subset (hV : V(G).Finite) (hE : E(G).Finite) (hX : X ⊆ V(G))
    (hne : X.Nonempty) (hA : A ⊆ Ins G X) (hc : ∀ x ∈ X, ∀ y ∈ X, Reach G A x y) :
    ∃ A' ⊆ A, TreeLike G X A' := by
  obtain ⟨hVf, hEf⟩ := finite_induce hV hE hX
  obtain ⟨A', hA', ht⟩ := exists_spanning_tree_subset hVf hEf _ A rfl hA hne
    (fun x hx y hy => (reach_induce_iff hA).2 (hc x hx y hy))
  exact ⟨A', hA', treeLike_of_spanningTree hV hE hX ht⟩

/-- A family of trees, one in each block. -/
def FamOK (G : Graph α β) (tr : Set α → Set β) : Prop :=
  ∀ x ∈ V(G), TreeLike G (blk G x) (tr (blk G x))

/-- The union of a family. -/
def famUnion (G : Graph α β) (tr : Set α → Set β) : Set β :=
  {e | ∃ x ∈ V(G), e ∈ tr (blk G x)}

lemma famUnion_inter_ins (hV : V(G).Finite) (hE : E(G).Finite) (hfam : FamOK G tr)
    (hx : x ∈ V(G)) : famUnion G tr ∩ Ins G (blk G x) = tr (blk G x) := by
  apply Set.Subset.antisymm
  · rintro e ⟨⟨z, hz, hez⟩, hex⟩
    obtain ⟨a, b, hl, ha, hb⟩ := hex
    obtain ⟨ha', _⟩ := ins_of_link ((hfam z hz).1 hez) hl
    have h1 := blk_eq_of_mem hV hE hx ha
    have h2 := blk_eq_of_mem hV hE hz ha'
    have : blk G z = blk G x := h2.symm.trans h1
    rw [this] at hez
    exact hez
  · intro e he
    exact ⟨⟨x, hx, he⟩, (hfam x hx).1 he⟩

lemma fam_subset (hfam : FamOK G tr) : famUnion G tr ⊆ E(G) := by
  rintro e ⟨z, hz, hez⟩
  exact ins_subset_edgeSet ((hfam z hz).1 hez)

lemma fam_fib (hV : V(G).Finite) (hE : E(G).Finite) (hfam : FamOK G tr) :
    Fib G (blk G) (famUnion G tr) := by
  have hint : ∀ e ∈ famUnion G tr, ∀ a b, G.IsLink e a b → blk G a = blk G b := by
    rintro e ⟨z, hz, hez⟩ a b hl
    obtain ⟨ha, hb⟩ := ins_of_link ((hfam z hz).1 hez) hl
    rw [blk_eq_of_mem hV hE hz ha, blk_eq_of_mem hV hE hz hb]
  refine ⟨fam_subset hfam, hint, ?_, ?_⟩
  · intro x hx y hy hxy
    have hy' : y ∈ blk G x := by rw [hxy]; exact mem_blk_self hV hE hy
    exact reach_mono (fun e he => ⟨x, hx, he⟩)
      ((hfam x hx).2.2 x (mem_blk_self hV hE hx) y hy')
  · have hfin : (famUnion G tr).Finite := hE.subset (fam_subset hfam)
    rw [isForest_iff_bridges hfin (fam_subset hfam)]
    rintro e he p q hl hr
    obtain ⟨z, hz, hez⟩ := he
    obtain ⟨hp, hq⟩ := ins_of_link ((hfam z hz).1 hez) hl
    have hcl : Closed G (famUnion G tr \ {e}) (blk G z) := by
      rintro g ⟨hg, _⟩ a b hl' ha
      have h1 := hint g hg a b hl'
      have h2 := blk_eq_of_mem hV hE hz ha
      have h3 : blk G b = blk G z := h1.symm.trans h2
      rw [← h3]
      exact mem_blk_self hV hE hl'.right_mem
    obtain ⟨_, hr'⟩ := reach_closed hcl hp hr
    refine forest_bridge (hfam z hz).2.1 hez hl (reach_mono ?_ hr')
    rintro g ⟨⟨hg1, hg2⟩, hg3⟩
    refine ⟨?_, hg2⟩
    rw [← famUnion_inter_ins hV hE hfam hz]
    exact ⟨hg1, hg3⟩

lemma fam_disjoint {tr₁ tr₂ : Set α → Set β} (hV : V(G).Finite) (hE : E(G).Finite)
    (h₁ : FamOK G tr₁) (h₂ : FamOK G tr₂)
    (hd : ∀ x ∈ V(G), Disjoint (tr₁ (blk G x)) (tr₂ (blk G x))) :
    Disjoint (famUnion G tr₁) (famUnion G tr₂) := by
  refine Set.disjoint_left.2 fun e he₁ he₂ => ?_
  obtain ⟨z, hz, hez⟩ := he₁
  have : e ∈ famUnion G tr₂ ∩ Ins G (blk G z) := ⟨he₂, (h₁ z hz).1 hez⟩
  rw [famUnion_inter_ins hV hE h₂ hz] at this
  exact Set.disjoint_left.1 (hd z hz) hez this

lemma exists_family (hV : V(G).Finite) (hE : E(G).Finite) :
    ∃ Af Bf : Set α → Set β, FamOK G Af ∧ FamOK G Bf ∧
      ∀ x ∈ V(G), Disjoint (Af (blk G x)) (Bf (blk G x)) := by
  have : ∀ U : Set α, ∃ A B : Set β, (∃ x ∈ V(G), blk G x = U) →
      (TreeLike G U A ∧ TreeLike G U B ∧ Disjoint A B) := by
    intro U
    by_cases h : ∃ x ∈ V(G), blk G x = U
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨_, _, A, B, hA, hB, hAB⟩ := isTwoTreeSet_blk hV hE hx
      exact ⟨A, B, fun _ => ⟨treeLike_of_spanningTree hV hE (blk_subset hV hE hx) hA,
        treeLike_of_spanningTree hV hE (blk_subset hV hE hx) hB, hAB⟩⟩
    · exact ⟨∅, ∅, fun h' => absurd h' h⟩
  choose Af Bf h using this
  exact ⟨Af, Bf, fun x hx => (h _ ⟨x, hx, rfl⟩).1, fun x hx => (h _ ⟨x, hx, rfl⟩).2.1,
    fun x hx => (h _ ⟨x, hx, rfl⟩).2.2⟩

/-- Two disjoint fibre forests for `blk G` (one pair of internal spanning trees per block). -/
theorem exists_AB (hV : V(G).Finite) (hE : E(G).Finite) :
    ∃ A B : Set β, Fib G (blk G) A ∧ Fib G (blk G) B ∧ Disjoint A B := by
  obtain ⟨Af, Bf, hA, hB, hd⟩ := exists_family hV hE
  exact ⟨_, _, fam_fib hV hE hA, fam_fib hV hE hB, fam_disjoint hV hE hA hB hd⟩

/-- Override a family on the blocks `U i`. -/
noncomputable def ovr (tr : Set α → Set β) {ι : Type*} (U : ι → Set α) (S : ι → Set β) :
    Set α → Set β := by
  classical
  exact fun W => if h : ∃ i, U i = W then S h.choose else tr W

lemma ovr_at {ι : Type*} {U : ι → Set α} {S : ι → Set β} (hU : Function.Injective U) (j : ι) :
    ovr tr U S (U j) = S j := by
  classical
  have h : ∃ i, U i = U j := ⟨j, rfl⟩
  simp only [ovr, dif_pos h]
  rw [hU h.choose_spec]

lemma ovr_off {ι : Type*} {U : ι → Set α} {S : ι → Set β} {W : Set α} (h : ∀ i, U i ≠ W) :
    ovr tr U S W = tr W := by
  classical
  have h' : ¬ ∃ i, U i = W := fun ⟨i, hi⟩ => h i hi
  simp only [ovr, dif_neg h']

lemma ovr_famOK {ι : Type*} {U : ι → Set α} {S : ι → Set β} (hU : Function.Injective U)
    (hfam : FamOK G tr) (hS : ∀ i, TreeLike G (U i) (S i)) : FamOK G (ovr tr U S) := by
  intro x hx
  by_cases h : ∃ i, U i = blk G x
  · obtain ⟨i, hi⟩ := h
    rw [← hi, ovr_at hU]
    exact hS i
  · push Not at h
    rw [ovr_off h]
    exact hfam x hx

end Lax630294Proofs.Quotient2Family
