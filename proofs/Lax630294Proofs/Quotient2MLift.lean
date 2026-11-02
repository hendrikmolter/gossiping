import Lax630294Proofs.Quotient2Quotient
import Lax630294Proofs.Quotient2Cycle
import Lax630294.MGraph

/-!
# Lifting an `M`-witness of the quotient: `lem:characterization-threshold`,
`lem:characterization-m-lift`

`m_lift` is the M-lift for a quotient cycle of arbitrary length `n ≥ 4`, with the blocks `U i`, the
cycle edges `d i` and the ports `p i, q i` (`d i` joins `q i ∈ U i` and `p (i+1) ∈ U (i+1)`)
explicit, indexed by `ZMod n`; `m_lift4` is the corollary `n = 4`.

DEVIATION: the cycle `D` of the M-witness is given as an indexing `U, d, p, q` by `ZMod n`
(injectivity of `U`, `d`, `range d = D`), instead of "each block X on D with ports p_X, q_X";
these are supplied by the caller (`Necessity`).

DEVIATION: the paper shows that each lifted forest has no cycle by projecting the external edges of
a cycle to a closed trail in the quotient forest.  Here this is replaced by the counting argument
already in the library (`Fib`, `lift_spanningForest`: a fibre-wise forest union an edge set of the
quotient is a spanning forest iff the component count matches).

DEVIATION: the "two spanning trees" of the paper are replaced by two edge-disjoint *connected*
spanning edge sets (`LocalCond`); a connected spanning edge set contains a spanning tree, and the
proof shrinks them to trees.  `P` is a path given by an explicit duplicate-free walk (`IsPathSet`).
The off-cycle blocks use the two edge-disjoint fibre forests of `exists_family`.
-/

namespace Lax630294Proofs.Quotient2MLift

open Graph Lax630294.SpanningStructures Lax630294.TGraph Lax630294.MGraph
  Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.QuotientExchange Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Family
  Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2Cycle

variable {α β : Type*} {G : Graph α β}

/-- The local lifting condition for the vertex set `X` (a block) and ports `p, q`: two
edge-disjoint connected spanning edge sets `A, B` of `G[X]` and a `p`-`q` path with edge set `P`
inside `G[X]`, the three edge sets being pairwise disjoint. -/
def LocalCond (G : Graph α β) (X : Set α) (p q : α) : Prop :=
  ∃ A B P : Set β, A ⊆ Ins G X ∧ B ⊆ Ins G X ∧ P ⊆ Ins G X ∧
    Disjoint A B ∧ Disjoint A P ∧ Disjoint B P ∧
    (∀ x ∈ X, ∀ y ∈ X, Reach G A x y) ∧ (∀ x ∈ X, ∀ y ∈ X, Reach G B x y) ∧
    IsPathSet G p q P

/-- `lem:characterization-threshold`: a connected "upper" edge set `E⁺` and a `p`-`q` path `P` in
the disjoint "lower" edge set `E⁻` whose removal leaves `E⁻` connected give the local condition. -/
theorem threshold {X : Set α} {Em Ep P : Set β} {p q : α} (hdisj : Disjoint Em Ep)
    (hEm : Em ⊆ Ins G X) (hEp : Ep ⊆ Ins G X)
    (hconn : ∀ x ∈ X, ∀ y ∈ X, Reach G Ep x y) (hP : IsPathSet G p q P) (hPE : P ⊆ Em)
    (hrest : ∀ x ∈ X, ∀ y ∈ X, Reach G (Em \ P) x y) : LocalCond G X p q :=
  ⟨Em \ P, Ep, P, Set.sdiff_subset.trans hEm, hEp, hPE.trans hEm,
    hdisj.mono_left Set.sdiff_subset, Set.disjoint_sdiff_left,
    (hdisj.mono_left hPE).symm, hrest, hconn, hP⟩

/-! ### Helper lemmas on blocks -/

lemma blk_of_mem (hV : V(G).Finite) (hE : E(G).Finite) {U : Set α} (hU : U ∈ V(quotient G))
    {w : α} (hw : w ∈ U) : blk G w = U := by
  obtain ⟨z, hz, rfl⟩ := hU
  exact blk_eq_of_mem hV hE hz hw

lemma ins_not_ext (hV : V(G).Finite) (hE : E(G).Finite) {U : Set α} (hU : U ∈ V(quotient G))
    {e : β} (he : e ∈ Ins G U) : e ∉ E(quotient G) := by
  intro hE'
  obtain ⟨x, y, hl, hne⟩ := mem_edgeSet_quotient.1 hE'
  obtain ⟨hx, hy⟩ := ins_of_link he hl
  exact hne ((blk_of_mem hV hE hU hx).trans (blk_of_mem hV hE hU hy).symm)

lemma quotient_disjoint (hV : V(G).Finite) (hE : E(G).Finite) {U W : Set α}
    (hU : U ∈ V(quotient G)) (hW : W ∈ V(quotient G)) (hne : U ≠ W) : Disjoint U W := by
  obtain ⟨x, hx, rfl⟩ := hU
  obtain ⟨y, hy, rfl⟩ := hW
  exact (blk_eq_or_disjoint hV hE hx hy).resolve_left hne

lemma meeting_lift (_hV : V(G).Finite) (_hE : E(G).Finite) {I L D D' : Set β}
    (hI : Fib G (blk G) I)
    (hmeet : ∀ x : V(quotient G), ∃ c : V(quotient G),
      (c : Set α) ∈ incidentVertices (quotient G) D ∧ (underlying (quotient G) L).Reachable x c)
    (hrep : ∀ c ∈ incidentVertices (quotient G) D,
      ∃ w ∈ V(G), blk G w = c ∧ w ∈ incidentVertices G D') :
    ∀ x : V(G), ∃ c : V(G), (c : α) ∈ incidentVertices G D' ∧
      (underlying G (L ∪ I)).Reachable x c := by
  intro x
  obtain ⟨c, hc, hr⟩ := hmeet ⟨blk G x, x, x.2, rfl⟩
  obtain ⟨w, hw, hbw, hwD⟩ := hrep c.1 hc
  refine ⟨⟨w, hw⟩, hwD, ?_⟩
  rw [underlying_reachable_iff]
  have h1 : Reach (quotient G) L (blk G x) c.1 := (underlying_reachable_iff _ _).1 hr
  rw [← hbw] at h1
  exact reach_of_reach_contract hI.conn x.2 hw h1

/-- Concatenating the walks `BV k, BE k` (`k < m`) gives a walk from `p 0` to `p m`. -/
lemma chain_concat {n : ℕ} [NeZero n] (p : ZMod n → α) (BV : ZMod n → List α)
    (BE : ZMod n → List β) (hch : ∀ i, Chain G (p i) (BV i) (BE i) (p (i + 1))) (m : ℕ) :
    Chain G (p 0) ((List.range m).flatMap fun k : ℕ => BV (k : ZMod n))
      ((List.range m).flatMap fun k : ℕ => BE (k : ZMod n)) (p (m : ZMod n)) := by
  induction m with
  | zero => simpa using Chain.nil (G := G) (p 0)
  | succ m ih =>
    have h := ih.append (hch (m : ZMod n))
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, Nat.cast_succ]
    simpa using h

lemma natCast_ne_of_lt {n : ℕ} [NeZero n] {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  intro h
  apply hab
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this

lemma nodup_concat {n : ℕ} [NeZero n] {γ : Type*} {L : ZMod n → List γ}
    (hn : ∀ i, (L i).Nodup) (hd : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a ≠ b) :
    ((List.range n).flatMap fun k : ℕ => L (k : ZMod n)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => hn _, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b ha hb hab x hx hx'
  exact hd _ _ (natCast_ne_of_lt (List.mem_range.1 ha) (List.mem_range.1 hb) hab.ne) x hx x hx'
    rfl

lemma mem_concat {n : ℕ} [NeZero n] {γ : Type*} (L : ZMod n → List γ) (e : γ) :
    e ∈ (List.range n).flatMap (fun k : ℕ => L (k : ZMod n)) ↔ ∃ i, e ∈ L i := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, _, hk⟩; exact ⟨_, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, List.mem_range.2 (ZMod.val_lt i), by rwa [ZMod.natCast_zmod_val]⟩

/-- **`lem:characterization-m-lift`**, for an arbitrary quotient cycle of length `n ≥ 4`.

`(U i, d i)_{i : ZMod n}` is the cycle `D = range d` of the quotient `Q` (the blocks `U i` and edges
`d i` are pairwise distinct), `d i` joins `q i ∈ U i` and `p (i+1) ∈ U (i+1)` in `G`, `p i, q i`
are the ports of the block `U i`, and each block satisfies the local condition.  If `Q` has the
`M`-witness `(D, L₁, L₂)`, then `G` admits an `M`-witness. -/
theorem m_lift (hV : V(G).Finite) (hE : E(G).Finite) {D L₁ L₂ : Set β}
    (hM : IsMWitness (quotient G) D L₁ L₂) (n : ℕ) (hn4 : 4 ≤ n)
    (U : ZMod n → Set α) (d : ZMod n → β) (p q : ZMod n → α)
    (hUinj : Function.Injective U) (hdinj : Function.Injective d) (hD : Set.range d = D)
    (hdl : ∀ i, (quotient G).IsLink (d i) (U i) (U (i + 1)))
    (hport : ∀ i, G.IsLink (d i) (q i) (p (i + 1)))
    (hq : ∀ i, q i ∈ U i) (hp : ∀ i, p i ∈ U i)
    (hloc : ∀ i, LocalCond G (U i) (p i) (q i)) : AdmitsMWitness G := by
  classical
  have : NeZero n := ⟨by omega⟩
  obtain ⟨_, _, ⟨hF1, hm1⟩, ⟨hF2, hm2⟩, hDL1, hDL2, hL12⟩ := hM
  have hL1E : L₁ ⊆ E(quotient G) := hF1.1
  have hL2E : L₂ ⊆ E(quotient G) := hF2.1
  have hDsubd : ∀ i, d i ∈ D := fun i => hD ▸ ⟨i, rfl⟩
  have hDE : D ⊆ E(quotient G) := by
    rw [← hD]; rintro _ ⟨i, rfl⟩; exact (hdl i).edge_mem
  have hUQ : ∀ i, U i ∈ V(quotient G) := fun i => (hdl i).left_mem
  have hUV : ∀ i, U i ⊆ V(G) := by
    intro i
    obtain ⟨z, hz, h⟩ := hUQ i
    rw [← h]; exact blk_subset hV hE hz
  have hUd : ∀ i j, i ≠ j → Disjoint (U i) (U j) := fun i j hij =>
    quotient_disjoint hV hE (hUQ i) (hUQ j) (fun h => hij (hUinj h))
  -- local data: shrink the connected sets to trees
  have hloc' : ∀ i, ∃ A B P : Set β, TreeLike G (U i) A ∧ TreeLike G (U i) B ∧ Disjoint A B ∧
      Disjoint A P ∧ Disjoint B P ∧ P ⊆ Ins G (U i) ∧ IsPathSet G (p i) (q i) P := by
    intro i
    obtain ⟨A, B, P, hA, hB, hPI, hAB, hAP, hBP, hcA, hcB, hPath⟩ := hloc i
    obtain ⟨A', hA'A, hA'⟩ := exists_treeLike_subset hV hE (hUV i) ⟨p i, hp i⟩ hA hcA
    obtain ⟨B', hB'B, hB'⟩ := exists_treeLike_subset hV hE (hUV i) ⟨p i, hp i⟩ hB hcB
    exact ⟨A', B', P, hA', hB', hAB.mono hA'A hB'B, hAP.mono_left hA'A, hBP.mono_left hB'B, hPI,
      hPath⟩
  choose A B P hA hB hAB hAP hBP hPI hPath using hloc'
  -- the two fibre forests
  obtain ⟨Af, Bf, hAf, hBf, hdf⟩ := exists_family hV hE
  have hfam1 : FamOK G (ovr Af U A) := ovr_famOK hUinj hAf hA
  have hfam2 : FamOK G (ovr Bf U B) := ovr_famOK hUinj hBf hB
  have hdisj : ∀ x ∈ V(G), Disjoint (ovr Af U A (blk G x)) (ovr Bf U B (blk G x)) := by
    intro x hx
    by_cases h : ∃ i, U i = blk G x
    · obtain ⟨i, hi⟩ := h
      rw [← hi, ovr_at hUinj, ovr_at hUinj]; exact hAB i
    · push Not at h
      rw [ovr_off h, ovr_off h]; exact hdf x hx
  obtain ⟨I1, I2, hI1, hI2, hI12, hI1A, hI2B⟩ : ∃ I1 I2 : Set β, Fib G (blk G) I1 ∧
      Fib G (blk G) I2 ∧ Disjoint I1 I2 ∧ (∀ i, I1 ∩ Ins G (U i) = A i) ∧
      (∀ i, I2 ∩ Ins G (U i) = B i) := by
    refine ⟨famUnion G (ovr Af U A), famUnion G (ovr Bf U B), fam_fib hV hE hfam1,
      fam_fib hV hE hfam2, fam_disjoint hV hE hfam1 hfam2 hdisj, fun i => ?_, fun i => ?_⟩
    · obtain ⟨z, hz, h⟩ := hUQ i
      have := famUnion_inter_ins hV hE hfam1 hz
      rw [h, ovr_at hUinj] at this
      exact this
    · obtain ⟨z, hz, h⟩ := hUQ i
      have := famUnion_inter_ins hV hE hfam2 hz
      rw [h, ovr_at hUinj] at this
      exact this
  -- the lifted cycle, as lists
  obtain ⟨BV, BE, hch, hBVn, hBEn, hBVm, hBEm⟩ : ∃ (BV : ZMod n → List α) (BE : ZMod n → List β),
      (∀ i, Chain G (p i) (BV i) (BE i) (p (i + 1))) ∧ (∀ i, (BV i).Nodup) ∧
      (∀ i, (BE i).Nodup) ∧ (∀ i v, v ∈ BV i → v ∈ U i) ∧
      (∀ i e, e ∈ BE i ↔ e = d i ∨ e ∈ P i) := by
    have hPath' : ∀ i, ∃ (vs : List α) (es : List β), Chain G (p i) vs es (q i) ∧
        (vs ++ [q i]).Nodup ∧ es.Nodup ∧ {e | e ∈ es} = P i := hPath
    choose vs es hc hvn hen hes using hPath'
    have hesm : ∀ i e, e ∈ es i ↔ e ∈ P i := fun i e => by rw [← hes i]; rfl
    refine ⟨fun i => vs i ++ [q i], fun i => es i ++ [d i], fun i => ?_, hvn, fun i => ?_,
      fun i v hv => ?_, fun i e => ?_⟩
    · exact (hc i).append (Chain.single (hport i))
    · rw [List.nodup_append]
      refine ⟨hen i, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      exact ins_not_ext hV hE (hUQ i) (hPI i ((hesm i a).1 ha)) (hab ▸ hDE (hDsubd i))
    · obtain ⟨h1, h2⟩ := (hc i).mem_of_ins (fun e he => hPI i ((hesm i e).1 he)) (hp i)
      rcases List.mem_append.1 hv with hv | hv
      · exact h1 v hv
      · rw [List.mem_singleton] at hv; exact hv ▸ h2
    · simp only [List.mem_append, List.mem_singleton, hesm]
      tauto
  -- distinctness
  have hVd : ∀ i j, i ≠ j → ∀ a ∈ BV i, ∀ b ∈ BV j, a ≠ b := by
    intro i j hij a ha b hb hab
    subst hab
    exact Set.disjoint_left.1 (hUd i j hij) (hBVm i a ha) (hBVm j a hb)
  have hEd : ∀ i j, i ≠ j → ∀ a ∈ BE i, ∀ b ∈ BE j, a ≠ b := by
    intro i j hij a ha b hb hab
    subst hab
    rcases (hBEm i a).1 ha with h1 | h1 <;> rcases (hBEm j a).1 hb with h2 | h2
    · exact hij (hdinj (h1.symm.trans h2))
    · exact ins_not_ext hV hE (hUQ j) (hPI j h2) (h1 ▸ hDE (hDsubd i))
    · exact ins_not_ext hV hE (hUQ i) (hPI i h1) (h2 ▸ hDE (hDsubd j))
    · obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet
        (ins_subset_edgeSet (hPI i h1))
      exact Set.disjoint_left.1 (hUd i j hij) (ins_of_link (hPI i h1) hl).1
        (ins_of_link (hPI j h2) hl).1
  -- chain of the whole cycle: replace each vertex `U i` of the quotient cycle by its path
  have hcyc : Chain G (p 0) ((List.range n).flatMap fun k : ℕ => BV (k : ZMod n))
      ((List.range n).flatMap fun k : ℕ => BE (k : ZMod n)) (p 0) := by
    have := chain_concat p BV BE hch n
    rwa [ZMod.natCast_self] at this
  have hVnd := nodup_concat hBVn hVd
  have hEnd := nodup_concat hBEn hEd
  have hEmem : ∀ e, e ∈ (List.range n).flatMap (fun k : ℕ => BE (k : ZMod n)) ↔ ∃ i, e ∈ BE i :=
    mem_concat BE
  have hne : (List.range n).flatMap (fun k : ℕ => BE (k : ZMod n)) ≠ [] := by
    intro h
    have := (hEmem (d 0)).2 ⟨0, (hBEm 0 _).2 (Or.inl rfl)⟩
    rw [h] at this
    simp at this
  obtain ⟨D', hD'cyc, hD'card, hDsub, hD'cases⟩ : ∃ D' : Set β, IsCycle G D' ∧ 4 ≤ D'.encard ∧
      D ⊆ D' ∧ ∀ e ∈ D', e ∈ D ∨ ∃ i, e ∈ P i := by
    refine ⟨{e | e ∈ (List.range n).flatMap fun k : ℕ => BE (k : ZMod n)},
      isCycle_of_chain hcyc hVnd hEnd hne, ?_, ?_, ?_⟩
    · have hsub : D ⊆ {e | e ∈ (List.range n).flatMap fun k : ℕ => BE (k : ZMod n)} := by
        rw [← hD]
        rintro _ ⟨i, rfl⟩
        exact (hEmem _).2 ⟨i, (hBEm i _).2 (Or.inl rfl)⟩
      have h1 : (ENat.card (ZMod n)) ≤ D.encard := by
        rw [← hD]; exact hdinj.encard_range
      rw [ENat.card_eq_coe_natCard, Nat.card_zmod] at h1
      refine le_trans ?_ (h1.trans (Set.encard_le_encard hsub))
      exact_mod_cast hn4
    · rw [← hD]
      rintro _ ⟨i, rfl⟩
      exact (hEmem _).2 ⟨i, (hBEm i _).2 (Or.inl rfl)⟩
    · intro e he
      obtain ⟨i, hi⟩ := (hEmem e).1 he
      rcases (hBEm i e).1 hi with rfl | h
      · exact Or.inl (hDsubd i)
      · exact Or.inr ⟨i, h⟩
  -- representatives for the incident vertices
  have hrep : ∀ c ∈ incidentVertices (quotient G) D,
      ∃ w ∈ V(G), blk G w = c ∧ w ∈ incidentVertices G D' := by
    rintro c ⟨e, he, y, hl⟩
    rw [← hD] at he
    obtain ⟨j, rfl⟩ := he
    rcases (hdl j).eq_and_eq_or_eq_and_eq hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨q j, (hport j).left_mem, ?_, d j, hDsub (hDsubd j), p (j + 1), hport j⟩
      rw [← h1]; exact blk_of_mem hV hE (hUQ j) (hq j)
    · refine ⟨p (j + 1), (hport j).right_mem, ?_, d j, hDsub (hDsubd j), q j, (hport j).symm⟩
      rw [← h2]; exact blk_of_mem hV hE (hUQ (j + 1)) (hp (j + 1))
  -- disjointness of the cycle from a lifted forest
  have hdisjD : ∀ (L I : Set β) (S : ZMod n → Set β), Disjoint D L → L ⊆ E(quotient G) →
      Fib G (blk G) I → (∀ i, I ∩ Ins G (U i) = S i) → (∀ i, Disjoint (S i) (P i)) →
      Disjoint D' (L ∪ I) := by
    intro L I S hDL hLE hI hIS hSP
    rw [Set.disjoint_union_right]
    constructor
    · refine Set.disjoint_left.2 fun e he hL => ?_
      rcases hD'cases e he with h | ⟨i, hPi⟩
      · exact Set.disjoint_left.1 hDL h hL
      · exact ins_not_ext hV hE (hUQ i) (hPI i hPi) (hLE hL)
    · refine Set.disjoint_left.2 fun e he hIe => ?_
      rcases hD'cases e he with h | ⟨i, hPi⟩
      · exact Set.disjoint_left.1 hI.disjoint_ext hIe (hDE h)
      · have : e ∈ I ∩ Ins G (U i) := ⟨hIe, hPI i hPi⟩
        rw [hIS i] at this
        exact Set.disjoint_left.1 (hSP i) this hPi
  refine ⟨D', L₁ ∪ I1, L₂ ∪ I2, hD'cyc, hD'card,
    ⟨(lift_spanningForest hV hE hI1 hL1E).1 hF1, meeting_lift hV hE hI1 hm1 hrep⟩,
    ⟨(lift_spanningForest hV hE hI2 hL2E).1 hF2, meeting_lift hV hE hI2 hm2 hrep⟩,
    hdisjD L₁ I1 A hDL1 hL1E hI1 hI1A hAP, hdisjD L₂ I2 B hDL2 hL2E hI2 hI2B hBP, ?_⟩
  rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
  refine ⟨⟨hL12, ?_⟩, ?_, hI12⟩
  · exact (hI2.disjoint_ext.symm).mono_left hL1E
  · exact hI1.disjoint_ext.mono_right hL2E

/-- The length-four case, as a corollary of `m_lift`. -/
theorem m_lift4 (hV : V(G).Finite) (hE : E(G).Finite) {D L₁ L₂ : Set β}
    (hM : IsMWitness (quotient G) D L₁ L₂)
    (U : ZMod 4 → Set α) (d : ZMod 4 → β) (p q : ZMod 4 → α)
    (hUinj : Function.Injective U) (hdinj : Function.Injective d) (hD : Set.range d = D)
    (hdl : ∀ i, (quotient G).IsLink (d i) (U i) (U (i + 1)))
    (hport : ∀ i, G.IsLink (d i) (q i) (p (i + 1)))
    (hq : ∀ i, q i ∈ U i) (hp : ∀ i, p i ∈ U i)
    (hloc : ∀ i, LocalCond G (U i) (p i) (q i)) : AdmitsMWitness G :=
  m_lift hV hE hM 4 le_rfl U d p q hUinj hdinj hD hdl hport hq hp hloc

end Lax630294Proofs.Quotient2MLift
