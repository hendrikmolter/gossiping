import Lax630294Proofs.ProtectedExtSwap

/-!
# Protected extension: gluing (replacing `S[X]`) and the bridge property
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β} {x0 x1 u0 u1 : α} {e f0 f1 g : β}

lemma compl_glue {S SX' : Set β} {X : Set α} (hSX' : SX' ⊆ Ins H X) :
    E(H) \ ((S \ Ins H X) ∪ SX') = ((E(H) \ S) \ Ins H X) ∪ (Ins H X \ SX') := by
  ext k
  simp only [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨hgE, hn⟩
    by_cases hI : k ∈ Ins H X
    · exact Or.inr ⟨hI, fun h => hn (Or.inr h)⟩
    · exact Or.inl ⟨⟨hgE, fun hs => hn (Or.inl ⟨hs, hI⟩)⟩, hI⟩
  · rintro (⟨⟨hgE, hgS⟩, hgI⟩ | ⟨hgI, hgn⟩)
    · exact ⟨hgE, by rintro (⟨hs, _⟩ | hs'); exacts [hgS hs, hgI (hSX' hs')]⟩
    · exact ⟨ins_subset_edgeSet hgI, by rintro (⟨_, hI⟩ | hs'); exacts [hI hgI, hgn hs']⟩

/-- **The gluing step**: replacing `S[X]` by another spanning tree of `X`, where `X` lies in the
non-special component `R` of `K`, keeps the class (and the components of `K`). -/
lemma glue_cls (_hV : V(H).Finite) (hE : E(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    {S : Set β} (hS : Cls H x0 x1 u0 e f0 f1 g S) {a : α}
    (hns : Ns H x0 x1 u0 (E(H) \ S) a) {R X : Set α}
    (hR : ∀ y, y ∈ R ↔ Reach H (E(H) \ S) a y) (hXR : X ⊆ R)
    {SX' : Set β} (hSX' : SX' ⊆ Ins H X)
    (hStilde : IsSpanningTree H ((S \ Ins H X) ∪ SX'))
    (hKK : ∀ x y, Reach H (E(H) \ S) x y ↔
      Reach H (E(H) \ ((S \ Ins H X) ∪ SX')) x y)
    (hcnt : ((E(H) \ S) ∩ Ins H X).ncard = (Ins H X \ SX').ncard) :
    Cls H x0 x1 u0 e f0 f1 g ((S \ Ins H X) ∪ SX') := by
  set K := E(H) \ S with hKdef
  have hgK : g ∈ K := ⟨hS.hgE, hS.hgS⟩
  obtain ⟨hx0, hx1, hu0, hu1⟩ := Ns.ends geo hgK hns
  have hx0R : x0 ∉ R := fun h => hx0 ((hR _).1 h)
  have hx1R : x1 ∉ R := fun h => hx1 ((hR _).1 h)
  have hu0R : u0 ∉ R := fun h => hu0 ((hR _).1 h)
  have hu1R : u1 ∉ R := fun h => hu1 ((hR _).1 h)
  have hKt := compl_glue (S := S) hSX'
  have hnotIns : ∀ {k : β} {p q : α}, H.IsLink k p q → p ∉ R → k ∉ Ins H X := by
    intro k p q hl hp hk
    exact hp (hXR (ins_of_link hk hl).1)
  have hnotIns' : ∀ {k : β} {p q : α}, H.IsLink k p q → q ∉ R → k ∉ Ins H X := by
    intro k p q hl hq hk
    exact hq (hXR (ins_of_link hk hl).2)
  refine ⟨hStilde, ?_, ?_, ?_, hS.hgE, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.mem_union_left _ ⟨hS.he, hnotIns geo.le hx0R⟩
  · exact Set.mem_union_left _ ⟨hS.hf0, hnotIns geo.lf0 hx0R⟩
  · exact Set.mem_union_left _ ⟨hS.hf1, hnotIns geo.lf1 hx1R⟩
  · rintro (h | h)
    · exact hS.hgS h.1
    · exact hnotIns geo.lg hu0R (hSX' h)
  · exact fun h => hS.d01 ((hKK _ _).2 h)
  · exact fun h => hS.d0u ((hKK _ _).2 h)
  · exact fun h => hS.d1u ((hKK _ _).2 h)
  · intro A hA n0 n1 nu
    obtain ⟨v, hv⟩ := hA.1
    have hAeq : A = {y | CallOrder.Conn H (E(H) \ ((S \ Ins H X) ∪ SX')) v y} := hA.eq_comp hv
    have hmemA : ∀ y, y ∈ A ↔ Reach H K v y := fun y => by
      rw [hAeq]; exact (hKK v y).symm
    have hvV : v ∈ V(H) := hA.2.1 hv
    have hAc : CallOrder.IsComp H K A := by
      have : A = {y | CallOrder.Conn H K v y} := Set.ext fun y => hmemA y
      rw [this]; exact CallOrder.isComp_comp hvV
    have hi : A.ncard ≤ (CallOrder.edgesIn H K A).ncard := hS.inv A hAc n0 n1 nu
    have hEfin : (CallOrder.edgesIn H (E(H) \ ((S \ Ins H X) ∪ SX')) A).Finite :=
      hE.subset (CallOrder.edgesIn_subset _ _)
    refine hi.trans ?_
    by_cases hvR : v ∈ R
    · -- `A = R`
      have hAR : A = R := Set.ext fun y => by
        rw [hmemA, hR]
        constructor
        · intro h; exact ((hR v).1 hvR).trans' h
        · intro h; exact ((hR v).1 hvR).symm'.trans' h
      subst hAR
      have hEKfin : (CallOrder.edgesIn H K A).Finite := hE.subset (CallOrder.edgesIn_subset _ _)
      have hEKXfin : (K ∩ Ins H X).Finite := hE.subset (Set.inter_subset_left.trans Set.sdiff_subset)
      have hsub1 : CallOrder.edgesIn H K A ⊆
          (CallOrder.edgesIn H K A \ Ins H X) ∪ (K ∩ Ins H X) := by
        intro k hk
        by_cases hkI : k ∈ Ins H X
        · exact Or.inr ⟨hk.1, hkI⟩
        · exact Or.inl ⟨hk, hkI⟩
      have hle1 := Set.ncard_le_ncard hsub1 ((hEKfin.sdiff).union hEKXfin)
      have hle2 := Set.ncard_union_le (CallOrder.edgesIn H K A \ Ins H X) (K ∩ Ins H X)
      have hdisj : Disjoint (CallOrder.edgesIn H K A \ Ins H X) (Ins H X \ SX') :=
        Set.disjoint_left.2 fun k hk1 hk2 => hk1.2 hk2.1
      have hsub2 : (CallOrder.edgesIn H K A \ Ins H X) ∪ (Ins H X \ SX') ⊆
          CallOrder.edgesIn H (E(H) \ ((S \ Ins H X) ∪ SX')) A := by
        intro k hk
        rcases hk with hk | hk
        · refine ⟨?_, hk.1.2⟩
          rw [hKt]; exact Or.inl ⟨hk.1.1, hk.2⟩
        · refine ⟨?_, ins_mono hXR hk.1⟩
          rw [hKt]; exact Or.inr hk
      have hle3 := Set.ncard_le_ncard hsub2 hEfin
      have hInsfin : (Ins H X).Finite := hE.subset ins_subset_edgeSet
      rw [Set.ncard_union_eq hdisj (hEKfin.sdiff) (hInsfin.sdiff)] at hle3
      omega
    · refine Set.ncard_le_ncard ?_ hEfin
      intro k hk
      have hkI : k ∉ Ins H X := by
        intro hkI
        obtain ⟨p, q, hpq⟩ := Graph.exists_isLink_of_mem_edgeSet hk.1.1
        have hp := (ins_of_link hkI hpq).1
        have hpA : p ∈ A := (hk.2.ends_mem hpq).1
        exact hvR ((hR v).2 (((hR p).1 (hXR hp)).trans' ((hmemA p).1 hpA).symm'))
      refine ⟨?_, hk.2⟩
      rw [hKt]; exact Or.inl ⟨hk.1, hkI⟩

end Lax630294Proofs.ProtectedExt
