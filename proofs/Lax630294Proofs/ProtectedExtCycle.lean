import Lax630294Proofs.ProtectedExtGlue

/-!
# Protected extension: a non-bridge of `K` lies inside one component of `S[R]`

This is `cycle_in_class` of `QuotientExchange`, with the bridge property assumed only at the base
vertex `a` (this is all that is used).
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β}

lemma cycle_in_class' (hE : E(H).Finite) {S : Set β} {a b : α} {g : β}
    (hbr : ∀ k, k ∈ E(H) \ S → ∀ w y, H.IsLink k w y → Reach H (E(H) \ S) a w →
      ¬ Reach H (S ∩ Ins H {y | Reach H (E(H) \ S) a y}) w y →
      ¬ Reach H ((E(H) \ S) \ {k}) w y)
    (hg : g ∈ E(H) \ S) (hl : H.IsLink g a b)
    (hr : Reach H ((E(H) \ S) \ {g}) a b) {R X : Set α}
    (hR : ∀ y, y ∈ R ↔ Reach H (E(H) \ S) a y)
    (hX : ∀ y, y ∈ X ↔ Reach H (S ∩ Ins H R) a y) :
    b ∈ X ∧ Reach H (((E(H) \ S) ∩ Ins H X) \ {g}) a b := by
  have hKE : E(H) \ S ⊆ E(H) := Set.sdiff_subset
  have hRset : {y | Reach H (E(H) \ S) a y} = R := Set.ext fun y => (hR y).symm
  let N : Set β := {h | h ∈ E(H) \ S ∧ ∃ p q, H.IsLink h p q ∧ Reach H ((E(H) \ S) \ {h}) p q}
  have hNg : Reach H (N \ {g}) a b := by
    by_contra hnot
    obtain ⟨f, hf, p, q, hfl, h1, h2⟩ := cut_lemma (G := H) (F₀ := N \ {g})
      (F' := (E(H) \ S) \ {g}) (Set.sdiff_subset_sdiff_left (fun h hh => hh.1))
      ((hE.subset hKE).subset Set.sdiff_subset) (Set.sdiff_subset.trans hKE) hr hnot
    have hfN : f ∉ N := fun hN => hf.2 ⟨hN, hf.1.2⟩
    apply hfN
    refine ⟨hf.1.1, p, q, hfl, ?_⟩
    have hsubK : ((E(H) \ S) \ {g}) \ {f} ⊆ (E(H) \ S) \ {f} := fun z hz => ⟨hz.1.1, hz.2⟩
    have hgK : g ∈ (E(H) \ S) \ {f} := ⟨hg, fun h => hf.1.2 h.symm⟩
    exact ((reach_mono hsubK h1).symm').trans'
      ((reach_of_isLink hgK hl).trans' (reach_mono hsubK h2).symm')
  have hXR : ∀ w, w ∈ X → w ∈ R := by
    intro w hw
    have hcl : Closed H (S ∩ Ins H R) R := fun g hg x y hl hx => (ins_of_link hg.2 hl).2
    have haR : a ∈ R := (hR a).2 reach_refl
    exact (reach_closed hcl haR ((hX w).1 hw)).1
  have key : ∀ x, Reach H (N \ {g}) a x →
      x ∈ X ∧ Reach H (((E(H) \ S) ∩ Ins H X) \ {g}) a x := by
    intro x h
    induction h with
    | refl => exact ⟨(hX a).2 reach_refl, reach_refl⟩
    | @tail w y _ hs ih =>
      obtain ⟨h, hh, hhl⟩ := hs
      obtain ⟨⟨hhK, p, q, hpql, hbr'⟩, hhg⟩ := hh
      have hwy : Reach H ((E(H) \ S) \ {h}) w y := by
        rcases hpql.eq_and_eq_or_eq_and_eq hhl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hbr'
        · exact hbr'.symm'
      have hwR : w ∈ R := hXR w ih.1
      have hSw : Reach H (S ∩ Ins H R) w y := by
        by_contra hnr
        refine hbr h hhK w y hhl ((hR w).1 hwR) ?_ hwy
        rwa [hRset]
      have hyX : y ∈ X := (hX y).2 (((hX w).1 ih.1).trans' hSw)
      exact ⟨hyX, ih.2.trans' (reach_of_isLink ⟨⟨hhK, mem_ins_of_link hhl ih.1 hyX⟩, hhg⟩ hhl)⟩
  exact key b hNg


end Lax630294Proofs.ProtectedExt
