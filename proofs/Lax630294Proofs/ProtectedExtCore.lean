import Lax630294Proofs.QuotientExchange
import Lax630294Proofs.CallOrderMain

/-!
# Protected extension: the class of protected trees and its basic lemmas

Setting of `lem:characterization-protected-extension` (paper l. 4744-4813), stated for an abstract
finite loopless graph `H`.  We fix vertices `x0 x1 u0` ("anchors"; `u1` is a neighbour of `u0`
through the edge `g`) and edges `e = x0x1`, `f0 = x0u0`, `f1 = x1u1`, `g = u0u1`.

The paper minimises the number of components of the complement `K = E(H) \ S` of a spanning tree
`S` among trees that keep `e, f0, f1` ("protected") and keep the three distinguished tree
components of `K` (those of the original `A0, A1, Y`) separate while every other component is
unicyclic.  We encode this as the class `Cls` below.

* `S` is a spanning tree containing `e, f0, f1`, `g ∈ E(H) \ S`;
* the anchors `x0, x1, u0` lie in three different components of `K`;
* every component of `K` containing none of the anchors has at least as many edges as vertices
  (it is not a tree).

The revised paper minimises over spanning trees containing `e, f0, f1` but not `g`, whose
complements have three distinct tree components containing `x0, x1, u0` and all other components
unicyclic.  The class `Cls` states this in the equivalent form "three different anchored components,
every other component is not a tree"; `special_comps` below shows that, under the global edge count
`|E(H)| = 2|V(H)| - 4` (i.e. `|K| + 3 = |V(H)|`), `Cls` implies the paper's exact invariant (the three
anchored components are trees and all other components are unicyclic), and conversely the paper's
invariant trivially gives the inequality kept in `Cls` (a unicyclic component has as many edges as
vertices).  The weaker form is easier to preserve in the exchange step.
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β}

/-- The class of protected trees (see the module docstring). -/
structure Cls (H : Graph α β) (x0 x1 u0 : α) (e f0 f1 g : β) (S : Set β) : Prop where
  tree : IsSpanningTree H S
  he : e ∈ S
  hf0 : f0 ∈ S
  hf1 : f1 ∈ S
  hgE : g ∈ E(H)
  hgS : g ∉ S
  d01 : ¬ Reach H (E(H) \ S) x0 x1
  d0u : ¬ Reach H (E(H) \ S) x0 u0
  d1u : ¬ Reach H (E(H) \ S) x1 u0
  inv : ∀ A, CallOrder.IsComp H (E(H) \ S) A → x0 ∉ A → x1 ∉ A → u0 ∉ A →
    A.ncard ≤ (CallOrder.edgesIn H (E(H) \ S) A).ncard

/-- In the class, the paper's invariant holds (global edge count `|K| + 3 = |V|`): the components
of the three anchors are trees and every other component is unicyclic. Conversely this invariant
implies the inequality in `Cls` (a unicyclic component has as many edges as vertices), so the
class `Cls` used here and the paper's class of trees are equivalent for the graphs at hand. -/
lemma special_comps (hV : V(H).Finite) (hE : E(H).Finite) {K : Set β} (hK : K ⊆ E(H))
    {x0 x1 u0 : α} (hx0 : x0 ∈ V(H)) (hx1 : x1 ∈ V(H)) (hu0 : u0 ∈ V(H))
    (h01 : ¬ Reach H K x0 x1) (h0u : ¬ Reach H K x0 u0) (h1u : ¬ Reach H K x1 u0)
    (hcard : K.ncard + 3 = V(H).ncard)
    (hinv : ∀ A, CallOrder.IsComp H K A → x0 ∉ A → x1 ∉ A → u0 ∉ A →
      A.ncard ≤ (CallOrder.edgesIn H K A).ncard) :
    ∀ A, CallOrder.IsComp H K A →
      ((x0 ∈ A ∨ x1 ∈ A ∨ u0 ∈ A) → CallOrder.IsTreeComp H K A) ∧
      (x0 ∉ A → x1 ∉ A → u0 ∉ A → CallOrder.IsUnicyclicComp H K A) := by
  classical
  set C := CallOrder.comps hV K with hC
  set A0 : Set α := {y | CallOrder.Conn H K x0 y} with hA0
  set A1 : Set α := {y | CallOrder.Conn H K x1 y} with hA1
  set A2 : Set α := {y | CallOrder.Conn H K u0 y} with hA2
  have c0 : CallOrder.IsComp H K A0 := CallOrder.isComp_comp hx0
  have c1 : CallOrder.IsComp H K A1 := CallOrder.isComp_comp hx1
  have c2 : CallOrder.IsComp H K A2 := CallOrder.isComp_comp hu0
  have m0 : x0 ∈ A0 := CallOrder.Conn.refl x0
  have m1 : x1 ∈ A1 := CallOrder.Conn.refl x1
  have m2 : u0 ∈ A2 := CallOrder.Conn.refl u0
  have n01 : A0 ≠ A1 := fun h => h01 (show x1 ∈ A0 from h ▸ m1)
  have n02 : A0 ≠ A2 := fun h => h0u (show u0 ∈ A0 from h ▸ m2)
  have n12 : A1 ≠ A2 := fun h => h1u (show u0 ∈ A1 from h ▸ m2)
  let T3 : Finset (Set α) := {A0, A1, A2}
  have hT3card : T3.card = 3 := Finset.card_eq_three.2 ⟨A0, A1, A2, n01, n02, n12, rfl⟩
  have hT3C : T3 ⊆ C := by
    intro A hA
    simp only [T3, Finset.mem_insert, Finset.mem_singleton] at hA
    rw [hC, CallOrder.mem_comps hV]
    rcases hA with rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2
  have hsum := CallOrder.sum_excess hV hE hK
  rw [← hC] at hsum
  have hge : ∀ A ∈ C \ T3, 1 ≤ CallOrder.excess H K A := by
    intro A hA
    rw [Finset.mem_sdiff] at hA
    have hAc : CallOrder.IsComp H K A := (CallOrder.mem_comps hV).1 hA.1
    have hx0A : x0 ∉ A := fun h =>
      hA.2 (by simp [T3, hAc.eq_of_mem c0 h m0])
    have hx1A : x1 ∉ A := fun h =>
      hA.2 (by simp [T3, hAc.eq_of_mem c1 h m1])
    have hu0A : u0 ∉ A := fun h =>
      hA.2 (by simp [T3, hAc.eq_of_mem c2 h m2])
    have := hinv A hAc hx0A hx1A hu0A
    unfold CallOrder.excess
    omega
  have h1 : (C \ T3).card • 1 ≤ ∑ A ∈ C \ T3, CallOrder.excess H K A :=
    Finset.card_nsmul_le_sum _ _ _ hge
  have h2 := Finset.sum_sdiff (f := CallOrder.excess H K) hT3C
  have h3 : (C \ T3).card = C.card - 3 := by
    rw [Finset.card_sdiff_of_subset hT3C, hT3card]
  have h4 : 3 ≤ C.card := hT3card ▸ Finset.card_le_card hT3C
  have h5 : ∑ A ∈ T3, CallOrder.excess H K A = 0 := by
    simp only [smul_eq_mul, mul_one] at h1
    omega
  have h6 : ∀ A ∈ T3, CallOrder.excess H K A = 0 := Finset.sum_eq_zero_iff.1 h5
  have h7 : ∑ A ∈ C \ T3, CallOrder.excess H K A = C.card - 3 := by omega
  have h8 : ∀ A ∈ C \ T3, CallOrder.excess H K A = 1 := by
    intro A hA
    by_contra hne
    have h2A : 2 ≤ CallOrder.excess H K A := by have := hge A hA; omega
    have hlt := Finset.sum_lt_sum (s := C \ T3) (f := fun _ => 1) (g := CallOrder.excess H K)
      (fun B hB => hge B hB) ⟨A, hA, by omega⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt
    omega
  intro A hA
  refine ⟨fun hspec => ?_, fun hx0A hx1A hu0A => ?_⟩
  · have hAT : A ∈ T3 := by
      simp only [T3, Finset.mem_insert, Finset.mem_singleton]
      rcases hspec with h | h | h
      · exact Or.inl (hA.eq_of_mem c0 h m0)
      · exact Or.inr (Or.inl (hA.eq_of_mem c1 h m1))
      · exact Or.inr (Or.inr (hA.eq_of_mem c2 h m2))
    exact (CallOrder.isTreeComp_iff hV hE hA).2 (h6 A hAT)
  · have hAC : A ∈ C := (CallOrder.mem_comps hV).2 hA
    have hAn : A ∉ T3 := by
      intro hAT
      simp only [T3, Finset.mem_insert, Finset.mem_singleton] at hAT
      rcases hAT with rfl | rfl | rfl
      · exact hx0A m0
      · exact hx1A m1
      · exact hu0A m2
    have := h8 A (Finset.mem_sdiff.2 ⟨hAC, hAn⟩)
    unfold CallOrder.excess at this
    refine ⟨hA, ?_⟩
    omega

/-- In the class, the components of the anchors are trees (global edge count). -/
lemma special_tree (hV : V(H).Finite) (hE : E(H).Finite) {K : Set β} (hK : K ⊆ E(H))
    {x0 x1 u0 : α} (hx0 : x0 ∈ V(H)) (hx1 : x1 ∈ V(H)) (hu0 : u0 ∈ V(H))
    (h01 : ¬ Reach H K x0 x1) (h0u : ¬ Reach H K x0 u0) (h1u : ¬ Reach H K x1 u0)
    (hcard : K.ncard + 3 = V(H).ncard)
    (hinv : ∀ A, CallOrder.IsComp H K A → x0 ∉ A → x1 ∉ A → u0 ∉ A →
      A.ncard ≤ (CallOrder.edgesIn H K A).ncard) :
    ∀ A, CallOrder.IsComp H K A → (x0 ∈ A ∨ x1 ∈ A ∨ u0 ∈ A) → CallOrder.IsTreeComp H K A :=
  fun A hA => (special_comps hV hE hK hx0 hx1 hu0 h01 h0u h1u hcard hinv A hA).1

end Lax630294Proofs.ProtectedExt
