import Lax630294Proofs.PortsSink

/-!
# The compatible four-cycle (`lem:characterization-compatible-actual-cycle`)

Final assembly of the port selection: from an edge `g = U0 U1` of `Y` with arcs in both
directions and root indices `0`, `1`, we obtain the four blocks `x0, U0, U1, x1`, the four cycle
edges `f0, g, f1, e`, their ports, and the local lifting condition (`LocalCond`) in each of the four
blocks, in exactly the form hypothesised by `Quotient2MLift.m_lift4`.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- A function on `ZMod 4` given by its four values. -/
def four {γ : Type*} (a b c d : γ) : ZMod 4 → γ := fun i =>
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

section four

variable {γ : Type*} {a b c d : γ}

lemma zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

lemma four_0 : four a b c d 0 = a := by
  unfold four; rw [if_pos rfl]

lemma four_1 : four a b c d 1 = b := by
  unfold four; rw [if_neg (show ¬ ((1 : ZMod 4) = 0) by decide), if_pos rfl]

lemma four_2 : four a b c d 2 = c := by
  unfold four
  rw [if_neg (show ¬ ((2 : ZMod 4) = 0) by decide), if_neg (show ¬ ((2 : ZMod 4) = 1) by decide),
    if_pos rfl]

lemma four_3 : four a b c d 3 = d := by
  unfold four
  rw [if_neg (show ¬ ((3 : ZMod 4) = 0) by decide), if_neg (show ¬ ((3 : ZMod 4) = 1) by decide),
    if_neg (show ¬ ((3 : ZMod 4) = 2) by decide)]

lemma four_injective (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d) (h12 : b ≠ c) (h13 : b ≠ d)
    (h23 : c ≠ d) : Function.Injective (four a b c d) := by
  intro i j hij
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [four_0, four_1, four_2, four_3] at hij <;>
    first
    | rfl
    | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h03
    | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h23
    | exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h03
    | exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h23

lemma succ_0 : (0 : ZMod 4) + 1 = 1 := by decide
lemma succ_1 : (1 : ZMod 4) + 1 = 2 := by decide
lemma succ_2 : (2 : ZMod 4) + 1 = 3 := by decide
lemma succ_3 : (3 : ZMod 4) + 1 = 0 := by decide

end four

/-- Two ports of an external call are its two ends. -/
lemma link_of_ports (hV : V(G).Finite) (hE : E(G).Finite) {d : β} {A B : Set α}
    (hAB : (quotient G).IsLink d A B) {a b : α} (ha : IsPort G A d a) (hb : IsPort G B d b) :
    G.IsLink d a b := by
  obtain ⟨x, y, hl, hx, hy, hne⟩ := quotient_isLink.1 hAB
  have hAV : A ∈ V(quotient G) := hAB.left_mem
  have hBV : B ∈ V(quotient G) := hAB.right_mem
  have haA : blk G a = A := blk_of_mem hV hE hAV ha.1
  have hbB : blk G b = B := blk_of_mem hV hE hBV hb.1
  rcases ha.2.eq_or_eq_of_isLink hl with h1 | h1 <;>
    rcases hb.2.eq_or_eq_of_isLink hl with h2 | h2
  · exfalso; apply hne; rw [← haA, ← hbB, h1, h2]
  · rw [h1, h2]; exact hl
  · rw [h1, h2]; exact hl.symm
  · exfalso; apply hne; rw [← haA, ← hbB, h1, h2]

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

omit c in
lemma disj_below_above (U : Set α) (f : β) : Disjoint (Above G ℓ U f) (Below G ℓ U f) := by
  refine Set.disjoint_left.2 fun d hA hB => ?_
  exact causal_irrefl f (causal_trans (hA.2.1 f rfl) (hB.2.2 f rfl))

/-- Local lifting property at a root block. -/
theorem lc_root (i : Bool) {f : β} (hg : Good G ℓ e (rootOf x0 x1 i) f) :
    ∃ a p, IsPort G (rootOf x0 x1 i) e a ∧ IsPort G (rootOf x0 x1 i) f p ∧
      LocalCond G (rootOf x0 x1 i) a p ∧ LocalCond G (rootOf x0 x1 i) p a := by
  obtain ⟨a, p, P, ha, hp, hPA, hpath, hcon⟩ := hg
  have hr := rootOf_or x0 x1 i
  have hconn : ∀ x ∈ rootOf x0 x1 i, ∀ y ∈ rootOf x0 x1 i,
      Reach G (Below G ℓ (rootOf x0 x1 i) e) x y := fun x hx y hy =>
    (c.tc_below hr (rootOf_or x0 x1 (!i)) (rootOf_ne c.ne01 i) ha x hx).trans'
      (c.tc_below hr (rootOf_or x0 x1 (!i)) (rootOf_ne c.ne01 i) ha y hy).symm'
  refine ⟨a, p, ha, hp, ?_, ?_⟩
  · exact threshold (PCtx.disj_below_above _ e) Set.inter_subset_left Set.inter_subset_left hconn
      hpath hPA hcon
  · exact threshold (PCtx.disj_below_above _ e) Set.inter_subset_left Set.inter_subset_left hconn
      hpath.symm hPA hcon

/-- Local lifting property at a vertex of `Y`. -/
theorem lc_Y {U r : Set α} (hU : U ∈ Y) (hr : r = x0 ∨ r = x1) {f h : β}
    (hf : f ∈ E(quotient G) \ I) (hfl : (quotient G).IsLink f U r) (hp : ArcPath G ℓ U h f) :
    ∃ pa pf, IsPort G U h pa ∧ IsPort G U f pf ∧ LocalCond G U pa pf ∧ LocalCond G U pf pa := by
  obtain ⟨pa, pf, P, hpa, hpf, hpath, hPB, hcon⟩ := hp
  have hconn : ∀ x ∈ U, ∀ y ∈ U, Reach G (Above G ℓ U f) x y := fun x hx y hy =>
    (c.tc_future hU hr hf hfl hpf x hx).symm'.trans' (c.tc_future hU hr hf hfl hpf y hy)
  refine ⟨pa, pf, hpa, hpf, ?_, ?_⟩
  · exact threshold (PCtx.disj_below_above U f).symm Set.inter_subset_left Set.inter_subset_left
      hconn hpath hPB hcon
  · exact threshold (PCtx.disj_below_above U f).symm Set.inter_subset_left Set.inter_subset_left
      hconn hpath.symm hPB hcon

end PCtx

end Lax630294Proofs.Ports
