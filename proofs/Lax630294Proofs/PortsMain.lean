import Lax630294Proofs.PortsFinal

/-!
# `lem:characterization-compatible-actual-cycle`: the main statement of the port selection
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- The conclusion of `lem:characterization-compatible-actual-cycle`: an edge `g = U0 U1` of `Y`
and future edges `f0 = x0 U0`, `f1 = x1 U1` of `Q = quotient G` such that the four-cycle
`x0, U0, U1, x1` (edges `f0, g, f1, e`) has the local lifting property in each of its four blocks,
with exactly the data hypothesised by `Quotient2MLift.m_lift4`. -/
abbrev CompatibleCycle (G : Graph α β) (I : Set β) (Y : Set (Set α)) (e : β) (x0 x1 : Set α) :
    Prop :=
  ∃ g f0 f1 U0 U1, g ∈ edgesIn (quotient G) I Y ∧ (quotient G).IsLink g U0 U1 ∧
    f0 ∈ E(quotient G) \ I ∧ (quotient G).IsLink f0 x0 U0 ∧
    f1 ∈ E(quotient G) \ I ∧ (quotient G).IsLink f1 x1 U1 ∧
    ∃ (U : ZMod 4 → Set α) (d : ZMod 4 → β) (p q : ZMod 4 → α),
      U 0 = x0 ∧ U 1 = U0 ∧ U 2 = U1 ∧ U 3 = x1 ∧ d 0 = f0 ∧ d 1 = g ∧ d 2 = f1 ∧ d 3 = e ∧
      Function.Injective U ∧ Function.Injective d ∧
      (∀ i, (quotient G).IsLink (d i) (U i) (U (i + 1))) ∧
      (∀ i, G.IsLink (d i) (q i) (p (i + 1))) ∧ (∀ i, q i ∈ U i) ∧ (∀ i, p i ∈ U i) ∧
      (∀ i, LocalCond G (U i) (p i) (q i))

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

/-- **Compatible four-cycle** (`lem:characterization-compatible-actual-cycle`).  There is an edge
`g = U0 U1` of `Y` and future edges `f0 = x0 U0`, `f1 = x1 U1` such that the four-cycle
`x0, U0, U1, x1` has the local lifting property in each of its four blocks, in the form hypothesised
by `Quotient2MLift.m_lift4`. -/
theorem compatible_actual_cycle : CompatibleCycle G I Y e x0 x1 := by
  classical
  have := c.q.hA.simple
  obtain ⟨S, hS⟩ := c.exists_minClosed
  obtain ⟨ci, fi, hd⟩ := c.exists_acsData hS
  obtain ⟨U0, U1, g, hU0, hU1, hc0, hc1, hgS, hgl, hp0, hp1⟩ := c.sink_edge hS hd
  have hSY := hS.1.2.1
  have hU0Y : U0 ∈ Y := hSY hU0
  have hU1Y : U1 ∈ Y := hSY hU1
  obtain ⟨hf0F, hf0l, hf0g⟩ := hd.fut U0 hU0
  obtain ⟨hf1F, hf1l, hf1g⟩ := hd.fut U1 hU1
  rw [hc0] at hf0l hf0g
  rw [hc1] at hf1l hf1g
  have hf0l' : (quotient G).IsLink (fi U0) U0 x0 := hf0l
  have hf1l' : (quotient G).IsLink (fi U1) U1 x1 := hf1l
  have hf0g' : Good G ℓ e (rootOf x0 x1 false) (fi U0) := hf0g
  have hf1g' : Good G ℓ e (rootOf x0 x1 true) (fi U1) := hf1g
  obtain ⟨a0, p0', ha0, hp0', hLC0, -⟩ := c.lc_root false hf0g'
  obtain ⟨a1, p1', ha1, hp1', -, hLC3⟩ := c.lc_root true hf1g'
  have ha0' : IsPort G x0 e a0 := ha0
  have hp0'' : IsPort G x0 (fi U0) p0' := hp0'
  have ha1' : IsPort G x1 e a1 := ha1
  have hp1'' : IsPort G x1 (fi U1) p1' := hp1'
  have hLC0' : LocalCond G x0 a0 p0' := hLC0
  have hLC3' : LocalCond G x1 p1' a1 := hLC3
  obtain ⟨pg, pf, hpg, hpf, -, hLC1⟩ := c.lc_Y hU0Y (Or.inl rfl) hf0F hf0l' hp0
  obtain ⟨pg', pf', hpg', hpf', hLC2, -⟩ := c.lc_Y hU1Y (Or.inr rfl) hf1F hf1l' hp1
  -- distinctness
  have hx0X := c.q.x0_mem
  have hx1X := c.q.x1_mem
  have hn0 : x0 ≠ U0 := fun h => c.q.mem_Y_not_X hU0Y (h ▸ hx0X)
  have hn1 : x0 ≠ U1 := fun h => c.q.mem_Y_not_X hU1Y (h ▸ hx0X)
  have hn2 : U0 ≠ x1 := fun h => c.q.mem_Y_not_X hU0Y (h ▸ hx1X)
  have hn3 : U1 ≠ x1 := fun h => c.q.mem_Y_not_X hU1Y (h ▸ hx1X)
  have hn4 : U0 ≠ U1 := hgl.ne
  have hgI : g ∈ I := hgS.1
  have heI : e ∈ I := c.q.hC.e_mem.1
  have hd01 : fi U0 ≠ g := fun h => hf0F.2 (h ▸ hgI)
  have hd03 : fi U0 ≠ e := fun h => hf0F.2 (h ▸ heI)
  have hd12 : g ≠ fi U1 := fun h => hf1F.2 (h ▸ hgI)
  have hd23 : fi U1 ≠ e := fun h => hf1F.2 (h ▸ heI)
  have hd02 : fi U0 ≠ fi U1 := by
    intro h
    rw [h] at hf0l'
    rcases hf0l'.eq_and_eq_or_eq_and_eq hf1l'.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hn2 h1
    · exact hn4 h1
  have hd13 : g ≠ e := by
    intro h
    rw [h] at hgl
    rcases hgl.eq_and_eq_or_eq_and_eq c.q.hC.e_link with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hn0 h1.symm
    · exact hn2 h1
  refine ⟨g, fi U0, fi U1, U0, U1, ⟨hgS.1, hgS.2.mono hSY⟩, hgl, hf0F, hf0l'.symm, hf1F,
    hf1l'.symm, four x0 U0 U1 x1, four (fi U0) g (fi U1) e, four a0 pf pg' p1',
    four p0' pg pf' a1, four_0, four_1, four_2, four_3, four_0, four_1, four_2, four_3,
    four_injective hn0 hn1 c.q.ne01 hn4 hn2 hn3,
    four_injective hd01 hd02 hd03 hd12 hd13 hd23, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [succ_0, four_0, four_0, four_1]; exact hf0l'.symm
    · rw [succ_1, four_1, four_1, four_2]; exact hgl
    · rw [succ_2, four_2, four_2, four_3]; exact hf1l'.symm.symm
    · rw [succ_3, four_3, four_3, four_0]; exact c.q.hC.e_link.symm
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [succ_0, four_0, four_0, four_1]
      exact link_of_ports c.hV c.hE hf0l'.symm hp0'' hpf
    · rw [succ_1, four_1, four_1, four_2]
      exact link_of_ports c.hV c.hE hgl hpg hpg'
    · rw [succ_2, four_2, four_2, four_3]
      exact link_of_ports c.hV c.hE hf1l' hpf' hp1''
    · rw [succ_3, four_3, four_3, four_0]
      exact link_of_ports c.hV c.hE c.q.hC.e_link.symm ha1' ha0'
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [four_0, four_0]; exact hp0''.1
    · rw [four_1, four_1]; exact hpg.1
    · rw [four_2, four_2]; exact hpf'.1
    · rw [four_3, four_3]; exact ha1'.1
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [four_0, four_0]; exact ha0'.1
    · rw [four_1, four_1]; exact hpf.1
    · rw [four_2, four_2]; exact hpg'.1
    · rw [four_3, four_3]; exact hp1''.1
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [four_0, four_0, four_0]; exact hLC0'
    · rw [four_1, four_1, four_1]; exact hLC1
    · rw [four_2, four_2, four_2]; exact hLC2
    · rw [four_3, four_3, four_3]; exact hLC3'

end PCtx

end Lax630294Proofs.Ports
