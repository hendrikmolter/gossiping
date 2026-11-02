import Lax630294Proofs.PortsReroute

/-!
# An edge with both orientations and different root indices
(first half of the proof of `lem:characterization-compatible-actual-cycle`)
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

/-- An adjacent pair `U0, U1` of vertices of a minimal closed set with root indices `0` and `1`
and arcs in both directions: the maximal-directed-path argument of the paper, applied to the
digraph `D` on `S` (`Arc`) inside the tree `Y[S]`. -/
theorem sink_edge {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {ci : Set α → Bool}
    {fi : Set α → β} (hd : AcsData G ℓ e I x0 x1 S ci fi) :
    ∃ U0 U1 g, U0 ∈ S ∧ U1 ∈ S ∧ ci U0 = false ∧ ci U1 = true ∧
      g ∈ edgesIn (quotient G) I S ∧ (quotient G).IsLink g U0 U1 ∧
      ArcPath G ℓ U0 g (fi U0) ∧ ArcPath G ℓ U1 g (fi U1) := by
  classical
  have := c.q.hA.simple
  have hSY : S ⊆ Y := hS.1.2.1
  have hSfin : S.Finite := (c.q.hA.finV.subset c.q.hY.1.2.1).subset hSY
  have hE1Y : edgesIn (quotient G) I S ⊆ edgesIn (quotient G) I Y :=
    fun d hd => ⟨hd.1, hd.2.mono hSY⟩
  have hacS : Acyc (quotient G) (edgesIn (quotient G) I S) := c.q.acyc_Y.mono hE1Y
  have hsink := sink_pair (arc := fun U V => U ∈ S ∧ Arc G ℓ e I x0 x1 S ci fi U V) (idx := ci)
    hacS hSfin (fun d hd => hd.2)
    (by
      intro a b hab
      refine ⟨hab.1, ?_⟩
      obtain ⟨h, hhS, hl, -⟩ := hab.2
      exact ⟨h, hhS, hl⟩)
    (by
      intro U hU
      obtain ⟨V, hV⟩ := c.arc_out hS hd hU
      exact ⟨V, hU, hV⟩)
    (by
      intro a b hab hci
      have hbS : b ∈ S := by
        obtain ⟨h, hhS, hl, -⟩ := hab.2
        exact (hhS.2.ends_mem hl).2
      obtain ⟨W, hWa, hW⟩ := c.reroute hS hd hab.1 hbS hci hab.2
      exact ⟨W, hWa, hbS, hW⟩)
    hS.1.1
  obtain ⟨U, V, hUV, hVU, hne⟩ := hsink
  obtain ⟨h1, hh1S, hh1l, -, hp1⟩ := hUV.2
  obtain ⟨h2, hh2S, hh2l, -, hp2⟩ := hVU.2
  have hh12 : h2 = h1 := hh2l.symm.eq hh1l
  rw [hh12] at hp2
  have hUS : U ∈ S := hUV.1
  have hVS : V ∈ S := hVU.1
  cases hcU : ci U
  · have hcV : ci V = true := by
      rw [hcU] at hne
      cases hcV' : ci V
      · exact absurd (by rw [hcV']) hne
      · rfl
    exact ⟨U, V, h1, hUS, hVS, hcU, hcV, hh1S, hh1l, hp1, hp2⟩
  · have hcV : ci V = false := by
      rw [hcU] at hne
      cases hcV' : ci V
      · rfl
      · exact absurd (by rw [hcV']) hne
    exact ⟨V, U, h1, hVS, hUS, hcV, hcU, hh1S, hh1l.symm, hp2, hp1⟩

end PCtx

end Lax630294Proofs.Ports
