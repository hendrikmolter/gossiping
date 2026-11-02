import Lax630294Proofs.SmallCases
import Lax630294Proofs.Quotient2MLift
import Lax630294Proofs.PortsStanding
import Lax630294Proofs.ProtectedExtFinal
import Lax630294Proofs.CausalQuotient
import Lax630294Proofs.CallOrderMain
import Lax630294Proofs.QuotientExchange

namespace Lax630294Proofs.Necessity

open Graph Lax630294.Gossiping Lax630294.SpanningStructures Lax630294.TGraph Lax630294.MGraph
  Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.QuotientExchange Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift
  Lax630294Proofs.CausalQuotient Lax630294Proofs.Ports Lax630294Proofs.NecessityPrelim
  Lax630294Proofs.CallOrder Lax630294Proofs.SmallCases Lax630294Proofs.QuotientDef
  Lax630294Proofs.QuotientBlocks Lax630294Proofs.Causal

variable {α β : Type*} {G : Graph α β}

/-- The necessity direction: a label-connected finite multigraph has at most one vertex, is a
`T`-graph, or is an `M`-graph. -/
theorem necessity (hV : V(G).Finite) (hE : E(G).Finite) (h : IsLabelConnected G) :
    V(G).Subsingleton ∨ IsTGraph G ∨ IsMGraph G := by
  classical
  by_cases hs : V(G).Subsingleton
  · exact Or.inl hs
  right
  obtain ⟨ℓ0, hℓ0⟩ := h
  obtain ⟨ℓ, hinj, hℓ⟩ := tie_break hE hℓ0
  have hconn := connected_of_complete hℓ
  obtain ⟨hVQ, hEQ⟩ := quotient_finite hV hE
  have hQs := quotient_simple hV hE
  have hno : ∀ X ⊆ V(quotient G), 2 ≤ X.ncard → ¬ IsTwoTreeSet (quotient G) X :=
    fun X hX h2 => quotient_no_twoTree hV hE hX h2
  have hQconn := quotient_connected hconn
  have hloop : ∀ e x, ¬ (quotient G).IsLink e x x := fun e x => quotient_loopless e x
  have hA := admissible hV hE hQs hℓ
  have hVne : V(quotient G).Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hs
    exact ⟨blk G x, x, hx, rfl⟩
  have hr1 : 1 ≤ V(quotient G).ncard := (Set.ncard_pos hVQ).2 hVne
  by_cases hr1' : V(quotient G).ncard = 1
  · obtain ⟨T₁, T₂, h1, h2, hd⟩ := one_vertex hV hE hr1'
    exact Or.inl ⟨T₁, T₂, h1, h2, by rw [Set.disjoint_iff_inter_eq_empty.1 hd]; simp⟩
  have hr2 : 2 ≤ V(quotient G).ncard := by omega
  have hbound := edges_add_three_le hVQ hEQ hloop hno hr2 hQconn
  by_cases hr4 : 4 ≤ V(quotient G).ncard
  · have hlow := hA.lower_bound hr4
    by_cases hcard : E(quotient G).ncard = 2 * V(quotient G).ncard - 4
    · -- the equality case: build an M-witness
      by_cases hT : IsTGraph G
      · exact Or.inl hT
      right
      refine ⟨?_, hT⟩
      obtain ⟨I, X, Y, e, x0, x1, hC, hY, hYX, hall, hcyc⟩ := port_selection hV hE hℓ hr4 hcard
      obtain ⟨g, f0, f1, U0, U1, hg, hgl, hf0, hf0l, hf1, hf1l, U, d, p, q, hU0, hU1, hU2, hU3,
        hd0, hd1, hd2, hd3, hUinj, hdinj, hdl, hport, hq, hp, hloc⟩ := hcyc
      obtain ⟨Y', hY', hY'X, hall', hcl, hmin, hunic'⟩ :=
        hA.early_components hr4 hcard hC.ideal hC.card_I hC.tree hC.cross
      have hY'Y : Y' = Y := (hall Y' hY').resolve_left hY'X
      have hunic : ∀ D, IsComp (quotient G) I D → D ≠ X → D ≠ Y →
          IsUnicyclicComp (quotient G) I D := by
        intro D hD hDX hDY
        exact hunic' D hD hDX (hY'Y ▸ hDY)
      obtain ⟨L₁, L₂, hM, -⟩ := ProtectedExt.protected_extension hA hr4 hcard hno hC hY hYX hunic
        hg hgl hf0 hf0l hf1 hf1l
      have hD : Set.range d = {e, g, f0, f1} := by
        ext z
        simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · have hcases : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
          rintro ⟨i, rfl⟩
          rcases hcases i with rfl | rfl | rfl | rfl <;> simp [hd0, hd1, hd2, hd3]
        · intro hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact ⟨3, hd3⟩
          · exact ⟨1, hd1⟩
          · exact ⟨0, hd0⟩
          · exact ⟨2, hd2⟩
      exact m_lift4 hV hE hM U d p q hUinj hdinj hD hdl hport hq hp hloc
    · -- |E(Q)| = 2r - 3
      refine Or.inl (tCase hV hE hconn hr2 ?_)
      omega
  · -- r = 2 or r = 3
    by_cases hr2' : V(quotient G).ncard = 2
    · have := two_vertices_edge hVQ hEQ hr2' hQconn
      exact Or.inl (tCase hV hE hconn hr2 (by omega))
    · have hr3 : V(quotient G).ncard = 3 := by omega
      have hcQ : IsTemporallyConnected (quotient G) ℓ :=
        hA.complete ℓ (hinj.mono quotient_edgeSet_subset) (fun a b hab => Causal.causal_lt hab.2.2)
      have := three_vertices_edges hQs hVQ hEQ hr3 (hinj.mono quotient_edgeSet_subset) hcQ
      exact Or.inl (tCase hV hE hconn hr2 (by omega))

end Lax630294Proofs.Necessity
