import Lax630294Proofs.ThreePhase
import Lax630294.TGraph

namespace Lax630294Proofs.TSufficiency

open Graph Lax630294.Gossiping Lax630294.SpanningStructures Lax630294.TGraph
  Lax630294Proofs.Temporal Lax630294Proofs.ThreePhase

variable {α β : Type*} {G : Graph α β}

/-- A graph with at most one vertex is label-connected. -/
theorem subsingleton_sufficiency (h : V(G).Subsingleton) : IsLabelConnected G := by
  refine ⟨fun _ => 0, fun u hu v hv => ?_⟩
  obtain rfl : u = v := h hu hv
  exact (TW.nil u).hasTemporalPath

/-- The edges of a spanning tree connect all vertices. -/
lemma tree_connected {T : Set β} (h : IsSpanningTree G T) :
    ∀ x ∈ V(G), ∀ y ∈ V(G), Relation.ReflTransGen (step G T) x y := by
  intro x hx y hy
  have hr := h.2.2.connected.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  refine hr.lift Subtype.val (fun a b hab => ?_)
  obtain ⟨-, e, he, hl⟩ := hab
  exact ⟨e, he, hl⟩

/-- Deleting an edge `c = uv` from a connecting edge set leaves every vertex connected to
`u` or `v`. -/
lemma cut_connected {S : Set β} {c : β} {u v : α} (hc : c ∈ S) (hl : G.IsLink c u v)
    (hS : ∀ x ∈ V(G), ∀ y ∈ V(G), Relation.ReflTransGen (step G S) x y) :
    ∀ x ∈ V(G), ∃ r ∈ ({u, v} : Set α), Relation.ReflTransGen (step G (S \ {c})) x r := by
  intro x hx
  have h := hS x hx u hl.left_mem
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨u, by simp, .refl⟩
  | @head a b hab _ ih =>
    obtain ⟨e, he, hel⟩ := hab
    by_cases hec : e = c
    · subst hec
      refine ⟨a, ?_, .refl⟩
      rcases hel.left_eq_or_eq hl with h | h <;> simp [h]
    · obtain ⟨r, hr, hbr⟩ := ih hel.right_mem
      exact ⟨r, hr, .head ⟨e, ⟨he, hec⟩, hel⟩ hbr⟩

/-- A `T`-graph is label-connected. -/
theorem tGraph_sufficiency (hV : V(G).Finite) (h : IsTGraph G) : IsLabelConnected G := by
  obtain ⟨T1, T2, ht1, ht2, hcard⟩ := h
  have hc1 := tree_connected ht1
  have hc2 := tree_connected ht2
  by_cases hi : (T1 ∩ T2).Nonempty
  · obtain ⟨c, hc1', hc2'⟩ := hi
    have hsingle : ∀ f ∈ T1 ∩ T2, f = c := fun f hf =>
      Set.encard_le_one_iff.1 hcard f c hf ⟨hc1', hc2'⟩
    obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet (ht1.1 hc1')
    refine three_phase hV (T1 \ {c}) (T2 \ {c}) {c} {u, v} ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Set.disjoint_left]
      rintro f ⟨hf1, hf⟩ ⟨hf2, -⟩
      exact hf (hsingle f ⟨hf1, hf2⟩)
    · rw [Set.disjoint_left]
      rintro f ⟨-, hf⟩ hf'
      exact hf hf'
    · rw [Set.disjoint_left]
      rintro f ⟨-, hf⟩ hf'
      exact hf hf'
    · exact cut_connected hc1' hl hc1
    · intro y hy
      obtain ⟨r, hr, hry⟩ := cut_connected hc2' hl hc2 y hy
      exact ⟨r, hr, rtg_symm (fun a b h => step_symm h) hry⟩
    · intro r hr r' hr'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr hr'
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨c, rfl, hl⟩
      · exact Or.inr ⟨c, rfl, hl.symm⟩
      · exact Or.inl rfl
  · have hdisj : T1 ∩ T2 = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
    obtain ⟨⟨r0, hr0⟩⟩ := ht1.2.2.connected.nonempty
    refine three_phase hV T1 T2 ∅ {r0} ?_ (by simp) (by simp) ?_ ?_ ?_
    · exact Set.disjoint_iff_inter_eq_empty.2 hdisj
    · intro x hx
      exact ⟨r0, rfl, hc1 x hx r0 hr0⟩
    · intro y hy
      exact ⟨r0, rfl, hc2 r0 hr0 y hy⟩
    · intro r hr r' hr'
      simp only [Set.mem_singleton_iff] at hr hr'
      exact Or.inl (hr.trans hr'.symm)

end Lax630294Proofs.TSufficiency
