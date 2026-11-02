import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card

/-!
# Edge count of a finite forest

`|E(A)| + #components(A) = |V|` for a finite acyclic simple graph `A`.
(Not in Mathlib; needed for the tree completions of an `M`-witness.)
-/

namespace Lax630294Proofs.MSufficiencyForest

open SimpleGraph

variable {V : Type*}

-- DEVIATION (auxiliary, not in the paper): Mathlib has no edge count for forests; the paper uses
-- "a spanning tree has n-1 edges / the number of components of a forest" implicitly.  We prove
-- |E(A)| + #components(A) = |V| for finite acyclic simple graphs (by induction on the edges).

lemma reachable_sup_edge {G : SimpleGraph V} {u v x y : V} (h : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨ (G.Reachable x u ∧ G.Reachable v y) ∨ (G.Reachable x v ∧ G.Reachable u y) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (Reachable.refl _)
  | tail _ hbc ih =>
    rename_i b c
    rw [sup_adj, edge_adj] at hbc
    rcases hbc with hbc | ⟨⟨hb, hc⟩ | ⟨hb, hc⟩, hne⟩
    · have hr := hbc.reachable
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h1.trans hr)
      · exact Or.inr (Or.inl ⟨h1, h2.trans hr⟩)
      · exact Or.inr (Or.inr ⟨h1, h2.trans hr⟩)
    · subst hb; subst hc
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, Reachable.refl _⟩)
      · exact Or.inl (h1.trans h2.symm)
      · exact Or.inl h1
    · subst hb; subst hc
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨h1, Reachable.refl _⟩)
      · exact Or.inl h1
      · exact Or.inl (h1.trans h2.symm)
lemma card_cc_sup_edge [Finite V] {G : SimpleGraph V} {u v : V} (huv : ¬ G.Reachable u v) :
    Nat.card (G ⊔ edge u v).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  have hne : u ≠ v := fun h => huv (h ▸ Reachable.refl _)
  have hle : G ≤ G ⊔ edge u v := le_sup_left
  let f : G.ConnectedComponent → (G ⊔ edge u v).ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE hle)
  have hf : ∀ x, f (G.connectedComponentMk x) = (G ⊔ edge u v).connectedComponentMk x := fun x => rfl
  have hsurj : Function.Surjective f := ConnectedComponent.surjective_map_ofLE hle
  let c0 : G.ConnectedComponent := G.connectedComponentMk v
  let g : {c : G.ConnectedComponent // c ≠ c0} → (G ⊔ edge u v).ConnectedComponent :=
    fun c => f c.1
  have ginj : Function.Injective g := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ hcc
    induction c using ConnectedComponent.ind with | h a =>
    induction c' using ConnectedComponent.ind with | h b =>
    simp only [g, hf] at hcc
    have hr := ConnectedComponent.exact hcc
    rcases reachable_sup_edge hr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (ConnectedComponent.sound h)
    · exact absurd (ConnectedComponent.sound h2.symm) hc'
    · exact absurd (ConnectedComponent.sound h1) hc
  have gsurj : Function.Surjective g := by
    intro d
    obtain ⟨c, rfl⟩ := hsurj d
    by_cases hc : c = c0
    · subst hc
      refine ⟨⟨G.connectedComponentMk u, ?_⟩, ?_⟩
      · intro h; exact huv (ConnectedComponent.exact h)
      · simp only [g, hf, c0]
        apply ConnectedComponent.sound
        exact ((sup_adj _ _ _ _).2 (Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))).reachable
    · exact ⟨⟨c, hc⟩, rfl⟩
  classical
  have := Fintype.ofFinite G.ConnectedComponent
  have := Fintype.ofFinite (G ⊔ edge u v).ConnectedComponent
  have h1 : Nat.card {c : G.ConnectedComponent // c ≠ c0} = Nat.card (G ⊔ edge u v).ConnectedComponent :=
    Nat.card_congr (Equiv.ofBijective g ⟨ginj, gsurj⟩)
  rw [← h1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := Fintype.card_subtype_compl (fun c : G.ConnectedComponent => c = c0)
  have h2 := Fintype.card_subtype_eq c0
  simp only [ne_eq]
  rw [this, h2]
  have : 0 < Fintype.card G.ConnectedComponent := Fintype.card_pos_iff.2 ⟨c0⟩
  omega

lemma ncard_edgeSet_add_card_cc [Finite V] :
    ∀ (n : ℕ) (A : SimpleGraph V), A.IsAcyclic → A.edgeSet.ncard = n →
      A.edgeSet.ncard + Nat.card A.ConnectedComponent = Nat.card V := by
  intro n
  induction n with
  | zero =>
    intro A _ hn
    have hA : A = ⊥ := by
      rw [← edgeSet_eq_empty]
      exact (Set.ncard_eq_zero (Set.toFinite _)).1 hn
    subst hA
    rw [hn]
    have hb : Function.Bijective (fun x : V => (⊥ : SimpleGraph V).connectedComponentMk x) := by
      refine ⟨fun a b h => ?_, ConnectedComponent.ind (fun x => ⟨x, rfl⟩)⟩
      exact reachable_bot.1 (ConnectedComponent.exact h)
    rw [zero_add]
    exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm
  | succ n ih =>
    intro A hA hn
    have hne : A.edgeSet.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h] at hn
      simp at hn
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with | h u v =>
    have hadj : A.Adj u v := he
    set A' := A.deleteEdges {s(u, v)} with hA'
    have hbr : ¬ A'.Reachable u v := isAcyclic_iff_forall_adj_isBridge.1 hA hadj
    have hA'le : A' ≤ A := deleteEdges_le _
    have hsup : A = A' ⊔ edge u v := by
      ext x y
      simp only [hA', sup_adj, deleteEdges_adj, edge_adj, Set.mem_singleton_iff]
      constructor
      · intro h
        by_cases hxy : s(x, y) = s(u, v)
        · right
          rw [Sym2.eq_iff] at hxy
          exact ⟨hxy, h.ne⟩
        · exact Or.inl ⟨h, hxy⟩
      · rintro (⟨h, -⟩ | ⟨h | h, -⟩)
        · exact h
        · obtain ⟨rfl, rfl⟩ := h; exact hadj
        · obtain ⟨rfl, rfl⟩ := h; exact hadj.symm
    have hA'ac : A'.IsAcyclic := hA.anti hA'le
    have hnadj : s(u, v) ∉ A'.edgeSet := by
      rw [edgeSet_deleteEdges]; simp
    have hes : A.edgeSet = insert s(u, v) A'.edgeSet := by
      rw [hA', edgeSet_deleteEdges, Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
    have hcard : A.edgeSet.ncard = A'.edgeSet.ncard + 1 := by
      rw [hes, Set.ncard_insert_of_notMem hnadj]
    have hcc : Nat.card A.ConnectedComponent + 1 = Nat.card A'.ConnectedComponent := by
      have := card_cc_sup_edge hbr
      rwa [← hsup] at this
    have := ih A' hA'ac (by omega)
    omega

theorem ncard_edgeSet_add_card_cc' [Finite V] (A : SimpleGraph V) (hA : A.IsAcyclic) :
    A.edgeSet.ncard + Nat.card A.ConnectedComponent = Nat.card V :=
  ncard_edgeSet_add_card_cc _ A hA rfl

end Lax630294Proofs.MSufficiencyForest