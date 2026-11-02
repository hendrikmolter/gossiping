import Lax630294Proofs.QuotientDef

/-!
# Contraction along a family of internal forests

Generic lemmas on `contract G f`: if `I` is an edge set of `G` that is a forest, consists of edges
inside fibres of `f` and connects every fibre, then connectivity / component counts / spanning
trees and forests of `contract G f` correspond to those of `G` with `I` added
(`reach_contract_iff`, `comps_lift`, `lift_spanningTree`, `lift_spanningForest`).
For `f = blk G` the sets `I` are built from one pair of edge-disjoint spanning trees per block
(`exists_AB`).

DEVIATION (from the paper): the paper argues with "lift the quotient trees and add the internal
trees"; here this is one generic counting lemma (`Fib.card` + `rank_ineq`) used for all lifts.
-/

namespace Lax630294Proofs.Quotient2Contract

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs.QuotientBlocks
  Lax630294Proofs.QuotientDef

variable {α β γ : Type*} {G : Graph α β} {f : α → γ} {x y a b : α} {e : β} {F I : Set β}

lemma mem_edgeSet_contract : e ∈ E(contract G f) ↔ ∃ x y, G.IsLink e x y ∧ f x ≠ f y := by
  constructor
  · intro h; exact h.2
  · rintro ⟨x, y, hl, hne⟩; exact ⟨hl.edge_mem, x, y, hl, hne⟩

lemma contract_edgeSet_subset : E(contract G f) ⊆ E(G) := fun _ he => he.1

lemma contract_finite (hV : V(G).Finite) (hE : E(G).Finite) :
    V(contract G f).Finite ∧ E(contract G f).Finite :=
  ⟨hV.image f, hE.subset contract_edgeSet_subset⟩

lemma contract_ext {g : β} (hg : g ∈ E(contract G f)) {a b : α} (hl : G.IsLink g a b) :
    f a ≠ f b := by
  obtain ⟨x, y, hl', hne⟩ := mem_edgeSet_contract.1 hg
  rcases hl'.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne
  · exact fun h => hne h.symm

/-- `I` is a *fibre forest* for `f`: a forest of `G` consisting of edges inside fibres of `f` and
connecting every fibre. -/
structure Fib (G : Graph α β) (f : α → γ) (I : Set β) : Prop where
  subset : I ⊆ E(G)
  internal : ∀ e ∈ I, ∀ x y, G.IsLink e x y → f x = f y
  conn : ∀ x ∈ V(G), ∀ y ∈ V(G), f x = f y → Reach G I x y
  forest : IsForest G I

lemma Fib.disjoint_ext (h : Fib G f I) : Disjoint I E(contract G f) := by
  refine Set.disjoint_left.2 fun e he he' => ?_
  obtain ⟨x, y, hl, hne⟩ := mem_edgeSet_contract.1 he'
  exact hne (h.internal e he x y hl)

lemma reach_fiber (hI : ∀ e ∈ I, ∀ x y, G.IsLink e x y → f x = f y) (h : Reach G I x y) :
    f x = f y := by
  induction h with
  | refl => rfl
  | tail _ hs ih => obtain ⟨g, hg, hl⟩ := hs; exact ih.trans (hI g hg _ _ hl)

lemma reach_contract_of_reach (hF : F ⊆ E(contract G f))
    (hI : ∀ e ∈ I, ∀ x y, G.IsLink e x y → f x = f y) (h : Reach G (F ∪ I) x y) :
    Reach (contract G f) F (f x) (f y) := by
  induction h with
  | refl => exact reach_refl
  | @tail w z _ hs ih =>
    obtain ⟨g, hg, hl⟩ := hs
    rcases hg with hg | hg
    · refine ih.trans' (reach_of_isLink hg ?_)
      exact contract_isLink.2 ⟨w, z, hl, rfl, rfl, contract_ext (hF hg) hl⟩
    · rw [hI g hg w z hl] at ih; exact ih

lemma reach_of_reach_contract_aux
    (hconn : ∀ x ∈ V(G), ∀ y ∈ V(G), f x = f y → Reach G I x y) (hx : x ∈ V(G)) {W : γ}
    (h : Reach (contract G f) F (f x) W) :
    ∀ y ∈ V(G), f y = W → Reach G (F ∪ I) x y := by
  induction h with
  | refl => intro y hy hW; exact reach_mono Set.subset_union_right (hconn x hx y hy hW.symm)
  | @tail W' W _ hs ih =>
    intro y hy hW
    obtain ⟨g, hg, hl⟩ := hs
    obtain ⟨u, v, hlG, hu, hv, _⟩ := contract_isLink.1 hl
    have h1 := ih u hlG.left_mem hu
    have h2 : Reach G (F ∪ I) u v := reach_of_isLink (Set.mem_union_left _ hg) hlG
    have h3 : Reach G (F ∪ I) v y :=
      reach_mono Set.subset_union_right (hconn v hlG.right_mem y hy (hv.trans hW.symm))
    exact h1.trans' (h2.trans' h3)

lemma reach_of_reach_contract
    (hconn : ∀ x ∈ V(G), ∀ y ∈ V(G), f x = f y → Reach G I x y) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) (h : Reach (contract G f) F (f x) (f y)) : Reach G (F ∪ I) x y :=
  reach_of_reach_contract_aux hconn hx h y hy rfl

lemma reach_contract_iff (hI : Fib G f I) (hF : F ⊆ E(contract G f)) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : Reach (contract G f) F (f x) (f y) ↔ Reach G (F ∪ I) x y :=
  ⟨reach_of_reach_contract hI.conn hx hy, reach_contract_of_reach hF hI.internal⟩

/-- The component count of a fibre forest is the number of fibres. -/
lemma comps_fib (hI : Fib G f I) : comps G I = (f '' V(G)).ncard := by
  unfold comps
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun x : V(G) => (⟨f x, x, x.2, rfl⟩ : f '' V(G))) ?_) ⟨?_, ?_⟩)
  · intro x y h
    have h' : Reach G I x y := h
    have h2 : f x = f y := reach_fiber hI.internal h'
    exact Subtype.ext h2
  · intro c d
    induction c using Quotient.inductionOn with | _ c =>
    induction d using Quotient.inductionOn with | _ d =>
    intro h
    have h' : f c = f d := congrArg Subtype.val h
    exact Quotient.sound (hI.conn c c.2 d d.2 h')
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

lemma Fib.card (hI : Fib G f I) (hV : V(G).Finite) (hE : E(G).Finite) :
    I.ncard + (f '' V(G)).ncard = V(G).ncard := by
  have := forest_card hV hE hI.subset hI.forest
  rw [comps_fib hI] at this
  exact this

/-- Components of `F ∪ I` in `G` correspond to components of `F` in the contraction. -/
lemma comps_lift (hI : Fib G f I) (hF : F ⊆ E(contract G f)) :
    comps G (F ∪ I) = comps (contract G f) F := by
  unfold comps
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map (sa := reachSetoid G (F ∪ I)) (sb := reachSetoid (contract G f) F)
      (fun x : V(G) => (⟨f x, x, x.2, rfl⟩ : V(contract G f))) ?_) ⟨?_, ?_⟩)
  · intro x y h
    exact reach_contract_of_reach hF hI.internal h
  · intro c d
    induction c using Quotient.inductionOn with | _ c =>
    induction d using Quotient.inductionOn with | _ d =>
    intro h
    have h' : Reach (contract G f) F (f c) (f d) := Quotient.exact h
    exact Quotient.sound (reach_of_reach_contract hI.conn c.2 d.2 h')
  · intro c
    induction c using Quotient.inductionOn with | _ c =>
    obtain ⟨x, hx, h⟩ := c.2
    exact ⟨Quotient.mk _ ⟨x, hx⟩, congrArg (Quotient.mk _) (Subtype.ext h)⟩

theorem lift_spanningTree (hV : V(G).Finite) (hE : E(G).Finite) (hI : Fib G f I) {T : Set β}
    (hT : T ⊆ E(contract G f)) :
    IsSpanningTree (contract G f) T ↔ IsSpanningTree G (T ∪ I) := by
  obtain ⟨hVQ, hEQ⟩ := contract_finite (f := f) hV hE
  rw [isSpanningTree_iff hVQ hEQ, isSpanningTree_iff hV hE]
  have hdisj : Disjoint T I := (hI.disjoint_ext.symm).mono_left hT
  have hcard : (T ∪ I).ncard = T.ncard + I.ncard :=
    Set.ncard_union_eq hdisj (hEQ.subset hT) (hE.subset hI.subset)
  have hc := hI.card hV hE
  have hQ : V(contract G f).ncard = (f '' V(G)).ncard := rfl
  have hne : V(contract G f).Nonempty ↔ V(G).Nonempty := Set.image_nonempty
  constructor
  · rintro ⟨_, hn, hconn, hcn⟩
    refine ⟨Set.union_subset (hT.trans contract_edgeSet_subset) hI.subset, hne.1 hn, ?_, by omega⟩
    intro x hx y hy
    exact reach_of_reach_contract hI.conn hx hy (hconn _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  · rintro ⟨_, hn, hconn, hcn⟩
    refine ⟨hT, hne.2 hn, ?_, by omega⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact reach_contract_of_reach hT hI.internal (hconn x hx y hy)

theorem lift_spanningForest (hV : V(G).Finite) (hE : E(G).Finite) (hI : Fib G f I)
    (hF : F ⊆ E(contract G f)) {k : ℕ} :
    IsSpanningForest (contract G f) F k ↔ IsSpanningForest G (F ∪ I) k := by
  obtain ⟨hVQ, hEQ⟩ := contract_finite (f := f) hV hE
  rw [isSpanningForest_iff hVQ hEQ, isSpanningForest_iff hV hE]
  have hdisj : Disjoint F I := (hI.disjoint_ext.symm).mono_left hF
  have hcard : (F ∪ I).ncard = F.ncard + I.ncard :=
    Set.ncard_union_eq hdisj (hEQ.subset hF) (hE.subset hI.subset)
  have hc := hI.card hV hE
  have hQ : V(contract G f).ncard = (f '' V(G)).ncard := rfl
  have hcomp := comps_lift hI hF
  constructor
  · rintro ⟨_, hk, hn⟩
    exact ⟨Set.union_subset (hF.trans contract_edgeSet_subset) hI.subset, by rw [hcomp]; exact hk,
      by omega⟩
  · rintro ⟨_, hk, hn⟩
    exact ⟨hF, by rw [← hcomp]; exact hk, by omega⟩

end Lax630294Proofs.Quotient2Contract
