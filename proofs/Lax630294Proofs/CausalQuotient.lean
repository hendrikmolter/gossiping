import Lax630294Proofs.CausalOrder
import Lax630294Proofs.CallOrderDefs
import Lax630294Proofs.QuotientDef

/-!
# Transfer of the causal order to the quotient (`lem:characterization-poset-transfer`)

`G` is a labeled graph, `ℓ` makes it temporally connected, `Q = quotient G`.  The order `P_Q` is
the restriction of the causal order `causal G ℓ` of `G` (not a "blocks as vertices" order) to
the external edges `E(Q) ⊆ E(G)`.
-/

namespace Lax630294Proofs.CausalQuotient

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal Lax630294Proofs.Causal
  Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef

variable {α β : Type*}

/-- Restriction of a relation on edges to the edges of `H`. -/
def restrictE {γ : Type*} (H : Graph γ β) (R : β → β → Prop) (a b : β) : Prop :=
  a ∈ E(H) ∧ b ∈ E(H) ∧ R a b

/-- `P_Q`: the causal order of `G` restricted to the external edges `E(quotient G)`. -/
def causalQ (G : Graph α β) (ℓ : β → ℕ) : β → β → Prop :=
  restrictE (quotient G) (causal G ℓ)

variable {G : Graph α β} {ℓ : β → ℕ}

lemma vertexSet_quotient : V(quotient G) = blk G '' V(G) := rfl

/-- Projection of a route to the quotient: omit internal calls; the retained external calls form
a sublist and stay `R`-increasing. -/
theorem _root_.Lax630294Proofs.Causal.PW.project {R : β → β → Prop} {u v : α} {vs : List α} {es : List β}
    (h : PW G R u v vs es) :
    ∃ vs' es', PW (quotient G) (restrictE (quotient G) R) (blk G u) (blk G v) vs' es' ∧
      es'.Sublist es := by
  induction h with
  | nil => exact ⟨[], [], .nil _, List.Sublist.refl _⟩
  | @cons u w v e vs es hl hw hR ih =>
    obtain ⟨vs', es', h', hsub⟩ := ih
    by_cases hb : blk G u = blk G w
    · rw [hb]; exact ⟨vs', es', h', hsub.cons e⟩
    · have hq : (quotient G).IsLink e (blk G u) (blk G w) :=
        quotient_isLink.2 ⟨u, w, hl, rfl, rfl, hb⟩
      refine ⟨blk G u :: vs', e :: es', .cons hq h' fun f hf => ?_, hsub.cons_cons e⟩
      exact ⟨hq.edge_mem, h'.edge_mem f hf, hR f (hsub.subset hf)⟩

lemma inc_quotient {a : β} {x : α} (ha : a ∈ E(quotient G)) (hx : G.Inc a x) :
    (quotient G).Inc a (blk G x) := by
  obtain ⟨U, W, hUW⟩ := (quotient G).exists_isLink_of_mem_edgeSet ha
  obtain ⟨x0, y0, hl, rfl, rfl, hne⟩ := quotient_isLink.1 hUW
  obtain ⟨z, hz⟩ := hx
  rcases hl.eq_and_eq_or_eq_and_eq hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, hUW⟩
  · exact ⟨_, hUW.symm⟩

/-- Key step for covers: a causal chain from `a` to `b` without external call strictly in between
joins endpoints of `a` and `b` lying in one block. -/
lemma chain_block {a b : β} (h : causal G ℓ a b)
    (hno : ∀ c, causal G ℓ a c → causal G ℓ c b → c ∉ E(quotient G)) :
    ∃ x y, G.Inc a x ∧ G.Inc b y ∧ blk G x = blk G y := by
  induction h with
  | single h => obtain ⟨x, hx, hy⟩ := h.1; exact ⟨x, x, hx, hy, rfl⟩
  | @tail c' b hac hcb ih =>
    obtain ⟨x, y, hxa, hyc, hxy⟩ := ih (fun c h1 h2 =>
      hno c h1 (Relation.TransGen.tail h2 hcb))
    have hc'Q : c' ∉ E(quotient G) := hno c' hac (Relation.TransGen.single hcb)
    obtain ⟨z, hz1, hz2⟩ := hcb.1
    obtain ⟨p, q, hpq⟩ := G.exists_isLink_of_mem_edgeSet hz1.edge_mem
    have hbl : blk G p = blk G q := by
      by_contra hne
      exact hc'Q (quotient_isLink.2 ⟨p, q, hpq, rfl, rfl, hne⟩).edge_mem
    have hyz : blk G y = blk G z := by
      rcases hyc.eq_or_eq_of_isLink hpq with rfl | rfl <;>
        rcases hz1.eq_or_eq_of_isLink hpq with rfl | rfl <;> simp [hbl]
    exact ⟨x, z, hxa, hz2, hxy.trans hyz⟩

end Lax630294Proofs.CausalQuotient

namespace Lax630294Proofs.CausalQuotient

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal Lax630294Proofs.Causal
  Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- **`lem:characterization-poset-transfer`.**  If `ℓ` makes the finite graph `G` temporally
connected and its quotient `Q` is simple, then the restriction `P_Q` of the causal order of
`(G, ℓ)` to the external edges is admissible on `Q`: a strict partial order on `E(Q)`, every
linear extension is complete on `Q`, every cover relates incident edges. -/
-- DEVIATION: cover step proved by induction on the causal chain (no intermediate external call
-- => all intermediate internal calls lie in one block); loops/looplessness and injectivity of the
-- labeling are not needed; E(G) finite is an explicit hypothesis.
theorem admissible (hV : V(G).Finite) (hE : E(G).Finite) (hQ : (quotient G).Simple)
    (hℓ : IsTemporallyConnected G ℓ) :
    CallOrder.Admissible (quotient G) (causalQ G ℓ) where
  simple := hQ
  finV := by rw [vertexSet_quotient]; exact hV.image _
  finE := hE.subset fun e he => he.1
  irrefl e h := causal_irrefl e h.2.2
  trans h h' := ⟨h.1, h'.2.1, causal_trans h.2.2 h'.2.2⟩
  mem_left h := h.1
  mem_right h := h.2.1
  complete ℓ' _ hext := by
    intro U hU W hW
    rw [vertexSet_quotient] at hU hW
    obtain ⟨u, hu, rfl⟩ := hU
    obtain ⟨v, hv, rfl⟩ := hW
    obtain ⟨vs, es, -, -, -, h4⟩ := exists_route hℓ hu hv
    obtain ⟨vs', es', h5, -⟩ := h4.project
    exact h5.hasTemporalPath fun a b hab => hext a b hab
  cover_adj {a b} hab hcov := by
    obtain ⟨ha, hb, hab⟩ := hab
    obtain ⟨x, y, hx, hy, hxy⟩ := chain_block hab fun c h1 h2 hc =>
      hcov c ⟨ha, hc, h1⟩ ⟨hc, hb, h2⟩
    exact ⟨blk G x, inc_quotient ha hx, hxy ▸ inc_quotient hb hy⟩

/-! ### Internal graphs `J_B^-(t)` and `J_B^+(t)` -/

/-- `J_B^-(t)`: the edges of `G[B]` causally below the call `t`, on the full vertex set `B`. -/
def intBelow (G : Graph α β) (ℓ : β → ℕ) (B : Set α) (t : β) : Graph α β :=
  (G.induce B).restrict {e | causal G ℓ e t}

/-- `J_B^+(t)`: the edges of `G[B]` causally above the call `t`, on the full vertex set `B`. -/
def intAbove (G : Graph α β) (ℓ : β → ℕ) (B : Set α) (t : β) : Graph α β :=
  (G.induce B).restrict {e | causal G ℓ t e}

end Lax630294Proofs.CausalQuotient
