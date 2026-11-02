import Lax630294Proofs.PortsGood

/-!
# Closed sets and internal returns (`lem:characterization-actual-closed-set`)

* `rootOf x0 x1 i`: the root block of index `i : Bool`;
* `Nb`: the vertices `V` occurring immediately before a root in the projections of the filtered
  routes starting at a vertex of a block `U`;
* `ClosedSet`, `Cvx`, `MinClosed`.

As in the (revised) paper, `S` is inclusion-minimal among the nonempty closed sets for which `Y[S]`
is connected (`MinClosed`); that `Y[S]` is a tree is `Acyc.mono` applied to the acyclicity of `Y`.
No deviation.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- The root block of index `i`. -/
def rootOf (x0 x1 : Set α) (i : Bool) : Set α := cond i x1 x0

lemma rootOf_or (x0 x1 : Set α) (i : Bool) : rootOf x0 x1 i = x0 ∨ rootOf x0 x1 i = x1 := by
  cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma rootOf_ne {x0 x1 : Set α} (h : x0 ≠ x1) (i : Bool) : rootOf x0 x1 i ≠ rootOf x0 x1 (!i) := by
  cases i
  · exact h
  · exact fun h' => h h'.symm

/-- `V` is the vertex before the root `r` in a filtered route starting at a vertex of `U`. -/
def Nb (G : Graph α β) (ℓ : β → ℕ) (e : β) (r : Set α) (U V : Set α) : Prop :=
  ∃ u ∈ U, ∃ v L t, Filt G ℓ e r u v L t ∧ (quotient G).IsLink t V r

/-- A closed set of vertices of `Y`. -/
def ClosedSet (G : Graph α β) (ℓ : β → ℕ) (e : β) (x0 x1 : Set α) (Y S : Set (Set α)) : Prop :=
  S.Nonempty ∧ S ⊆ Y ∧ ∀ U ∈ S, ∀ i : Bool, ∀ V, Nb G ℓ e (rootOf x0 x1 i) U V → V ∈ S

/-- `Y[S]` is connected. -/
def Cvx (G : Graph α β) (I : Set β) (S : Set (Set α)) : Prop :=
  ∀ U ∈ S, ∀ W ∈ S, Reach (quotient G) (edgesIn (quotient G) I S) U W

/-- `S` is an inclusion-minimal closed set with `Y[S]` connected. -/
def MinClosed (G : Graph α β) (ℓ : β → ℕ) (e : β) (I : Set β) (x0 x1 : Set α)
    (Y S : Set (Set α)) : Prop :=
  ClosedSet G ℓ e x0 x1 Y S ∧ Cvx G I S ∧
    ∀ S', S' ⊆ S → ClosedSet G ℓ e x0 x1 Y S' → Cvx G I S' → S' = S

lemma reach_restrict {γ : Type*} {H : Graph γ β} {E0 : Set β} {T : Set γ}
    (hT : ∀ c ∈ E0, ∀ x y, H.IsLink c x y → x ∈ T → y ∈ T) {a x : γ} (ha : a ∈ T)
    (h : Reach H E0 a x) : x ∈ T ∧ Reach H {c | c ∈ E0 ∧ c ∈ Ins H T} a x := by
  induction h with
  | refl => exact ⟨ha, reach_refl⟩
  | tail _ hs ih =>
    obtain ⟨c, hc, hl⟩ := hs
    have hz := hT c hc _ _ hl ih.1
    exact ⟨hz, ih.2.tail ⟨c, ⟨hc, _, _, hl, ih.1, hz⟩, hl⟩⟩

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

lemma ne01 : x0 ≠ x1 := c.q.ne01

lemma link_root_unique {V V' r : Set α} {t : β} (hV' : V' ∈ Y) (hr : r = x0 ∨ r = x1)
    (hl : (quotient G).IsLink t V r) (hl' : (quotient G).IsLink t V' r) : V = V' := by
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · exfalso
    have hrX : r ∈ X := by rcases hr with rfl | rfl; exacts [c.q.x0_mem, c.q.x1_mem]
    exact c.q.mem_Y_not_X hV' (h ▸ hrX)

/-- No vertex is joined by future calls to both roots. -/
lemma no_other_root {U : Set α} {i : Bool} {f t : β} (hf : f ∈ E(quotient G) \ I)
    (hfl : (quotient G).IsLink f U (rootOf x0 x1 i)) (ht : t ∈ E(quotient G) \ I)
    (htl : (quotient G).IsLink t U (rootOf x0 x1 (!i))) : False := by
  cases i
  · exact c.q.not_both_roots hf ht hfl htl
  · exact c.q.not_both_roots ht hf htl hfl

lemma f_unique {U : Set α} {i i' : Bool} {f f' : β} (hf : f ∈ E(quotient G) \ I)
    (hfl : (quotient G).IsLink f U (rootOf x0 x1 i)) (hf' : f' ∈ E(quotient G) \ I)
    (hfl' : (quotient G).IsLink f' U (rootOf x0 x1 i')) : i = i' ∧ f = f' := by
  have hii : i = i' := by
    by_contra hne
    have : i' = !i := by cases i <;> cases i' <;> simp_all
    subst this
    exact c.no_other_root hf hfl hf' hfl'
  subst hii
  exact ⟨rfl, c.q.hA.simple.eq_of_isLink hfl hfl'⟩

/-- `Nb` stays inside `Y`. -/
lemma nb_mem_Y {U V : Set α} {i : Bool} (hU : U ∈ Y) (h : Nb G ℓ e (rootOf x0 x1 i) U V) :
    V ∈ Y := by
  obtain ⟨u, hu, v, L, t, hf, hl⟩ := h
  obtain ⟨V', hV'Y, hl', -⟩ := c.filt_shape hU (rootOf_or x0 x1 i) hu hf
  rw [c.link_root_unique hV'Y (rootOf_or x0 x1 i) hl hl']
  exact hV'Y

lemma closed_Y : ClosedSet G ℓ e x0 x1 Y Y :=
  ⟨c.q.hY.1.1, subset_rfl, fun _ hU _ _ h => c.nb_mem_Y hU h⟩

lemma cvx_Y : Cvx G I Y := fun U hU W hW =>
  (reach_edgesIn c.q.hYc hU (c.q.hY.1.2.2.2 U hU W hW)).1

lemma exists_minClosed : ∃ S, MinClosed G ℓ e I x0 x1 Y S := by
  classical
  have hYfin : Y.Finite := c.q.hA.finV.subset c.q.hY.1.2.1
  let F0 : Set (Set (Set α)) := {S | ClosedSet G ℓ e x0 x1 Y S ∧ Cvx G I S}
  have hF0fin : F0.Finite := hYfin.finite_subsets.subset fun S hS => hS.1.2.1
  obtain ⟨S, hS, hmin⟩ := Set.exists_min_image F0 (fun S => S.ncard) hF0fin ⟨Y, c.closed_Y, c.cvx_Y⟩
  refine ⟨S, hS.1, hS.2, fun S' hS'S hcl hcv => ?_⟩
  have hSfin : S.Finite := hYfin.subset hS.1.2.1
  exact Set.eq_of_subset_of_ncard_le hS'S (hmin S' ⟨hcl, hcv⟩) hSfin

omit c in
lemma exists_edge_at {S : Set (Set α)} (hcv : Cvx G I S) {U W : Set α} (hU : U ∈ S) (hW : W ∈ S)
    (hne : U ≠ W) : ∃ k ∈ edgesIn (quotient G) I S, (quotient G).Inc k U := by
  rcases Relation.ReflTransGen.cases_head (hcv U hU W hW) with h | ⟨y, ⟨k, hk, hl⟩, -⟩
  · exact absurd h hne
  · exact ⟨k, hk, hl.inc_left⟩

/-- The singleton case is impossible. -/
theorem two_le {S : Set (Set α)} (hS : ClosedSet G ℓ e x0 x1 Y S) :
    ∃ U W, U ∈ S ∧ W ∈ S ∧ U ≠ W := by
  by_contra hcon
  push Not at hcon
  obtain ⟨U, hU⟩ := hS.1
  have hUY : U ∈ Y := hS.2.1 hU
  have hUV := c.Y_V hUY
  obtain ⟨x, hx, rfl⟩ := hUV
  have hu : x ∈ blk G x := mem_blk_self c.hV c.hE hx
  have key : ∀ i : Bool, ∃ t, t ∈ E(quotient G) \ I ∧
      (quotient G).IsLink t (blk G x) (rootOf x0 x1 i) := by
    intro i
    obtain ⟨v, L, t, hf⟩ := c.root_good_routes hUY (rootOf_or x0 x1 i) hu
    obtain ⟨V, hVY, hl, htF, -⟩ := c.filt_shape hUY (rootOf_or x0 x1 i) hu hf
    have hVS : V ∈ S := hS.2.2 _ hU i V ⟨x, hu, v, L, t, hf, hl⟩
    have := hcon V _ hVS hU
    rw [this] at hl
    exact ⟨t, htF, hl⟩
  obtain ⟨t0, ht0, hl0⟩ := key false
  obtain ⟨t1, ht1, hl1⟩ := key true
  exact c.q.not_both_roots ht0 ht1 hl0 hl1

end PCtx

end Lax630294Proofs.Ports
