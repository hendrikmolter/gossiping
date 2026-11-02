import Lax630294Proofs.PortsGraph

/-!
# The quotient-level standing facts for port selection

`QCtx H P I X Y e x0 x1` records the standing hypotheses of the section "Selecting Compatible
Ports Using Original Routes" on the level of the quotient `H = Q` with its order `P = P_Q`:
`H` is admissible, `(I, X, e, x0, x1)` is canonical, and `Y` is the second tree component of `H[I]`.
Everything here is purely about `H` (no original graph).

Derived facts: the two roots are separated by `F = E(H) \ I`, outward comparability of future edges
at a vertex adjacent to a root, acyclicity of the early trees, of `F` and of `F + e`, `e` maximal
in `I`, and the "interval" lemmas (calls between two calls of a tree/forest stay in it) that feed
`forest-confinement`.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.SpanningStructures Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder

variable {γ β : Type*} {H : Graph γ β} {P : β → β → Prop}

/-- Standing hypotheses on the quotient level. -/
structure QCtx (H : Graph γ β) (P : β → β → Prop) (I : Set β) (X Y : Set γ) (e : β)
    (x0 x1 : γ) : Prop where
  hA : Admissible H P
  hC : IsCanonical H P I X e x0 x1
  hY : IsTreeComp H I Y
  hYX : Y ≠ X

section QCtx

variable {I : Set β} {X Y : Set γ} {e : β} {x0 x1 : γ}

lemma QCtx.hX (c : QCtx H P I X Y e x0 x1) : IsComp H I X := c.hC.tree.1

lemma QCtx.hYc (c : QCtx H P I X Y e x0 x1) : IsComp H I Y := c.hY.1

lemma QCtx.ne01 (c : QCtx H P I X Y e x0 x1) : x0 ≠ x1 := by
  have := c.hA.simple
  exact c.hC.e_link.ne

lemma QCtx.x0_mem (c : QCtx H P I X Y e x0 x1) : x0 ∈ X :=
  (c.hC.e_mem.2.ends_mem c.hC.e_link).1

lemma QCtx.x1_mem (c : QCtx H P I X Y e x0 x1) : x1 ∈ X :=
  (c.hC.e_mem.2.ends_mem c.hC.e_link).2

lemma QCtx.disj (c : QCtx H P I X Y e x0 x1) : Disjoint X Y :=
  c.hX.disjoint_of_ne c.hYc c.hYX.symm

lemma QCtx.mem_Y_not_X (c : QCtx H P I X Y e x0 x1) {U : γ} (hU : U ∈ Y) : U ∉ X :=
  fun h => Set.disjoint_left.1 c.disj h hU

lemma QCtx.Y_ne_x0 (c : QCtx H P I X Y e x0 x1) {U : γ} (hU : U ∈ Y) : U ≠ x0 :=
  fun h => c.mem_Y_not_X hU (h ▸ c.x0_mem)

lemma QCtx.Y_ne_x1 (c : QCtx H P I X Y e x0 x1) {U : γ} (hU : U ∈ Y) : U ≠ x1 :=
  fun h => c.mem_Y_not_X hU (h ▸ c.x1_mem)

lemma QCtx.hI (c : QCtx H P I X Y e x0 x1) : IsIdeal H P I := c.hC.ideal

lemma QCtx.trans (c : QCtx H P I X Y e x0 x1) : ∀ a b d, P a b → P b d → P a d :=
  fun _ _ _ h1 h2 => c.hA.trans h1 h2

/-- A component of `H[I]` is closed under the edges of `I`. -/
lemma _root_.Lax630294Proofs.CallOrder.IsComp.link_mem {S : Set β} {A : Set γ} (hA : IsComp H S A) {f : β} (hf : f ∈ S) {u w : γ}
    (hl : H.IsLink f u w) (hu : u ∈ A) : w ∈ A := hA.2.2.1 f hf u w hl hu

/-- Well-founded induction along the order. -/
lemma _root_.Lax630294Proofs.CallOrder.Admissible.ind (hA : Admissible H P) {motive : β → Prop}
    (h : ∀ c ∈ E(H), (∀ d, P d c → motive d) → motive c) : ∀ c ∈ E(H), motive c := by
  have : Finite E(H) := hA.finE.to_subtype
  let r : E(H) → E(H) → Prop := fun a b => P a b
  have : IsTrans E(H) r := ⟨fun a b c => hA.trans⟩
  have : Std.Irrefl r := ⟨fun a => hA.irrefl a⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  intro c hc
  have key : ∀ x : E(H), motive x.1 := fun x => wf.induction x (fun y ih =>
    h y.1 y.2 (fun d hd => ih ⟨d, hA.mem_left hd⟩ hd))
  exact key ⟨c, hc⟩

/-- Calls above an internal call of a component, inside an ideal, are internal to it too. -/
lemma _root_.Lax630294Proofs.CallOrder.Admissible.interval_internal (hA : Admissible H P) {I : Set β} {A : Set γ}
    (hI : IsIdeal H P I) (hAc : IsComp H I A) {a : β} (ha : Internal H A a) :
    ∀ c, P a c → c ∈ I → Internal H A c := by
  have key : ∀ c ∈ E(H), P a c → c ∈ I → Internal H A c := by
    refine hA.ind (fun c hcE ih hac hcI => ?_)
    obtain ⟨d, ⟨hdT, hdc⟩, hdmax⟩ := hA.exists_max
      (T := {d | (d = a ∨ P a d) ∧ P d c}) (fun d hd => hA.mem_left hd.2)
      ⟨a, Or.inl rfl, hac⟩
    have hcov : ∀ x, P d x → ¬ P x c := by
      intro x hdx hxc
      refine hdmax x ⟨Or.inr ?_, hxc⟩ hdx
      rcases hdT with rfl | h
      · exact hdx
      · exact hA.trans h hdx
    have hdI : d ∈ I := hI.2 d c hdc hcI
    have hdint : Internal H A d := by
      rcases hdT with rfl | h
      · exact ha
      · exact ih d hdc h hdI
    obtain ⟨z, hz1, hz2⟩ := hA.cover_adj hdc hcov
    obtain ⟨y1, hy1⟩ := hz1
    obtain ⟨y2, hy2⟩ := hz2
    have hzA : z ∈ A := (hdint.ends_mem hy1).1
    exact ⟨z, y2, hy2, hzA, hAc.link_mem hcI hy2 hzA⟩
  intro c hac hcI
  exact key c (hA.mem_right hac) hac hcI

lemma QCtx.mid_early (c : QCtx H P I X Y e x0 x1) {A : Set γ} (hAc : IsComp H I A) {a b : β}
    (ha : a ∈ edgesIn H I A) (hb : b ∈ edgesIn H I A) :
    ∀ d, P a d → P d b → d ∈ edgesIn H I A := fun d had hdb =>
  have hdI : d ∈ I := c.hI.2 d b hdb hb.1
  ⟨hdI, c.hA.interval_internal c.hI hAc ha.2 d had hdI⟩

lemma QCtx.e_max_I (c : QCtx H P I X Y e x0 x1) : ∀ d ∈ I, ¬ P e d := by
  intro d hdI hed
  have hint := c.hA.interval_internal c.hI c.hX c.hC.e_mem.2 d hed hdI
  have hne : d ≠ e := fun h => c.hA.irrefl e (h ▸ hed)
  exact c.hA.asymm hed (c.hC.e_max d ⟨hdI, hint⟩ hne)

lemma QCtx.mid_future (c : QCtx H P I X Y e x0 x1) {a : β} (ha : a ∈ E(H) \ I) :
    ∀ d, P a d → d ∈ E(H) \ I := fun d had =>
  ⟨c.hA.mem_right had, fun hdI => ha.2 (c.hI.2 a d had hdI)⟩

lemma QCtx.mid_eF (c : QCtx H P I X Y e x0 x1) :
    ∀ d, P e d → d ∈ E(H) → d ∈ E(H) \ I := fun d hed hdE =>
  ⟨hdE, fun hdI => c.e_max_I d hdI hed⟩

lemma QCtx.e_lt_F (c : QCtx H P I X Y e x0 x1) {f : β} (hf : f ∈ E(H) \ I) : P e f :=
  c.hC.e_lt f hf

/-- Reachability inside a component stays on the component's own edges. -/
lemma reach_edgesIn {I : Set β} {A : Set γ} (hAc : IsComp H I A) {x y : γ} (hx : x ∈ A)
    (h : Conn H I x y) : Reach H (edgesIn H I A) x y ∧ y ∈ A := by
  induction h with
  | refl => exact ⟨reach_refl, hx⟩
  | tail _ hs ih =>
    obtain ⟨f, hf, hl⟩ := hs
    have hz : _ ∈ A := hAc.link_mem hf hl ih.2
    exact ⟨ih.1.tail ⟨f, ⟨hf, _, _, hl, ih.2, hz⟩, hl⟩, hz⟩

lemma QCtx.acyc_tree (c : QCtx H P I X Y e x0 x1) {A : Set γ} (hA : IsTreeComp H I A) :
    Acyc H (edgesIn H I A) := by
  refine acyc_of_tree c.hA.finV c.hA.finE hA.1.2.1 hA.1.1 (fun f hf => hf.2) ?_ ?_
  · intro x hx y hy
    exact (reach_edgesIn hA.1 hx (hA.1.2.2.2 x hx y hy)).1
  · have := hA.2
    omega

lemma QCtx.acyc_Y (c : QCtx H P I X Y e x0 x1) : Acyc H (edgesIn H I Y) :=
  c.acyc_tree c.hY

/-! ### The forest `F` -/

/-- The root separation: a set `Sd` containing `x0` but not `x1` such that no edge of `F`
crosses it. -/
lemma QCtx.side (c : QCtx H P I X Y e x0 x1) :
    ∃ Sd : Set γ, x0 ∈ Sd ∧ x1 ∉ Sd ∧
      ∀ f ∈ E(H) \ I, ∀ u w, H.IsLink f u w → (u ∈ Sd ↔ w ∈ Sd) := by
  obtain ⟨par, pe, hfor⟩ := c.hC.forest
  refine ⟨{v | ∃ n, par^[n] v = x0}, ⟨0, rfl⟩, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    rw [Function.iterate_fixed hfor.par_x1 n] at hn
    exact c.ne01 hn.symm
  · intro f hf u w hl
    obtain ⟨v, hv, hvf⟩ := hfor.bij.surjOn hf
    have hv0 : v ≠ x0 := fun h => hv.2 (Or.inl h)
    have hv1 : v ≠ x1 := fun h => hv.2 (Or.inr h)
    have hlv := (hfor.edge_mem v hv.1 hv0 hv1).2
    rw [hvf] at hlv
    have hiff : (∃ n, par^[n] v = x0) ↔ ∃ n, par^[n] (par v) = x0 :=
      iterate_step_iff hv0
    rcases hlv.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hiff
    · exact hiff.symm

lemma QCtx.not_reach_F (c : QCtx H P I X Y e x0 x1) : ¬ Reach H (E(H) \ I) x0 x1 := by
  obtain ⟨Sd, h0, h1, hSd⟩ := c.side
  intro h
  have : ∀ y, Reach H (E(H) \ I) x0 y → y ∈ Sd := by
    intro y hy
    induction hy with
    | refl => exact h0
    | tail _ hs ih =>
      obtain ⟨f, hf, hl⟩ := hs
      exact (hSd f hf _ _ hl).1 ih
  exact h1 (this x1 h)

/-- No vertex is adjacent by future edges to both roots. -/
lemma QCtx.not_both_roots (c : QCtx H P I X Y e x0 x1) {U : γ} {f t : β} (hf : f ∈ E(H) \ I)
    (ht : t ∈ E(H) \ I) (hfl : H.IsLink f U x0) (htl : H.IsLink t U x1) : False := by
  obtain ⟨Sd, h0, h1, hSd⟩ := c.side
  have hU : U ∈ Sd := (hSd f hf _ _ hfl).2 h0
  exact h1 ((hSd t ht _ _ htl).1 hU)

lemma QCtx.acyc_F (c : QCtx H P I X Y e x0 x1) : Acyc H (E(H) \ I) := by
  have := c.hA.simple
  obtain ⟨par, pe, hfor⟩ := c.hC.forest
  obtain ⟨-, hs, ha, -⟩ := hfor.isSpanningForest (Set.sdiff_subset) c.hC.e_link.left_mem
    c.hC.e_link.right_mem c.ne01
  exact acyc_of_isForest ⟨hs, ha⟩

lemma QCtx.acyc_eF (c : QCtx H P I X Y e x0 x1) : Acyc H (insert e (E(H) \ I)) := by
  have := c.hA.simple
  obtain ⟨par, pe, hfor⟩ := c.hC.forest
  obtain ⟨-, hs, ha, -⟩ := hfor.isSpanningForest (Set.sdiff_subset) c.hC.e_link.left_mem
    c.hC.e_link.right_mem c.ne01
  exact acyc_of_isForest
    ((isForest_insert_iff_of_not_reach c.hC.e_link c.not_reach_F).2 ⟨hs, ha⟩)

/-- Outward comparability: if `f` joins `U` to a root, every future edge `t` at `U` is `f` or
above `f`. -/
lemma QCtx.outward (c : QCtx H P I X Y e x0 x1) {U r : γ} (_hU : U ∈ V(H)) (hU0 : U ≠ x0)
    (hU1 : U ≠ x1) {f t : β} (hf : f ∈ E(H) \ I) (hfl : H.IsLink f U r)
    (hr : r = x0 ∨ r = x1) (ht : t ∈ E(H) \ I) (htU : H.Inc t U) : t = f ∨ P f t := by
  obtain ⟨par, pe, hfor⟩ := c.hC.forest
  obtain ⟨v, hv, hvf⟩ := hfor.bij.surjOn hf
  have hv0 : v ≠ x0 := fun h => hv.2 (Or.inl h)
  have hv1 : v ≠ x1 := fun h => hv.2 (Or.inr h)
  have hlv := (hfor.edge_mem v hv.1 hv0 hv1).2
  rw [hvf] at hlv
  -- `v = U` and `par U = r`
  have hvU : v = U ∧ par v = r := by
    rcases hlv.eq_and_eq_or_eq_and_eq hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exfalso
      rcases hr with rfl | rfl
      · exact hv0 h1
      · exact hv1 h1
  obtain ⟨hvU1, hpar⟩ := hvU
  obtain ⟨v', hv', hvt⟩ := hfor.bij.surjOn ht
  have hv'0 : v' ≠ x0 := fun h => hv'.2 (Or.inl h)
  have hv'1 : v' ≠ x1 := fun h => hv'.2 (Or.inr h)
  have hlv' := (hfor.edge_mem v' hv'.1 hv'0 hv'1).2
  rw [hvt] at hlv'
  rcases htU.eq_or_eq_of_isLink hlv' with h | h
  · left
    have : v' = v := h.symm.trans hvU1.symm
    rw [← hvt, ← hvf, this]
  · right
    have := hfor.outward v' hv'.1 hv'0 hv'1 (by rw [← h]; exact hU0) (by rw [← h]; exact hU1)
    rw [← h, ← hvU1, hvf, hvt] at this
    exact this

end QCtx

end Lax630294Proofs.Ports
