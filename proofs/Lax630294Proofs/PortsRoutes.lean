import Lax630294Proofs.PortsSelect
import Lax630294Proofs.CausalQuotient

/-!
# Original routes with their external skeleton

An *original route* is a `causal`-increasing walk of `G` (`PW`).  Its external projection is the
list `ts` of its calls in `E(Q)`; between two consecutive external calls the route runs inside one
block.  We record exactly this shape:

* `Seg G ℓ lo hi u v`: `u` and `v` are connected inside the block of `u` by internal calls strictly
  between the calls `lo` and `hi` (`none` = unbounded), and `lo <_P hi` if both are given;
* `XR G ℓ lo hi u v ts`: a route from `u` to `v` with external calls `ts`, all internal calls
  between `lo` and `hi` (an alternating sequence of `Seg`s and external calls).

DEVIATION: internal parts of routes are only kept up to connectivity (`Reach`), never as walks; the
only place where walks (`PW`) are needed is the extraction of the external skeleton of a route
from the completeness assumption (`XR.of_pw`).  Loop erasure of the paper is never needed.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree Lax630294Proofs.Quotient2Cycle
  Lax630294Proofs.CallOrder Lax630294Proofs.Causal Lax630294Proofs.CausalQuotient
  Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef Lax630294Proofs.Quotient2Contract
  Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- The bounds `lo`, `hi` are comparable (when both are given). -/
def Bnd (G : Graph α β) (ℓ : β → ℕ) (lo hi : Option β) : Prop :=
  ∀ a b, lo = some a → hi = some b → causal G ℓ a b

/-- The calls strictly between `lo` and `hi` in the causal order. -/
def Iv (G : Graph α β) (ℓ : β → ℕ) (lo hi : Option β) : Set β :=
  {c | (∀ a, lo = some a → causal G ℓ a c) ∧ (∀ b, hi = some b → causal G ℓ c b)}

/-- An internal segment inside the block of `u`, with calls strictly between `lo` and `hi`. -/
def Seg (G : Graph α β) (ℓ : β → ℕ) (lo hi : Option β) (u v : α) : Prop :=
  Bnd G ℓ lo hi ∧ Reach G (Ins G (blk G u) ∩ Iv G ℓ lo hi) u v

/-- An original route from `u` to `v` with external calls `ts`, internal calls between `lo`, `hi`. -/
def XR (G : Graph α β) (ℓ : β → ℕ) : Option β → Option β → α → α → List β → Prop
  | lo, hi, u, v, [] => Seg G ℓ lo hi u v
  | lo, hi, u, v, t :: ts => ∃ x y, Seg G ℓ lo (some t) u x ∧ G.IsLink t x y ∧
      t ∈ E(quotient G) ∧ XR G ℓ (some t) hi y v ts

/-- `x` is the end in `U` of the (external) call `t`. -/
def IsPort (G : Graph α β) (U : Set α) (t : β) (x : α) : Prop := x ∈ U ∧ G.Inc t x

lemma Iv_none_none : Iv G ℓ none none = Set.univ := by
  ext c; simp [Iv]

lemma bnd_none_left {hi : Option β} : Bnd G ℓ none hi := fun a b ha _ => by simp at ha

lemma XR.split : ∀ {ts1 : List β} {t : β} {ts2 : List β} {lo hi : Option β} {u v : α},
    XR G ℓ lo hi u v (ts1 ++ t :: ts2) →
    ∃ x y, XR G ℓ lo (some t) u x ts1 ∧ G.IsLink t x y ∧ t ∈ E(quotient G) ∧
      XR G ℓ (some t) hi y v ts2 := by
  intro ts1
  induction ts1 with
  | nil =>
    intro t ts2 lo hi u v h
    obtain ⟨x, y, h1, h2, h3, h4⟩ := h
    exact ⟨x, y, h1, h2, h3, h4⟩
  | cons t1 ts1 ih =>
    intro t ts2 lo hi u v h
    obtain ⟨x1, y1, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, k1, k2, k3, k4⟩ := ih h4
    exact ⟨x, y, ⟨x1, y1, h1, h2, h3, k1⟩, k2, k3, k4⟩

section Finite

variable (hV : V(G).Finite) (hE : E(G).Finite)
include hV hE

lemma Seg.blk_eq {lo hi : Option β} {u x : α} (h : Seg G ℓ lo hi u x) :
    blk G x = blk G u := by
  by_cases hxu : x = u
  · rw [hxu]
  have hu : u ∈ V(G) := reach_eq_or_mem h.2 (fun h => hxu h.symm)
  have key : ∀ y, Reach G (Ins G (blk G u) ∩ Iv G ℓ lo hi) u y → y ∈ blk G u := by
    intro y hy
    induction hy with
    | refl => exact mem_blk_self hV hE hu
    | tail _ hs _ =>
      obtain ⟨c, hc, hl⟩ := hs
      exact (ins_of_link hc.1 hl).2
  exact blk_eq_of_mem hV hE hu (key x h.2)

lemma Seg.prepend {lo hi : Option β} {e : β} {u w v : α} (hl : G.IsLink e u w)
    (he : e ∉ E(quotient G)) (hlo : ∀ a, lo = some a → causal G ℓ a e)
    (hhi : ∀ b, hi = some b → causal G ℓ e b) (h : Seg G ℓ lo hi w v) : Seg G ℓ lo hi u v := by
  have hb : blk G w = blk G u := by
    by_contra hne
    exact he (quotient_isLink.2 ⟨u, w, hl, rfl, rfl, fun h => hne h.symm⟩).edge_mem
  have hins : e ∈ Ins G (blk G u) :=
    ⟨u, w, hl, mem_blk_self hV hE hl.left_mem, hb ▸ mem_blk_self hV hE hl.right_mem⟩
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [hb] at h2
  exact (reach_of_isLink (F := Ins G (blk G u) ∩ Iv G ℓ lo hi) ⟨hins, hlo, hhi⟩ hl).trans' h2

/-- Extract the external skeleton of an increasing walk. -/
lemma XR.of_pw {u v : α} {vs : List α} {es : List β} (h : PW G (causal G ℓ) u v vs es) :
    ∀ lo hi : Option β, Bnd G ℓ lo hi → (∀ c ∈ es, c ∈ Iv G ℓ lo hi) →
      ∃ ts, XR G ℓ lo hi u v ts ∧ ∀ t ∈ ts, t ∈ es := by
  induction h with
  | nil u =>
    intro lo hi hb _
    exact ⟨[], ⟨hb, reach_refl⟩, by simp⟩
  | @cons u w v e vs es hl hw hR ih =>
    intro lo hi hb hIv
    have heIv : e ∈ Iv G ℓ lo hi := hIv e (by simp)
    by_cases heQ : e ∈ E(quotient G)
    · have hb' : Bnd G ℓ (some e) hi := fun a b ha hb => by
        have := Option.some.inj ha
        subst this
        exact heIv.2 b hb
      obtain ⟨ts, hts, hsub⟩ := ih (some e) hi hb' (fun c hc => ⟨fun a ha => by
        have := Option.some.inj ha
        subst this
        exact hR c hc, (hIv c (by simp [hc])).2⟩)
      refine ⟨e :: ts, ⟨u, w, ⟨fun a b ha hb => ?_, reach_refl⟩, hl, heQ, hts⟩, ?_⟩
      · have := Option.some.inj hb
        subst this
        exact heIv.1 a ha
      · intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · simp
        · simp [hsub t ht]
    · obtain ⟨ts, hts, hsub⟩ := ih lo hi hb (fun c hc => hIv c (by simp [hc]))
      refine ⟨ts, ?_, fun t ht => by simp [hsub t ht]⟩
      cases ts with
      | nil => exact Seg.prepend hV hE hl heQ heIv.1 heIv.2 hts
      | cons t ts' =>
        obtain ⟨x, y, h1, h2, h3, h4⟩ := hts
        refine ⟨x, y, Seg.prepend hV hE hl heQ heIv.1 (fun b hb => ?_) h1, h2, h3, h4⟩
        have := Option.some.inj hb
        subst this
        exact hR t (hsub t (by simp))

/-- The projection of a route to the quotient is an increasing trail. -/
lemma XR.incTrail : ∀ {ts : List β} {lo hi : Option β} {u v : α}, XR G ℓ lo hi u v ts →
    IncTrail (quotient G) (causalQ G ℓ) (blk G u) (blk G v) ts := by
  intro ts
  induction ts with
  | nil =>
    intro lo hi u v h
    have := Seg.blk_eq hV hE h
    rw [this]
    exact IncTrail.nil _
  | cons t ts ih =>
    intro lo hi u v h
    obtain ⟨x, y, hs, hl, ht, hrest⟩ := h
    have hbx := Seg.blk_eq hV hE hs
    have hne : blk G x ≠ blk G y := contract_ext (G := G) (f := blk G) ht hl
    have hq : (quotient G).IsLink t (blk G u) (blk G y) :=
      hbx ▸ quotient_isLink.2 ⟨x, y, hl, rfl, rfl, hne⟩
    refine IncTrail.cons hq (ih hrest) ?_
    intro f hf
    cases ts with
    | nil => simp at hf
    | cons f' ts' =>
      simp only [List.head?_cons, Option.some.injEq] at hf
      subst hf
      obtain ⟨x', y', hs', -, hf', -⟩ := hrest
      exact ⟨ht, hf', hs'.1 t f' rfl rfl⟩

/-- Completeness gives a route with an external skeleton between any two original vertices. -/
lemma exists_xr (hℓ : IsTemporallyConnected G ℓ) {u v : α} (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ ts, XR G ℓ none none u v ts := by
  obtain ⟨vs, es, -, -, -, hpw⟩ := exists_route hℓ hu hv
  obtain ⟨ts, hts, -⟩ := XR.of_pw hV hE hpw none none bnd_none_left
    (fun c _ => by rw [Iv_none_none]; trivial)
  exact ⟨ts, hts⟩

lemma Seg.chain {lo hi : Option β} {k : β} {u x y : α} (h1 : Seg G ℓ lo (some k) u x)
    (h2 : Seg G ℓ (some k) hi x y) : Seg G ℓ lo hi u y := by
  refine ⟨fun a b ha hb => causal_trans (h1.1 a k ha rfl) (h2.1 k b rfl hb), ?_⟩
  have hbl := Seg.blk_eq hV hE h1
  have h2' := h2.2
  rw [hbl] at h2'
  refine (reach_mono ?_ h1.2).trans' (reach_mono ?_ h2')
  · intro d hd
    exact ⟨hd.1, hd.2.1, fun b hb => causal_trans (hd.2.2 k rfl) (h2.1 k b rfl hb)⟩
  · intro d hd
    exact ⟨hd.1, fun a ha => causal_trans (h1.1 a k ha rfl) (hd.2.1 k rfl), hd.2.2⟩

end Finite

/-! ### Ports -/

section Ports

variable (hV : V(G).Finite) (hE : E(G).Finite)
include hV hE

lemma isPort_unique {U : Set α} (hU : U ∈ V(quotient G)) {t : β} (ht : t ∈ E(quotient G))
    {x y : α} (hx : IsPort G U t x) (hy : IsPort G U t y) : x = y := by
  obtain ⟨a, b, hl, hne⟩ := mem_edgeSet_quotient.1 ht
  have hxa : blk G x = U := blk_of_mem hV hE hU hx.1
  have hya : blk G y = U := blk_of_mem hV hE hU hy.1
  rcases hx.2.eq_or_eq_of_isLink hl with rfl | rfl <;>
    rcases hy.2.eq_or_eq_of_isLink hl with rfl | rfl
  · rfl
  · exact absurd (hxa.trans hya.symm) hne
  · exact absurd (hya.trans hxa.symm) hne
  · rfl

lemma exists_isPort {U : Set α} (hU : U ∈ V(quotient G)) {t : β}
    (hinc : (quotient G).Inc t U) : ∃ x, IsPort G U t x := by
  obtain ⟨W, hW⟩ := hinc
  obtain ⟨a, b, hl, rfl, rfl, hne⟩ := quotient_isLink.1 hW
  exact ⟨a, mem_blk_self hV hE hl.left_mem, hl.inc_left⟩

end Ports

/-! ### Chains of calls realised as walks -/

lemma _root_.Lax630294Proofs.Causal.PW.snoc {R : β → β → Prop} {u v w : α} {vs : List α} {es : List β} {c : β}
    (h : PW G R u v vs es) (hl : G.IsLink c v w) (hR : ∀ f ∈ es, R f c) :
    PW G R u w (vs ++ [v]) (es ++ [c]) := by
  induction h with
  | nil u => exact PW.cons hl (PW.nil w) (by simp)
  | @cons u w' v e vs es hl' hw hR' ih =>
    have := ih hl (fun f hf => hR f (by simp [hf]))
    refine PW.cons hl' this ?_
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact hR' f hf
    · rw [List.mem_singleton] at hf
      subst hf
      exact hR e (by simp)

lemma inc_isLink {a : β} {x y : α} (hx : G.Inc a x) (hy : G.Inc a y) (hne : x ≠ y) :
    G.IsLink a x y := by
  obtain ⟨w, hw⟩ := hy
  have : x = w := hx.eq_of_isLink_of_ne_left hw hne
  rw [this]
  exact hw.symm

/-- If `a <_P b`, there is an increasing walk from an end of `a` to an end of `b` using only calls
strictly between them. -/
lemma chain_walk {a b : β} (h : causal G ℓ a b) :
    ∃ s t vs es, G.Inc a s ∧ G.Inc b t ∧ PW G (causal G ℓ) s t vs es ∧
      ∀ c ∈ es, causal G ℓ a c ∧ causal G ℓ c b := by
  induction h with
  | single hs =>
    obtain ⟨⟨x, hx1, hx2⟩, -⟩ := hs
    exact ⟨x, x, [], [], hx1, hx2, PW.nil x, by simp⟩
  | @tail c' b hac hs ih =>
    obtain ⟨s, t', vs, es, ha, hc', hpw, hes⟩ := ih
    obtain ⟨⟨z, hz1, hz2⟩, hlt⟩ := hs
    have hcb : causal G ℓ c' b := Relation.TransGen.single ⟨⟨z, hz1, hz2⟩, hlt⟩
    by_cases ht : t' = z
    · subst ht
      exact ⟨s, t', vs, es, ha, hz2, hpw, fun c hc =>
        ⟨(hes c hc).1, causal_trans (hes c hc).2 hcb⟩⟩
    · have hl : G.IsLink c' t' z := inc_isLink hc' hz1 ht
      refine ⟨s, z, vs ++ [t'], es ++ [c'], ha, hz2, hpw.snoc hl (fun f hf => (hes f hf).2), ?_⟩
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ⟨(hes c hc).1, causal_trans (hes c hc).2 hcb⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact ⟨hac, hcb⟩

end Lax630294Proofs.Ports
