import Lax630294Proofs.PortsConfine
import Lax630294Proofs.PortsQ2

/-!
# Internal connectivity at the relevant thresholds
(`lem:characterization-internal-threshold-connectivity`)

`PCtx G ℓ I X Y e x0 x1` collects the standing hypotheses: `G` finite, `ℓ` temporally connecting
(injectivity of `ℓ` is not needed), and the quotient-level context `QCtx` for
`Q = quotient G` with the causal order `P_Q`.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- The internal edges of the block `U` causally below `f` (`J_U^-(f)`). -/
def Below (G : Graph α β) (ℓ : β → ℕ) (U : Set α) (f : β) : Set β :=
  Ins G U ∩ Iv G ℓ none (some f)

/-- The internal edges of the block `U` causally above `f` (`J_U^+(f)`). -/
def Above (G : Graph α β) (ℓ : β → ℕ) (U : Set α) (f : β) : Set β :=
  Ins G U ∩ Iv G ℓ (some f) none

/-- Standing hypotheses of the section, bundled. -/
structure PCtx (G : Graph α β) (ℓ : β → ℕ) (I : Set β) (X Y : Set (Set α)) (e : β)
    (x0 x1 : Set α) : Prop where
  hV : V(G).Finite
  hE : E(G).Finite
  hℓ : IsTemporallyConnected G ℓ
  q : QCtx (quotient G) (causalQ G ℓ) I X Y e x0 x1

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

lemma blk_eq {U : Set α} (hU : U ∈ V(quotient G)) {z : α} (hz : z ∈ U) : blk G z = U :=
  blk_of_mem c.hV c.hE hU hz

lemma sub_V {U : Set α} (hU : U ∈ V(quotient G)) : U ⊆ V(G) := by
  obtain ⟨x, hx, rfl⟩ := hU
  exact blk_subset c.hV c.hE hx

lemma Y_V {U : Set α} (hU : U ∈ Y) : U ∈ V(quotient G) := c.q.hYc.2.1 hU

lemma root_V {r : Set α} (hr : r = x0 ∨ r = x1) : r ∈ V(quotient G) := by
  rcases hr with rfl | rfl
  · exact c.q.hC.e_link.left_mem
  · exact c.q.hC.e_link.right_mem

lemma e_inc_root {r : Set α} (hr : r = x0 ∨ r = x1) : (quotient G).Inc e r := by
  rcases hr with rfl | rfl
  · exact c.q.hC.e_link.inc_left
  · exact c.q.hC.e_link.inc_right

lemma e_mem_Q : e ∈ E(quotient G) := c.q.hC.e_link.edge_mem

lemma exists_e_port {r : Set α} (hr : r = x0 ∨ r = x1) : ∃ a, IsPort G r e a :=
  exists_isPort c.hV c.hE (c.root_V hr) (c.e_inc_root hr)

/-- A `Seg` read as connectivity in `Ins G U ∩ Iv lo' hi'`. -/
lemma seg_reach {lo hi lo' hi' : Option β} {U : Set α} {u v : α} (hU : U ∈ V(quotient G))
    (hu : u ∈ U) (hs : Seg G ℓ lo hi u v) (hsub : Iv G ℓ lo hi ⊆ Iv G ℓ lo' hi') :
    Reach G (Ins G U ∩ Iv G ℓ lo' hi') u v := by
  have hb := c.blk_eq hU hu
  have h := hs.2
  rw [hb] at h
  exact reach_mono (fun d hd => ⟨hd.1, hsub hd.2⟩) h

lemma seg_blk_mem {lo hi : Option β} {U : Set α} {u v : α} (hU : U ∈ V(quotient G)) (hu : u ∈ U)
    (hs : Seg G ℓ lo hi u v) (hv : v ∈ V(G)) : v ∈ U := by
  have := Seg.blk_eq c.hV c.hE hs
  rw [c.blk_eq hU hu] at this
  exact this ▸ mem_blk_self c.hV c.hE hv

/-! ### Instances of confinement -/

lemma conf_early {A : Set (Set α)} (hA : IsTreeComp (quotient G) I A) {a b : β}
    (ha : a ∈ edgesIn (quotient G) I A) (hb : b ∈ edgesIn (quotient G) I A)
    (hab : causalQ G ℓ a b) {U : Set α} (haU : (quotient G).Inc a U) (hbU : (quotient G).Inc b U) :
    ∃ pa pb, IsPort G U a pa ∧ IsPort G U b pb ∧ Seg G ℓ (some a) (some b) pa pb :=
  confinement c.hV c.hE hab haU hbU (c.q.acyc_tree hA) ha hb
    (fun d h1 h2 => c.q.mid_early hA.1 ha hb d h1 h2)

lemma conf_future {a b : β} (ha : a ∈ E(quotient G) \ I) (hb : b ∈ E(quotient G) \ I)
    (hab : causalQ G ℓ a b) {U : Set α} (haU : (quotient G).Inc a U) (hbU : (quotient G).Inc b U) :
    ∃ pa pb, IsPort G U a pa ∧ IsPort G U b pb ∧ Seg G ℓ (some a) (some b) pa pb :=
  confinement c.hV c.hE hab haU hbU c.q.acyc_F ha hb
    (fun d h1 _ => c.q.mid_future ha d h1)

lemma conf_eF {b : β} (hb : b ∈ E(quotient G) \ I) (heb : causalQ G ℓ e b) {U : Set α}
    (heU : (quotient G).Inc e U) (hbU : (quotient G).Inc b U) :
    ∃ pa pb, IsPort G U e pa ∧ IsPort G U b pb ∧ Seg G ℓ (some e) (some b) pa pb :=
  confinement c.hV c.hE heb heU hbU c.q.acyc_eF (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hb)
    (fun d h1 _h2 => Set.mem_insert_of_mem _ (c.q.mid_eF d h1 h1.2.1))

/-! ### Connectivity at the thresholds -/

/-- `J_{x_i}^-(e)` is connected: every vertex of the root block `r` reaches the port of `e` before
`e`. -/
theorem tc_below {r r' : Set α} (hr : r = x0 ∨ r = x1) (hr' : r' = x0 ∨ r' = x1) (hrr : r ≠ r')
    {a : α} (ha : IsPort G r e a) : ∀ z ∈ r, Reach G (Below G ℓ r e) z a := by
  intro z hz
  have hrV := c.root_V hr
  have hr'V := c.root_V hr'
  obtain ⟨a', ha'⟩ := c.exists_e_port hr'
  have hzV : z ∈ V(G) := c.sub_V hrV hz
  have ha'V : a' ∈ V(G) := ha'.2.vertex_mem
  obtain ⟨ts, hts⟩ := exists_xr c.hV c.hE c.hℓ hzV ha'V
  have hT := XR.incTrail c.hV c.hE hts
  rw [c.blk_eq hrV hz, c.blk_eq hr'V ha'.1] at hT
  obtain ⟨a0, ts', rfl, ha0⟩ := c.q.trail_roots_first hr hr' hrr hT
  obtain ⟨x, y, hseg, hl, hQ, -⟩ := XR.split (ts1 := []) (t := a0) (ts2 := ts') hts
  have hseg' : Seg G ℓ none (some a0) z x := hseg
  have hxU : x ∈ r := c.seg_blk_mem hrV hz hseg' hl.left_mem
  by_cases hae : a0 = e
  · subst hae
    have : x = a := isPort_unique c.hV c.hE hrV hQ ⟨hxU, hl.inc_left⟩ ha
    subst this
    exact c.seg_reach hrV hz hseg' (fun d hd => hd)
  · have hlt : causalQ G ℓ a0 e := c.q.hC.e_max a0 ha0 hae
    have hinc1 : (quotient G).Inc a0 r := by
      have := inc_quotient hQ hl.inc_left
      rwa [c.blk_eq hrV hxU] at this
    have hinc2 : (quotient G).Inc e r := c.e_inc_root hr
    obtain ⟨pa, pb, hpa, hpb, hs2⟩ := c.conf_early c.q.hC.tree ha0 c.q.hC.e_mem hlt hinc1 hinc2
    have h1 : pa = x := isPort_unique c.hV c.hE hrV hQ hpa ⟨hxU, hl.inc_left⟩
    have h2 : pb = a := isPort_unique c.hV c.hE hrV c.e_mem_Q hpb ha
    subst h1 h2
    have hxs : pa ∈ r := hxU
    refine (c.seg_reach hrV hz hseg' ?_).trans' (c.seg_reach hrV hxs hs2 ?_)
    · intro d hd
      exact ⟨fun a1 h => by simp at h, fun b1 h => by
        obtain rfl := Option.some.inj h
        exact causal_trans (hd.2 a0 rfl) hlt.2.2⟩
    · intro d hd
      exact ⟨fun a1 h => by simp at h, hd.2⟩

/-- `J_U^+(f)` is connected for a future call `f` joining `U ∈ Y` to a root. -/
theorem tc_future {U r : Set α} (hU : U ∈ Y) (hr : r = x0 ∨ r = x1) {f : β}
    (hf : f ∈ E(quotient G) \ I) (hfl : (quotient G).IsLink f U r) {pf : α}
    (hpf : IsPort G U f pf) : ∀ z ∈ U, Reach G (Above G ℓ U f) pf z := by
  intro z hz
  have hUV := c.Y_V hU
  have hrV := c.root_V hr
  obtain ⟨a, ha⟩ := c.exists_e_port hr
  have hzV : z ∈ V(G) := c.sub_V hUV hz
  have haV : a ∈ V(G) := ha.2.vertex_mem
  obtain ⟨ts, hts⟩ := exists_xr c.hV c.hE c.hℓ haV hzV
  have hT := XR.incTrail c.hV c.hE hts
  rw [c.blk_eq hrV ha.1, c.blk_eq hUV hz] at hT
  have hrX : r ∈ X := by rcases hr with rfl | rfl; exacts [c.q.x0_mem, c.q.x1_mem]
  obtain ⟨L, t, m, rfl, -, hmt, htF⟩ := c.q.trail_X_Y hrX hU hT
  obtain ⟨x, y, -, hl, hQ, hseg⟩ := XR.split hts
  have hseg' : Seg G ℓ (some t) none y z := hseg
  have hyU : y ∈ U := by
    have := Seg.blk_eq c.hV c.hE hseg'
    rw [c.blk_eq hUV hz] at this
    exact this ▸ mem_blk_self c.hV c.hE hl.right_mem
  have hty : IsPort G U t y := ⟨hyU, hl.inc_right⟩
  have htinc : (quotient G).Inc t U := by
    have := inc_quotient hQ hl.inc_right
    rwa [c.blk_eq hUV hyU] at this
  rcases c.q.outward hUV (c.q.Y_ne_x0 hU) (c.q.Y_ne_x1 hU) hf hfl hr htF htinc with rfl | hft
  · have : y = pf := isPort_unique c.hV c.hE hUV hQ hty hpf
    subst this
    exact c.seg_reach hUV hyU hseg' (fun d hd => hd)
  · obtain ⟨pa, pb, hpa, hpb, hs2⟩ := c.conf_future hf htF hft hfl.inc_left htinc
    have h1 : pa = pf := isPort_unique c.hV c.hE hUV hf.1 hpa hpf
    have h2 : pb = y := isPort_unique c.hV c.hE hUV hQ hpb hty
    subst h1 h2
    refine (c.seg_reach hUV hpa.1 hs2 ?_).trans' (c.seg_reach hUV hyU hseg' ?_)
    · intro d hd
      exact ⟨hd.1, fun b1 h => by simp at h⟩
    · intro d hd
      exact ⟨fun a1 h => by
        obtain rfl := Option.some.inj h
        exact causal_trans hft.2.2 (hd.1 t rfl), fun b1 h => by simp at h⟩

end PCtx

end Lax630294Proofs.Ports
