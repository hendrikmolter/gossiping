import Lax630294Proofs.PortsThreshold

/-!
# Good future calls and filtered routes (`lem:characterization-root-good-routes`)

A future call `t` joining a vertex of `Y` to the root block `r` is *good at `r`* if the port of `e`
in `r` and the port of `t` in `r` are joined by a path in `J_r^+(e)` whose deletion leaves
`J_r^+(e)` connected.  A *filtered route* with root block `r` is a route from a vertex of a block
in `Y` to a vertex of `r` whose last external call is good at `r`.

DEVIATION: filtered routes are arbitrary increasing routes (not necessarily paths); loop erasure
is never needed since only the external skeleton and connectivity of the internal segments matter.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- `t` is *good at the root block `r`*. -/
def Good (G : Graph α β) (ℓ : β → ℕ) (e : β) (r : Set α) (t : β) : Prop :=
  ∃ a p P, IsPort G r e a ∧ IsPort G r t p ∧ P ⊆ Above G ℓ r e ∧ IsPathSet G a p P ∧
    ∀ x ∈ r, ∀ y ∈ r, Reach G (Above G ℓ r e \ P) x y

/-- A *filtered route* with root block `r` from `u` to `v` with external calls `L ++ [t]`, the last
call `t` being good at `r`. -/
def Filt (G : Graph α β) (ℓ : β → ℕ) (e : β) (r : Set α) (u v : α) (L : List β) (t : β) : Prop :=
  XR G ℓ none none u v (L ++ [t]) ∧ v ∈ r ∧ Good G ℓ e r t

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

/-- **`lem:characterization-root-good-routes`.** -/
theorem root_good_routes {U r : Set α} (hU : U ∈ Y) (hr : r = x0 ∨ r = x1) {u : α} (hu : u ∈ U) :
    ∃ v L t, Filt G ℓ e r u v L t := by
  have hUV := c.Y_V hU
  have hrV := c.root_V hr
  have huV : u ∈ V(G) := c.sub_V hUV hu
  have hrfin : r.Finite := c.hV.subset (c.sub_V hrV)
  have : Finite r := hrfin.to_subtype
  obtain ⟨a, ha⟩ := c.exists_e_port hr
  have hex : ∀ w : r, ∃ (L : List β) (t : β) (y : α), XR G ℓ none none u w.1 (L ++ [t]) ∧
      t ∈ E(quotient G) \ I ∧ (quotient G).Inc t r ∧ IsPort G r t y ∧
      Seg G ℓ (some t) none y w.1 := by
    intro w
    have hwV : w.1 ∈ V(G) := c.sub_V hrV w.2
    obtain ⟨ts, hts⟩ := exists_xr c.hV c.hE c.hℓ huV hwV
    have hT := XR.incTrail c.hV c.hE hts
    rw [c.blk_eq hUV hu, c.blk_eq hrV w.2] at hT
    obtain ⟨L, t, V, rfl, -, htF, htl, -, -⟩ := c.q.trail_Y_root hU hr hT
    obtain ⟨x, y, -, hl, hQ, hseg⟩ := XR.split hts
    have hyU : y ∈ r := by
      have := Seg.blk_eq c.hV c.hE (hseg : Seg G ℓ (some t) none y w.1)
      rw [c.blk_eq hrV w.2] at this
      exact this ▸ mem_blk_self c.hV c.hE hl.right_mem
    exact ⟨L, t, y, hts, htF, htl.inc_right, ⟨hyU, hl.inc_right⟩, hseg⟩
  choose L t y hts htF htinc hyp hseg using hex
  have hJB : Above G ℓ r e ⊆ Ins G r := Set.inter_subset_left
  have hlt : ∀ w : r, causalQ G ℓ e (t w) := fun w => c.q.e_lt_F (htF w)
  obtain ⟨i, P, hPJ, hpath, hcon⟩ := antichain_selection (G := G) hrfin hJB ha.1
    (R := fun p q => causal G ℓ q p) (fun d => causal_irrefl d)
    (fun _ _ _ h1 h2 => causal_trans h2 h1) t y (fun w => (hyp w).1)
    (by
      intro x hx
      refine ⟨⟨x, hx⟩, ?_⟩
      have h := c.seg_reach hrV (hyp ⟨x, hx⟩).1 (hseg ⟨x, hx⟩) (fun d hd => hd)
      refine reach_mono (fun d hd => ⟨⟨hd.1, ?_⟩, hd.2.1 _ rfl⟩) h.symm'
      exact ⟨fun a1 h' => by
        obtain rfl := Option.some.inj h'
        exact causal_trans (hlt ⟨x, hx⟩).2.2 (hd.2.1 _ rfl), fun b1 h' => by simp at h'⟩)
    (by
      intro w
      obtain ⟨pa, pb, hpa, hpb, hs2⟩ := c.conf_eF (htF w) (hlt w) (c.e_inc_root hr) (htinc w)
      have h1 : pa = a := isPort_unique c.hV c.hE hrV c.e_mem_Q hpa ha
      have h2 : pb = y w := isPort_unique c.hV c.hE hrV (htF w).1 hpb (hyp w)
      subst h1 h2
      have h := c.seg_reach hrV hpa.1 hs2 (fun d hd => hd)
      refine reach_mono (fun d hd => ⟨⟨hd.1, hd.2.1, fun b1 h' => by simp at h'⟩, hd.2.2 _ rfl⟩)
        h.symm')
    (by
      intro i j hij
      have hQ : causalQ G ℓ (t j) (t i) := ⟨(htF j).1, (htF i).1, hij⟩
      obtain ⟨pa, pb, hpa, hpb, hs2⟩ := c.conf_future (htF j) (htF i) hQ (htinc j) (htinc i)
      have h1 : pa = y j := isPort_unique c.hV c.hE hrV (htF j).1 hpa (hyp j)
      have h2 : pb = y i := isPort_unique c.hV c.hE hrV (htF i).1 hpb (hyp i)
      subst h1 h2
      have h := c.seg_reach hrV hpa.1 hs2 (fun d hd => hd)
      refine reach_mono (fun d hd => ⟨⟨hd.1, ⟨fun a1 h' => ?_, fun b1 h' => by simp at h'⟩⟩,
        hd.2.2 _ rfl, hd.2.1 _ rfl⟩) h.symm'
      obtain rfl := Option.some.inj h'
      exact causal_trans (hlt j).2.2 (hd.2.1 _ rfl))
  exact ⟨i.1, L i, t i, hts i, i.2, a, y i, P, ha, hyp i, hPJ, hpath, hcon⟩

/-- Shape of a filtered route starting in `Y`: an early path in `Y` followed by the good call. -/
theorem filt_shape {U r : Set α} (hU : U ∈ Y) (hr : r = x0 ∨ r = x1) {u v : α} {L : List β}
    {t : β} (hu : u ∈ U) (hf : Filt G ℓ e r u v L t) :
    ∃ V, V ∈ Y ∧ (quotient G).IsLink t V r ∧ t ∈ E(quotient G) \ I ∧
      (∀ g ∈ L, g ∈ edgesIn (quotient G) I Y) ∧ IncTrail (quotient G) (causalQ G ℓ) U V L := by
  have hUV := c.Y_V hU
  have hrV := c.root_V hr
  have hT := XR.incTrail c.hV c.hE hf.1
  rw [c.blk_eq hUV hu, c.blk_eq hrV hf.2.1] at hT
  obtain ⟨L', t', V, heq, hL', ht'F, hl, hVY, hT'⟩ := c.q.trail_Y_root hU hr hT
  obtain ⟨hLL, htt⟩ := List.append_inj' heq rfl
  have htt' : t = t' := by simpa using htt
  subst hLL htt'
  exact ⟨V, hVY, hl, ht'F, hL', hT'⟩

/-- **`lem:characterization-internal-threshold-connectivity`**, the claim that `J^+_{B_{x_i}}(e)`
is connected.  DEVIATION: the paper proves this with an original route from `a_{1-i}` into the
root block; here it is read off `root_good_routes`, since a good last call comes with a path `P`
such that `J^+_{B_{x_i}}(e)` minus `P` is still connected. -/
theorem tc_above {r : Set α} (hr : r = x0 ∨ r = x1) :
    ∀ x ∈ r, ∀ y ∈ r, Reach G (Above G ℓ r e) x y := by
  obtain ⟨U, hU⟩ := c.q.hYc.1
  have hUim : U ∈ blk G '' V(G) := c.Y_V hU
  obtain ⟨z, hz, rfl⟩ := hUim
  obtain ⟨v, L, t, -, -, hgood⟩ := c.root_good_routes hU hr (mem_blk_self c.hV c.hE hz)
  obtain ⟨a, p, P, -, -, -, -, hconn⟩ := hgood
  intro x hx y hy
  exact reach_mono Set.sdiff_subset (hconn x hx y hy)


end PCtx

end Lax630294Proofs.Ports
