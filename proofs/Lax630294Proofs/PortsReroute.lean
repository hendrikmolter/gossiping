import Lax630294Proofs.PortsArcs

/-!
# Same-index rerouting (`lem:characterization-same-index-rerouting`)
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

/-- Every vertex of `S` has an outgoing arc. -/
theorem arc_out {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {ci : Set α → Bool}
    {fi : Set α → β} (hd : AcsData G ℓ e I x0 x1 S ci fi) {U : Set α} (hU : U ∈ S) :
    ∃ V, Arc G ℓ e I x0 x1 S ci fi U V := by
  have hSY := hS.1.2.1
  obtain ⟨h, V, -, hhS, hl, hfirst, hpath⟩ := c.sfe hS hd hU (fun _ => True) (by
    intro u hu
    obtain ⟨v, L, t, hF⟩ := c.root_good_routes (hSY hU) (rootOf_or x0 x1 (!(ci U))) hu
    obtain ⟨-, -, -, -, -, -, hLne⟩ := c.filt_early hS hd hU hu hF
    obtain ⟨h, L', rfl⟩ := List.exists_cons_of_ne_nil hLne
    exact ⟨v, h :: L', t, h, L', hF, rfl, trivial⟩)
  exact ⟨V, h, hhS, hl, hfirst, hpath⟩

/-- **`lem:characterization-same-index-rerouting`.** -/
theorem reroute {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {ci : Set α → Bool}
    {fi : Set α → β} (hd : AcsData G ℓ e I x0 x1 S ci fi) {U V : Set α} (hU : U ∈ S)
    (hV : V ∈ S) (hc : ci U = ci V) (harc : Arc G ℓ e I x0 x1 S ci fi U V) :
    ∃ W, W ≠ U ∧ Arc G ℓ e I x0 x1 S ci fi V W := by
  classical
  have := c.q.hA.simple
  have hSY := hS.1.2.1
  obtain ⟨h, hhS, hhl, ⟨u, hu, v, L, t, L', hF, hL⟩, -⟩ := harc
  obtain ⟨V', hV'S, hl', htF, hLS, htr0, hLne⟩ := c.filt_early hS hd hU hu hF
  subst hL
  obtain ⟨w, hhl', htr', -⟩ := htr0.mem_cons_inv
  have hwV : w = V := hhl'.right_unique hhl
  rw [hwV] at htr'
  have hroot : rootOf x0 x1 (!(ci V)) = rootOf x0 x1 (!(ci U)) := by rw [hc]
  have hL'ne : L' ≠ [] := by
    intro hnil
    subst hnil
    have hVV : V = V' := by cases htr'; rfl
    rw [← hVV, ← hroot] at hl'
    obtain ⟨hfF, hfl, -⟩ := hd.fut V hV
    exact c.no_other_root hfF hfl htF hl'
  obtain ⟨h2, L'', rfl⟩ := List.exists_cons_of_ne_nil hL'ne
  obtain ⟨W, hh2l, -, -⟩ := htr'.mem_cons_inv
  have hh2S : h2 ∈ edgesIn (quotient G) I S := hLS h2 (by simp)
  have hpw := IncTrail.pairwise (P := causalQ G ℓ) (fun _ _ _ h1 h2 => causalQ_trans h1 h2) htr0
  have hhh2 : causalQ G ℓ h h2 := (List.pairwise_cons.1 hpw).1 h2 (by simp)
  have hh2h : h2 ≠ h := fun heq => causalQ_irrefl h (heq ▸ hhh2)
  -- the first two calls of the witnessing route
  have hX := hF.1
  obtain ⟨xu, yu, hXs, hxy, hhQ, hrest⟩ :=
    XR.split (ts1 := []) (t := h) (ts2 := h2 :: (L'' ++ [t])) hX
  obtain ⟨x', y', hseg2, hl2, hQ2, hrest2⟩ := hrest
  have hUV' := c.Y_V (hSY hU)
  have hVV' := c.Y_V (hSY hV)
  have hbxu : blk G xu = U := by
    have := Seg.blk_eq c.hV c.hE (hXs : Seg G ℓ none (some h) u xu)
    rw [c.blk_eq hUV' hu] at this
    exact this
  have hbyu : blk G yu = V := by
    have hq : (quotient G).IsLink h (blk G xu) (blk G yu) :=
      quotient_isLink.2 ⟨xu, yu, hxy, rfl, rfl, contract_ext (G := G) (f := blk G) hhQ hxy⟩
    rw [hbxu] at hq
    exact hq.right_unique hhl
  have hyuV : IsPort G V h yu := ⟨hbyu ▸ mem_blk_self c.hV c.hE hxy.right_mem, hxy.inc_right⟩
  -- the candidate family at `V`
  have hfam : ∀ w0 ∈ V, ∃ v1 L1 t1 h1 L1', Filt G ℓ e (rootOf x0 x1 (!(ci V))) w0 v1 L1 t1 ∧
      L1 = h1 :: L1' ∧ h1 ≠ h := by
    intro w0 hw0
    obtain ⟨v1, L1, t1, hF1⟩ := c.root_good_routes (hSY hV) (rootOf_or x0 x1 (!(ci V))) hw0
    obtain ⟨-, -, -, -, -, -, hL1ne⟩ := c.filt_early hS hd hV hw0 hF1
    obtain ⟨h1, L1', rfl⟩ := List.exists_cons_of_ne_nil hL1ne
    by_cases hh1 : h1 = h
    · subst hh1
      obtain ⟨xv, yv, hXs1, hxy1, hhQ1, -⟩ :=
        XR.split (ts1 := []) (t := h1) (ts2 := L1' ++ [t1]) hF1.1
      have hxvV : xv ∈ V := by
        have := Seg.blk_eq c.hV c.hE (hXs1 : Seg G ℓ none (some h1) w0 xv)
        rw [c.blk_eq hVV' hw0] at this
        exact this ▸ mem_blk_self c.hV c.hE hxy1.left_mem
      have hxy_eq : xv = yu :=
        isPort_unique c.hV c.hE hVV' hhQ1 ⟨hxvV, hxy1.inc_left⟩ hyuV
      subst hxy_eq
      have hnew : Seg G ℓ none (some h2) w0 x' := Seg.chain c.hV c.hE hXs1 hseg2
      refine ⟨v, h2 :: L'', t, h2, L'', ⟨⟨x', y', hnew, hl2, hQ2, hrest2⟩, ?_, ?_⟩, rfl, hh2h⟩
      · rw [hroot]; exact hF.2.1
      · rw [hroot]; exact hF.2.2
    · exact ⟨v1, h1 :: L1', t1, h1, L1', hF1, rfl, hh1⟩
  obtain ⟨h', W', hh'ne, hh'S, hh'l, hfirst, hpath⟩ := c.sfe hS hd hV (fun h' => h' ≠ h) hfam
  refine ⟨W', fun hWU => ?_, h', hh'S, hh'l, hfirst, hpath⟩
  subst hWU
  exact hh'ne (hh'l.eq hhl.symm)

end PCtx

end Lax630294Proofs.Ports
