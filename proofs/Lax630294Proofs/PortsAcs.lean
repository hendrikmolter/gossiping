import Lax630294Proofs.PortsClosed
import Lax630294Proofs.PortsDigraph

/-!
# Minimal closed sets supply internal returns (`lem:characterization-actual-closed-set`)
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

/-- The return data at a vertex `U` of a minimal closed set, for a call `k` of `Y[S]` at `U` that
is maximal among those: the next external call of a witnessing route is a good future call. -/
theorem acs_core {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {U : Set α} (hU : U ∈ S)
    {k : β} (hkS : k ∈ edgesIn (quotient G) I S) (hkU : (quotient G).Inc k U)
    (hmax : ∀ k' ∈ edgesIn (quotient G) I S, (quotient G).Inc k' U → ¬ causalQ G ℓ k k') :
    ∃ (i : Bool) (f : β), f ∈ E(quotient G) \ I ∧ (quotient G).IsLink f U (rootOf x0 x1 i) ∧
      Good G ℓ e (rootOf x0 x1 i) f ∧ causalQ G ℓ k f ∧
      ∃ pa pf, IsPort G U k pa ∧ IsPort G U f pf ∧ Seg G ℓ (some k) (some f) pa pf := by
  classical
  have hSY : S ⊆ Y := hS.1.2.1
  let E1 : Set β := edgesIn (quotient G) I S
  have hE1Y : E1 ⊆ edgesIn (quotient G) I Y := fun d hd => ⟨hd.1, hd.2.mono hSY⟩
  have hE1ins : E1 ⊆ Ins (quotient G) S := fun d hd => hd.2
  have hac1 : Acyc (quotient G) E1 := c.q.acyc_Y.mono hE1Y
  obtain ⟨W', hkl⟩ := hkU
  have hW'S : W' ∈ S := (hkS.2.ends_mem hkl).2
  let S' : Set (Set α) := {W | Reach (quotient G) (E1 \ {k}) W' W}
  have hS'S : S' ⊆ S := fun W hW => reach_in_set (fun d hd => hE1ins hd.1) hW'S hW
  have hUS' : U ∉ S' := fun h => hac1 k hkS U W' hkl h.symm'
  have hS'cv : Cvx G I S' := by
    intro W1 h1 W2 h2
    have hT : ∀ d ∈ E1 \ {k}, ∀ x y, (quotient G).IsLink d x y → x ∈ S' → y ∈ S' :=
      fun d hd x y hl hx => hx.tail ⟨d, hd, hl⟩
    have r1 := reach_restrict hT (show W' ∈ S' from reach_refl) h1
    have r2 := reach_restrict hT (show W' ∈ S' from reach_refl) h2
    have hsub : {d | d ∈ E1 \ {k} ∧ d ∈ Ins (quotient G) S'} ⊆ edgesIn (quotient G) I S' :=
      fun d hd => ⟨hd.1.1.1, hd.2⟩
    exact (reach_mono hsub r1.2).symm'.trans' (reach_mono hsub r2.2)
  have hSY' : S' ⊆ Y := hS'S.trans hSY
  have hexit : ∃ W ∈ S', ∃ i V, Nb G ℓ e (rootOf x0 x1 i) W V ∧ V ∉ S' := by
    by_contra hcon
    push Not at hcon
    have hcl : ClosedSet G ℓ e x0 x1 Y S' := ⟨⟨W', reach_refl⟩, hSY', fun W hW i V hNb =>
      hcon W hW i V hNb⟩
    exact hUS' ((hS.2.2 S' hS'S hcl hS'cv) ▸ hU)
  obtain ⟨W, hWS', i, V, hNb, hVn⟩ := hexit
  obtain ⟨u, hu, v, L, t, hf, hl⟩ := hNb
  have hWS : W ∈ S := hS'S hWS'
  have hWY : W ∈ Y := hSY hWS
  have hVS : V ∈ S := hS.1.2.2 W hWS i V ⟨u, hu, v, L, t, hf, hl⟩
  obtain ⟨V', hV'Y, hl', htF, hLY, htr⟩ := c.filt_shape hWY (rootOf_or x0 x1 i) hu hf
  have hVV' : V = V' := c.link_root_unique hV'Y (rootOf_or x0 x1 i) hl hl'
  have htr' : IncTrail (quotient G) (causalQ G ℓ) W V L := hVV' ▸ htr
  have hcvS : ∀ x ∈ S, ∀ y ∈ S,
      Reach (quotient G) (edgesIn (quotient G) I Y ∩ Ins (quotient G) S) x y :=
    fun x hx y hy => reach_mono (fun d hd => ⟨hE1Y hd, hE1ins hd⟩) (hS.2.1 x hx y hy)
  have hnd : L.Nodup := IncTrail.nodup (P := causalQ G ℓ)
    (fun _ _ _ h1 h2 => causalQ_trans h1 h2) (fun d => causalQ_irrefl d) htr'
  have hLins : ∀ g ∈ L, g ∈ Ins (quotient G) S :=
    trail_stay c.q.acyc_Y hcvS htr' hLY hnd hWS hVS
  have hLE1 : ∀ g ∈ L, g ∈ E1 := fun g hg => ⟨(hLY g hg).1, hLins g hg⟩
  obtain ⟨es1, es2, hLeq, h1, h2⟩ := trail_exit hac1 hkl.symm hkS (fun x => Iff.rfl) htr' hLE1
    hWS' hVn
  have hes2 : es2 = [] := by
    by_contra hne
    obtain ⟨g, es2', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨w, hgl, -, -⟩ := h2.mem_cons_inv
    have hgL : g ∈ L := by rw [hLeq]; simp
    have hpw := IncTrail.pairwise (P := causalQ G ℓ) (fun _ _ _ h1 h2 => causalQ_trans h1 h2) htr'
    rw [hLeq] at hpw
    have hpw2 := (List.pairwise_append.1 hpw).2.1
    have hkg : causalQ G ℓ k g := (List.pairwise_cons.1 hpw2).1 g (by simp)
    exact hmax g (hLE1 g hgL) hgl.inc_left hkg
  subst hes2
  have hUV : U = V := by cases h2; rfl
  rw [← hUV] at hl
  have hX : XR G ℓ none none u v (es1 ++ k :: [t]) := by
    have := hf.1
    rw [hLeq] at this
    simpa using this
  obtain ⟨x, y, hXs, hxy, hkQ, hrest⟩ := XR.split (ts1 := es1) (t := k) (ts2 := [t]) hX
  obtain ⟨x', y', hseg, hxy', htQ, hlast⟩ := hrest
  have hrV := c.root_V (rootOf_or x0 x1 i)
  have hrX : rootOf x0 x1 i ∈ X := by
    rcases rootOf_or x0 x1 i with h | h <;> rw [h]
    exacts [c.q.x0_mem, c.q.x1_mem]
  have hy'blk : blk G y' = rootOf x0 x1 i := by
    have := Seg.blk_eq c.hV c.hE (hlast : Seg G ℓ (some t) none y' v)
    rw [← this]
    exact c.blk_eq hrV hf.2.1
  have hQt : (quotient G).IsLink t (blk G x') (blk G y') :=
    quotient_isLink.2 ⟨x', y', hxy', rfl, rfl, contract_ext (G := G) (f := blk G) htQ hxy'⟩
  have hbx' : blk G x' = U := by
    rw [hy'blk] at hQt
    rcases hQt.eq_and_eq_or_eq_and_eq hl with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd (h ▸ hrX) (c.q.mem_Y_not_X (hSY hU))
  have hyblk : blk G y = U := (Seg.blk_eq c.hV c.hE hseg).symm.trans hbx'
  refine ⟨i, t, htF, hl, hf.2.2, ⟨hkQ, htQ, hseg.1 k t rfl rfl⟩, y, x',
    ⟨hyblk ▸ mem_blk_self c.hV c.hE hxy.right_mem, hxy.inc_right⟩,
    ⟨hbx' ▸ mem_blk_self c.hV c.hE hxy'.left_mem, hxy'.inc_left⟩, hseg⟩

/-- **`lem:characterization-actual-closed-set`**: every vertex `U` of a minimal closed set has a
future call `f_U` to a root (good at that root) and an internal return from the port of every
call `h` of `Y[S]` at `U` to the port of `f_U`, strictly between `h` and `f_U`. -/
theorem acs {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {U : Set α} (hU : U ∈ S) :
    ∃ (i : Bool) (f : β), f ∈ E(quotient G) \ I ∧ (quotient G).IsLink f U (rootOf x0 x1 i) ∧
      Good G ℓ e (rootOf x0 x1 i) f ∧
      ∀ h ∈ edgesIn (quotient G) I S, (quotient G).Inc h U → causalQ G ℓ h f ∧
        ∃ pa pf, IsPort G U h pa ∧ IsPort G U f pf ∧ Seg G ℓ (some h) (some f) pa pf := by
  classical
  have hSY : S ⊆ Y := hS.1.2.1
  have hUY : U ∈ Y := hSY hU
  have hUV := c.Y_V hUY
  let E1 : Set β := edgesIn (quotient G) I S
  have hE1Y : E1 ⊆ edgesIn (quotient G) I Y := fun d hd => ⟨hd.1, hd.2.mono hSY⟩
  let K : Set β := {k | k ∈ E1 ∧ (quotient G).Inc k U}
  have hKE : K ⊆ E(quotient G) := fun k hk => hk.2.edge_mem
  have hKne : K.Nonempty := by
    obtain ⟨U1, W1, hU1, hW1, hne⟩ := c.two_le hS.1
    by_cases h1 : U1 = U
    · subst h1
      obtain ⟨k, hk, hkU⟩ := PCtx.exists_edge_at hS.2.1 hU hW1 hne
      exact ⟨k, hk, hkU⟩
    · obtain ⟨k, hk, hkU⟩ := PCtx.exists_edge_at hS.2.1 hU hU1 (Ne.symm h1)
      exact ⟨k, hk, hkU⟩
  obtain ⟨k0, hk0, hk0max⟩ := c.q.hA.exists_max hKE hKne
  obtain ⟨i0, f0, hf0, hl0, hg0, -⟩ := c.acs_core hS hU hk0.1 hk0.2
    (fun k' hk' hk'U => hk0max k' ⟨hk', hk'U⟩)
  refine ⟨i0, f0, hf0, hl0, hg0, fun h hhE hhU => ?_⟩
  -- a maximal call above `h`
  let T2 : Set β := {k | k ∈ K ∧ (k = h ∨ causalQ G ℓ h k)}
  obtain ⟨k, hkT2, hkmax⟩ := c.q.hA.exists_max (T := T2) (fun k hk => hKE hk.1)
    ⟨h, ⟨hhE, hhU⟩, Or.inl rfl⟩
  have hkmaxK : ∀ k' ∈ E1, (quotient G).Inc k' U → ¬ causalQ G ℓ k k' := by
    intro k' hk'E hk'U hkk'
    refine hkmax k' ⟨⟨hk'E, hk'U⟩, Or.inr ?_⟩ hkk'
    rcases hkT2.2 with rfl | hhk
    · exact hkk'
    · exact causalQ_trans hhk hkk'
  obtain ⟨i', f', hf', hl', hg', hkf', pa, pf, hpa, hpf, hseg⟩ :=
    c.acs_core hS hU hkT2.1.1 hkT2.1.2 hkmaxK
  obtain ⟨hii, hff⟩ := c.f_unique hf0 hl0 hf' hl'
  subst hii hff
  rcases hkT2.2 with rfl | hhk
  · exact ⟨hkf', pa, pf, hpa, hpf, hseg⟩
  · obtain ⟨pa', pb', hpa', hpb', hseg'⟩ := c.conf_early c.q.hY (hE1Y hhE) (hE1Y hkT2.1.1) hhk
      hhU hkT2.1.2
    have hpb : pb' = pa := isPort_unique c.hV c.hE hUV (c.q.hA.mem_right hhk) hpb' hpa
    subst hpb
    exact ⟨causalQ_trans hhk hkf', pa', pf, hpa', hpf, Seg.chain c.hV c.hE hseg' hseg⟩

end PCtx

end Lax630294Proofs.Ports
