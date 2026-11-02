import Lax630294Proofs.PortsAcs

/-!
# Safe first edges, the arc digraph and same-index rerouting
(`lem:characterization-safe-first-edges`, `lem:characterization-same-index-rerouting`)
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

/-- The data of `lem:characterization-actual-closed-set` at the vertices of `S`: the root index
`ci U` and the future call `fi U = f_U`. -/
structure AcsData (G : Graph α β) (ℓ : β → ℕ) (e : β) (I : Set β) (x0 x1 : Set α)
    (S : Set (Set α)) (ci : Set α → Bool) (fi : Set α → β) : Prop where
  fut : ∀ U ∈ S, fi U ∈ E(quotient G) \ I ∧
    (quotient G).IsLink (fi U) U (rootOf x0 x1 (ci U)) ∧ Good G ℓ e (rootOf x0 x1 (ci U)) (fi U)
  ret : ∀ U ∈ S, ∀ h ∈ edgesIn (quotient G) I S, (quotient G).Inc h U →
    causalQ G ℓ h (fi U) ∧ ∃ pa pf, IsPort G U h pa ∧ IsPort G U (fi U) pf ∧
      Seg G ℓ (some h) (some (fi U)) pa pf

/-- A path between the ports of `h` and `f` in `J_U^-(f)` whose deletion leaves `J_U^-(f)`
connected. -/
def ArcPath (G : Graph α β) (ℓ : β → ℕ) (U : Set α) (h f : β) : Prop :=
  ∃ pa pf P, IsPort G U h pa ∧ IsPort G U f pf ∧ IsPathSet G pa pf P ∧ P ⊆ Below G ℓ U f ∧
    ∀ x ∈ U, ∀ y ∈ U, Reach G (Below G ℓ U f \ P) x y

/-- A filtered route with root block `r` starting in `U` whose first external call is `h`. -/
def FirstEdge (G : Graph α β) (ℓ : β → ℕ) (e : β) (r U : Set α) (h : β) : Prop :=
  ∃ u ∈ U, ∃ v L t L', Filt G ℓ e r u v L t ∧ L = h :: L'

/-- The arc `U → V` of the digraph `D` of the paper. -/
def Arc (G : Graph α β) (ℓ : β → ℕ) (e : β) (I : Set β) (x0 x1 : Set α) (S : Set (Set α))
    (ci : Set α → Bool) (fi : Set α → β) (U V : Set α) : Prop :=
  ∃ h, h ∈ edgesIn (quotient G) I S ∧ (quotient G).IsLink h U V ∧
    FirstEdge G ℓ e (rootOf x0 x1 (!(ci U))) U h ∧ ArcPath G ℓ U h (fi U)

namespace PCtx

variable {I : Set β} {X Y : Set (Set α)} {e : β} {x0 x1 : Set α}
variable (c : PCtx G ℓ I X Y e x0 x1)
include c

lemma exists_acsData {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) :
    ∃ ci fi, AcsData G ℓ e I x0 x1 S ci fi := by
  classical
  have : Nonempty β := ⟨e⟩
  choose! ci fi hf1 hf2 hf3 hret using (fun U (hU : U ∈ S) => c.acs hS hU)
  exact ⟨ci, fi, ⟨fun U hU => ⟨hf1 U hU, hf2 U hU, hf3 U hU⟩, hret⟩⟩

/-- A trail from `U ∈ S` to `V ∈ S` along calls of `Y` uses only calls of `Y[S]`. -/
lemma trail_E1 {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {U V : Set α} {L : List β}
    (hU : U ∈ S) (hV : V ∈ S) (htr : IncTrail (quotient G) (causalQ G ℓ) U V L)
    (hLY : ∀ g ∈ L, g ∈ edgesIn (quotient G) I Y) :
    ∀ g ∈ L, g ∈ edgesIn (quotient G) I S := by
  have hSY : S ⊆ Y := hS.1.2.1
  have hE1Y : edgesIn (quotient G) I S ⊆ edgesIn (quotient G) I Y :=
    fun d hd => ⟨hd.1, hd.2.mono hSY⟩
  have hcvS : ∀ x ∈ S, ∀ y ∈ S,
      Reach (quotient G) (edgesIn (quotient G) I Y ∩ Ins (quotient G) S) x y :=
    fun x hx y hy => reach_mono (fun d hd => ⟨hE1Y hd, hd.2⟩) (hS.2.1 x hx y hy)
  have hnd : L.Nodup := IncTrail.nodup (P := causalQ G ℓ)
    (fun _ _ _ h1 h2 => causalQ_trans h1 h2) (fun d => causalQ_irrefl d) htr
  have hLins := trail_stay c.q.acyc_Y hcvS htr hLY hnd hU hV
  exact fun g hg => ⟨(hLY g hg).1, hLins g hg⟩

/-- Shape of a filtered route with the root index opposite to `ci U`. -/
lemma filt_early {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {ci : Set α → Bool}
    {fi : Set α → β} (hd : AcsData G ℓ e I x0 x1 S ci fi) {U : Set α} (hU : U ∈ S) {u v : α}
    {L : List β} {t : β} (hu : u ∈ U) (hF : Filt G ℓ e (rootOf x0 x1 (!(ci U))) u v L t) :
    ∃ V, V ∈ S ∧ (quotient G).IsLink t V (rootOf x0 x1 (!(ci U))) ∧ t ∈ E(quotient G) \ I ∧
      (∀ g ∈ L, g ∈ edgesIn (quotient G) I S) ∧
      IncTrail (quotient G) (causalQ G ℓ) U V L ∧ L ≠ [] := by
  have hUY : U ∈ Y := hS.1.2.1 hU
  obtain ⟨V, hVY, hl, htF, hLY, htr⟩ := c.filt_shape hUY (rootOf_or x0 x1 _) hu hF
  have hVS : V ∈ S := hS.1.2.2 U hU _ V ⟨u, hu, v, L, t, hF, hl⟩
  refine ⟨V, hVS, hl, htF, c.trail_E1 hS hU hVS htr hLY, htr, ?_⟩
  rintro rfl
  have hUV : U = V := by cases htr; rfl
  rw [← hUV] at hl
  obtain ⟨hfF, hfl, -⟩ := hd.fut U hU
  exact c.no_other_root hfF hfl htF hl

/-- `lem:characterization-safe-first-edges` (with prescribed candidate routes). -/
theorem sfe {S : Set (Set α)} (hS : MinClosed G ℓ e I x0 x1 Y S) {ci : Set α → Bool}
    {fi : Set α → β} (hd : AcsData G ℓ e I x0 x1 S ci fi) {U : Set α} (hU : U ∈ S)
    (Φ : β → Prop)
    (hfam : ∀ u ∈ U, ∃ v L t h L', Filt G ℓ e (rootOf x0 x1 (!(ci U))) u v L t ∧ L = h :: L' ∧
      Φ h) :
    ∃ h V, Φ h ∧ h ∈ edgesIn (quotient G) I S ∧ (quotient G).IsLink h U V ∧
      FirstEdge G ℓ e (rootOf x0 x1 (!(ci U))) U h ∧ ArcPath G ℓ U h (fi U) := by
  classical
  have hSY : S ⊆ Y := hS.1.2.1
  have hUY := hSY hU
  have hUV := c.Y_V hUY
  have hE1Y : edgesIn (quotient G) I S ⊆ edgesIn (quotient G) I Y :=
    fun d hd => ⟨hd.1, hd.2.mono hSY⟩
  obtain ⟨hfF, hfl, -⟩ := hd.fut U hU
  obtain ⟨pf0, hpf0⟩ := exists_isPort c.hV c.hE hUV hfl.inc_left
  have hUfin : U.Finite := c.hV.subset (c.sub_V hUV)
  have : Finite U := hUfin.to_subtype
  have hex : ∀ w : U, ∃ (h : β) (x : α), h ∈ edgesIn (quotient G) I S ∧ (quotient G).Inc h U ∧
      Φ h ∧ IsPort G U h x ∧ Seg G ℓ none (some h) w.1 x ∧
      FirstEdge G ℓ e (rootOf x0 x1 (!(ci U))) U h := by
    intro w
    obtain ⟨v, L, t, h, L', hF, hL, hΦ⟩ := hfam w.1 w.2
    obtain ⟨V, hVS, hl, htF, hLS, htr, hLne⟩ := c.filt_early hS hd hU w.2 hF
    have hhS := hLS h (by rw [hL]; simp)
    rw [hL] at htr
    obtain ⟨w', hhl, -, -⟩ := htr.mem_cons_inv
    have hX := hF.1
    rw [hL] at hX
    obtain ⟨x, y, hXs, hxy, -, -⟩ := XR.split (ts1 := []) (t := h) (ts2 := L' ++ [t]) hX
    have hxU : x ∈ U := by
      have := Seg.blk_eq c.hV c.hE (hXs : Seg G ℓ none (some h) w.1 x)
      rw [c.blk_eq hUV w.2] at this
      exact this ▸ mem_blk_self c.hV c.hE hxy.left_mem
    exact ⟨h, x, hhS, hhl.inc_left, hΦ, ⟨hxU, hxy.inc_left⟩, hXs,
      w.1, w.2, v, L, t, L', hF, hL⟩
  choose h x hhS hhU hΦ hxp hseg hfirst using hex
  have hret : ∀ w : U, causalQ G ℓ (h w) (fi U) ∧ Seg G ℓ (some (h w)) (some (fi U)) (x w) pf0 := by
    intro w
    obtain ⟨hc, pa, pf, hpa, hpf, hs⟩ := hd.ret U hU (h w) (hhS w) (hhU w)
    have h1 : pa = x w := isPort_unique c.hV c.hE hUV (c.q.hA.mem_left hc) hpa (hxp w)
    have h2 : pf = pf0 := isPort_unique c.hV c.hE hUV hfF.1 hpf hpf0
    subst h1 h2
    exact ⟨hc, hs⟩
  obtain ⟨i, P, hPJ, hpath, hcon⟩ := antichain_selection (G := G) hUfin
    (Set.inter_subset_left : Below G ℓ U (fi U) ⊆ Ins G U) hpf0.1
    (R := causal G ℓ) (fun d => causal_irrefl d) (fun _ _ _ h1 h2 => causal_trans h1 h2)
    h x (fun w => (hxp w).1)
    (by
      intro y hy
      refine ⟨⟨y, hy⟩, ?_⟩
      have hs := c.seg_reach hUV hy (hseg ⟨y, hy⟩) (fun d hd => hd)
      refine reach_mono (fun d hd => ⟨⟨hd.1, ?_⟩, hd.2.2 _ rfl⟩) hs
      exact ⟨fun a1 h' => by simp at h', fun b1 h' => by
        obtain rfl := Option.some.inj h'
        exact causal_trans (hd.2.2 _ rfl) (hret ⟨y, hy⟩).1.2.2⟩)
    (by
      intro w
      have hs := c.seg_reach hUV (hxp w).1 (hret w).2 (fun d hd => hd)
      exact reach_mono (fun d hd => ⟨⟨hd.1, ⟨fun a1 h' => by simp at h', hd.2.2⟩⟩,
        hd.2.1 _ rfl⟩) hs)
    (by
      intro i j hij
      have hQ : causalQ G ℓ (h i) (h j) :=
        ⟨c.q.hI.1 (hhS i).1, c.q.hI.1 (hhS j).1, hij⟩
      obtain ⟨pa, pb, hpa, hpb, hs2⟩ := c.conf_early c.q.hY (hE1Y (hhS i)) (hE1Y (hhS j)) hQ
        (hhU i) (hhU j)
      have h1 : pa = x i := isPort_unique c.hV c.hE hUV (c.q.hA.mem_left hQ) hpa (hxp i)
      have h2 : pb = x j := isPort_unique c.hV c.hE hUV (c.q.hA.mem_right hQ) hpb (hxp j)
      subst h1 h2
      have hs := c.seg_reach hUV hpa.1 hs2 (fun d hd => hd)
      exact reach_mono (fun d hd => ⟨⟨hd.1, ⟨fun a1 h' => by simp at h', fun b1 h' => by
        obtain rfl := Option.some.inj h'
        exact causal_trans (hd.2.2 _ rfl) (hret j).1.2.2⟩⟩, hd.2.1 _ rfl, hd.2.2 _ rfl⟩) hs)
  obtain ⟨V, hV⟩ := hhU i
  exact ⟨h i, V, hΦ i, hhS i, hV, hfirst i, x i, pf0, P, hxp i, hpf0, hpath.symm, hPJ, hcon⟩

end PCtx

end Lax630294Proofs.Ports
