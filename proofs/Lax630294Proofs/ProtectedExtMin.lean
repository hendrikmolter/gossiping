import Lax630294Proofs.ProtectedExtCycle

/-!
# Protected extension: the minimising tree has a forest as complement

`claim_bridge'` is the bridge property of a minimising tree of the class `Cls` (paper l. 4778-4790)
and `forest_of_min'` the induction step (paper l. 4791-4801), following the proof of
`QuotientExchange.forest_of_min`.  The induction hypothesis is the *public* exchange lemma
`QuotientExchange.exchange`, applied to the induced subgraph `H[X]`.
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β} {x0 x1 u0 u1 : α} {e f0 f1 g : β}

/-- **Bridge property of a minimising protected tree** (paper l. 4778-4790). -/
lemma claim_bridge' (hV : V(H).Finite) (hE : E(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    {S : Set β} (hS : Cls H x0 x1 u0 e f0 f1 g S)
    (hmin : ∀ S', Cls H x0 x1 u0 e f0 f1 g S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S'))
    {a0 : α} (ha0 : a0 ∈ V(H)) (hns : Ns H x0 x1 u0 (E(H) \ S) a0) {h : β}
    (hh : h ∈ E(H) \ S) {a b : α} (hl : H.IsLink h a b) (ha : Reach H (E(H) \ S) a0 a)
    (hnr : ¬ Reach H (S ∩ Ins H {y | Reach H (E(H) \ S) a0 y}) a b) :
    ¬ Reach H ((E(H) \ S) \ {h}) a b := by
  intro hcon
  have hSt := hS.tree
  obtain ⟨hSE, hne, hconn, hcard⟩ := (isSpanningTree_iff hV hE).1 hSt
  have hc := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
  have hforest : IsForest H S := isForest_of_card hV hE hSE (by omega)
  have hab : Reach H S a b := hconn a hl.left_mem b hl.right_mem
  obtain ⟨f, hfS, p, q, hfl, h1, h2, hside⟩ :=
    boundary_edge (hE.subset hSE) hSE (R := {y | Reach H (E(H) \ S) a0 y}) ha hab hnr
  have hnr' : ¬ Reach H (S \ {f}) a b := fun h' =>
    forest_bridge hforest hfS hfl (h1.symm'.trans' (h'.trans' h2.symm'))
  have key : ∀ p q, H.IsLink f p q → Reach H (E(H) \ S) a0 p → ¬ Reach H (E(H) \ S) a0 q →
      False := by
    intro p q hfl hp hq
    obtain ⟨hcls, hcomp⟩ := swap_cls hV hE geo hS ha0 hns hh hl ha hcon hfS hfl hp hq hnr'
    have := hmin _ hcls
    omega
  rcases hside with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact key p q hfl hp hq
  · exact key q p hfl.symm hq hp

/-- **The induction step**: a minimising protected tree has a forest as complement.  `hcard` is the
edge count `|E(H)| + 4 = 2 |V(H)|`. -/
theorem forest_of_min' (hV : V(H).Finite) (hE : E(H).Finite) (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X)
    (geo : Geo H x0 x1 u0 u1 e f0 f1 g) (hcard : E(H).ncard + 4 = 2 * V(H).ncard)
    {S : Set β} (hS : Cls H x0 x1 u0 e f0 f1 g S)
    (hmin : ∀ S', Cls H x0 x1 u0 e f0 f1 g S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S')) :
    IsForest H (E(H) \ S) := by
  by_contra hnf
  have hSt := hS.tree
  obtain ⟨hSE, hne, hconn, hcardS⟩ := (isSpanningTree_iff hV hE).1 hSt
  have hKE : E(H) \ S ⊆ E(H) := Set.sdiff_subset
  have hgK : g ∈ E(H) \ S := ⟨hS.hgE, hS.hgS⟩
  obtain ⟨k0, hk0K, a, b, hk0l, hk0r⟩ := exists_nonbridge (hE.subset hKE) hKE hnf
  have haV : a ∈ V(H) := hk0l.left_mem
  have hbV : b ∈ V(H) := hk0l.right_mem
  -- `a` lies in a non-special component
  have hnsa : Ns H x0 x1 u0 (E(H) \ S) a := by
    have hKcard : (E(H) \ S).ncard + 3 = V(H).ncard := by
      rw [Set.ncard_sdiff hSE (hE.subset hSE)]
      have := Set.ncard_le_ncard hSE hE
      omega
    have hsp := special_tree hV hE hKE geo.le.left_mem geo.le.right_mem geo.lf0.right_mem
      hS.d01 hS.d0u hS.d1u hKcard hS.inv
    have key : ∀ z, Reach H (E(H) \ S) a z → (z = x0 ∨ z = x1 ∨ z = u0) → False := by
      intro z hz hzz
      have hAc : CallOrder.IsComp H (E(H) \ S) {y | CallOrder.Conn H (E(H) \ S) a y} :=
        CallOrder.isComp_comp haV
      have hspec : x0 ∈ {y | CallOrder.Conn H (E(H) \ S) a y} ∨
          x1 ∈ {y | CallOrder.Conn H (E(H) \ S) a y} ∨
          u0 ∈ {y | CallOrder.Conn H (E(H) \ S) a y} := by
        rcases hzz with rfl | rfl | rfl
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr hz)
      have hT := hsp _ hAc hspec
      have hmemb : b ∈ {y | CallOrder.Conn H (E(H) \ S) a y} :=
        reach_of_isLink hk0K hk0l
      have hk0A : k0 ∈ CallOrder.edgesIn H (E(H) \ S) {y | CallOrder.Conn H (E(H) \ S) a y} :=
        ⟨hk0K, a, b, hk0l, CallOrder.Conn.refl a, hmemb⟩
      obtain ⟨A1, A2, hA1, hA2, hdis, -, ha1, hb2⟩ :=
        CallOrder.tree_split hV hE hT hk0A hk0l
      have : b ∈ A1 := hA1.1.mem_of_conn ha1 hk0r
      exact Set.disjoint_left.1 hdis this hb2
    exact ⟨fun h => key x0 h (Or.inl rfl), fun h => key x1 h (Or.inr (Or.inl rfl)),
      fun h => key u0 h (Or.inr (Or.inr rfl))⟩
  have hbr : ∀ k, k ∈ E(H) \ S → ∀ w y, H.IsLink k w y → Reach H (E(H) \ S) a w →
      ¬ Reach H (S ∩ Ins H {y | Reach H (E(H) \ S) a y}) w y →
      ¬ Reach H ((E(H) \ S) \ {k}) w y :=
    fun k hk w y hl hw hnr => claim_bridge' hV hE geo hS hmin haV hnsa hk hl hw hnr
  obtain ⟨R, hR⟩ : ∃ R : Set α, ∀ y, y ∈ R ↔ Reach H (E(H) \ S) a y :=
    ⟨{y | Reach H (E(H) \ S) a y}, fun _ => Iff.rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Set α, ∀ y, y ∈ X ↔ Reach H (S ∩ Ins H R) a y :=
    ⟨{y | Reach H (S ∩ Ins H R) a y}, fun _ => Iff.rfl⟩
  obtain ⟨hbX, hrX⟩ := cycle_in_class' hE hbr hk0K hk0l hk0r hR hX
  have haR : a ∈ R := (hR a).2 reach_refl
  have hRV : R ⊆ V(H) := fun y hy => reach_mem_of_mem ((hR y).1 hy) haV
  have hclS : Closed H (S ∩ Ins H R) R := fun g hg x y hl hx => (ins_of_link hg.2 hl).2
  have hXR : X ⊆ R := fun w hw => (reach_closed hclS haR ((hX w).1 hw)).1
  have hXV : X ⊆ V(H) := hXR.trans hRV
  have haX : a ∈ X := (hX a).2 reach_refl
  have hclX : Closed H (S ∩ Ins H R) X := fun g hg x y hl hx =>
    (hX y).2 (((hX x).1 hx).trans' (reach_of_isLink hg hl))
  have hXconnS : ∀ v ∈ X, Reach H (S ∩ Ins H X) a v := fun v hv =>
    reach_mono (fun z hz => ⟨hz.1.1, hz.2⟩) (reach_closed hclX haX ((hX v).1 hv)).2
  have hSXconn : ∀ u ∈ X, ∀ v ∈ X, Reach H (S ∩ Ins H X) u v := fun u hu v hv =>
    (hXconnS u hu).symm'.trans' (hXconnS v hv)
  have hclK : Closed H (E(H) \ S) R := fun g hg u v hl hu =>
    (hR v).2 (((hR u).1 hu).trans' (reach_of_isLink hg hl))
  -- `X` is a proper subset of `R`
  have hex : ∃ y ∈ R, y ∉ X := by
    by_contra hall
    push Not at hall
    have hab : a ≠ b := fun h => hloop k0 a (h ▸ hk0l)
    have hbR : b ∈ R := (hR b).2 (reach_of_isLink hk0K hk0l)
    have hRfin : R.Finite := hV.subset hRV
    have h2 : 2 ≤ R.ncard := by
      have : 1 < R.ncard := (Set.one_lt_ncard hRfin).2 ⟨a, haR, b, hbR, hab⟩
      omega
    apply hno R hRV h2
    rw [isTwoTreeSet_iff hV hE]
    refine ⟨⟨a, haR⟩, hRV, S ∩ Ins H R, (E(H) \ S) ∩ Ins H R, Set.inter_subset_right,
      Set.inter_subset_right, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.2 fun z hz hz' => hz'.1.2 hz.1
    · intro x hx y hy
      exact ((hX x).1 (hall x hx)).symm'.trans' ((hX y).1 (hall y hy))
    · intro x hx y hy
      have hx' := reach_closed hclK haR ((hR x).1 hx)
      have hy' := reach_closed hclK haR ((hR y).1 hy)
      exact hx'.2.symm'.trans' hy'.2
  obtain ⟨y0, hy0R, hy0X⟩ := hex
  have hlt : X.ncard < V(H).ncard :=
    Set.ncard_lt_ncard ⟨hXV, fun h => hy0X (h (hRV hy0R))⟩ hV
  -- the induced graph on `X`
  obtain ⟨hV', hE'⟩ := finite_induce hV hE hXV
  have hSXsub : S ∩ Ins H X ⊆ Ins H X := Set.inter_subset_right
  have hc1 : comps H S = 1 := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
  have hSforest : IsForest H S := isForest_of_card hV hE hSE (by omega)
  have hSXforest' : IsForest (H.induce X) (S ∩ Ins H X) :=
    (isForest_induce_iff hE hSXsub).2 (hSforest.mono Set.inter_subset_left)
  have hconnX : ∀ x ∈ V(H.induce X), ∀ y ∈ V(H.induce X),
      Reach (H.induce X) (S ∩ Ins H X) x y :=
    fun x hx y hy => (reach_induce_iff hSXsub).2 (hSXconn x hx y hy)
  have hSXcard : (S ∩ Ins H X).ncard + 1 = X.ncard := by
    have hc := (comps_eq_one_iff hV').2 ⟨⟨a, haX⟩, hconnX⟩
    have : (S ∩ Ins H X).ncard + comps (H.induce X) (S ∩ Ins H X) = X.ncard :=
      forest_card hV' hE' hSXsub hSXforest'
    omega
  have hSXtree : IsSpanningTree (H.induce X) (S ∩ Ins H X) :=
    (isSpanningTree_iff hV' hE').2 ⟨hSXsub, ⟨a, haX⟩, hconnX, hSXcard⟩
  -- the induction hypothesis: the exchange lemma on `H[X]`
  obtain ⟨SX', hSX't, ⟨kk, hSX'fk⟩, hSX'co⟩ := exchange hV' hE'
    (fun e x h => hloop e x h.1)
    (fun Y hY h2 hTT => hno Y (hY.trans hXV) h2 (isTwoTreeSet_of_induce hXV hY hTT)) hSXtree
  have hSX'f : IsForest (H.induce X) (E(H.induce X) \ SX') := ⟨hSX'fk.2.1, hSX'fk.2.2.1⟩
  obtain ⟨hSX'sub, -, hSX'conn, hSX'card⟩ := (isSpanningTree_iff hV' hE').1 hSX't
  have hSX'sub' : SX' ⊆ Ins H X := hSX'sub
  have hSX'conn' : ∀ u ∈ X, ∀ v ∈ X, Reach H SX' u v := fun u hu v hv =>
    (reach_induce_iff hSX'sub').1 (hSX'conn u hu v hv)
  have hSX'card' : SX'.ncard + 1 = X.ncard := hSX'card
  -- the new tree
  have hStilde : IsSpanningTree H ((S \ Ins H X) ∪ SX') :=
    glue_tree hV hE hSt hSX'sub' hSX'conn' hSX'card' hSXcard
  have hKt := compl_glue (S := S) hSX'sub'
  have hKK : ∀ x y, Reach H (E(H) \ S) x y ↔
      Reach H (E(H) \ ((S \ Ins H X) ∪ SX')) x y := by
    intro x y
    constructor
    · intro h
      refine reach_of_forall_step (fun g hg u v hl => ?_) h
      by_cases hgI : g ∈ Ins H X
      · obtain ⟨hu, hv⟩ := ins_of_link hgI hl
        have h1 : Reach (H.induce X) (E(H.induce X) \ (S ∩ Ins H X)) u v :=
          reach_of_isLink (e := g) ⟨hgI, fun hh => hg.2 hh.1⟩ ⟨hl, hu, hv⟩
        have h2 := hSX'co u v h1
        have h3 : Reach H (Ins H X \ SX') u v :=
          (reach_induce_iff (Set.sdiff_subset.trans (le_refl _))).1 h2
        refine reach_mono ?_ h3
        rw [hKt]; exact Set.subset_union_right
      · rw [hKt]
        exact reach_of_isLink (Set.mem_union_left _ ⟨hg, hgI⟩) hl
    · intro h
      refine reach_of_forall_step (fun g hg u v hl => ?_) h
      rw [hKt] at hg
      rcases hg with hg | hg
      · exact reach_of_isLink hg.1 hl
      · obtain ⟨hu, hv⟩ := ins_of_link hg.1 hl
        exact ((hR u).1 (hXR hu)).symm'.trans' ((hR v).1 (hXR hv))
  have hKXeq : (E(H) \ S) ∩ Ins H X = Ins H X \ (S ∩ Ins H X) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨_, hzS⟩, hzI⟩
      exact ⟨hzI, fun h => hzS h.1⟩
    · rintro ⟨hzI, hn⟩
      exact ⟨⟨ins_subset_edgeSet hzI, fun hs => hn ⟨hs, hzI⟩⟩, hzI⟩
  have hKXsub : (E(H) \ S) ∩ Ins H X ⊆ Ins H X := Set.inter_subset_right
  have hK''sub : Ins H X \ SX' ⊆ Ins H X := Set.sdiff_subset
  have hgI : k0 ∈ Ins H X := mem_ins_of_link hk0l haX hbX
  have hnfX : ¬ IsForest (H.induce X) ((E(H) \ S) ∩ Ins H X) := by
    intro hF
    refine forest_bridge hF (e := k0) ⟨hk0K, hgI⟩ (p := a) (q := b) ⟨hk0l, haX, hbX⟩ ?_
    exact (reach_induce_iff (A := ((E(H) \ S) ∩ Ins H X) \ {k0})
      (Set.sdiff_subset.trans hKXsub)).2 hrX
  have hlt1 : X.ncard < ((E(H) \ S) ∩ Ins H X).ncard +
      comps (H.induce X) ((E(H) \ S) ∩ Ins H X) := by
    obtain ⟨h1, h2⟩ := rank_ineq hV' (Set.Finite.subset hE' hKXsub) hKXsub
    have h1' : X.ncard ≤ ((E(H) \ S) ∩ Ins H X).ncard +
        comps (H.induce X) ((E(H) \ S) ∩ Ins H X) := h1
    by_contra hcon
    exact hnfX (h2.1 (by have : X.ncard = _ := le_antisymm h1' (not_lt.1 hcon); exact this.symm ▸ rfl))
  have hInsfin : (Ins H X).Finite := hE.subset ins_subset_edgeSet
  have heq2 : (Ins H X \ SX').ncard + comps (H.induce X) (Ins H X \ SX') = X.ncard :=
    forest_card hV' hE' hK''sub hSX'f
  have hcnt : ((E(H) \ S) ∩ Ins H X).ncard = (Ins H X \ SX').ncard := by
    rw [hKXeq, Set.ncard_sdiff Set.inter_subset_right (hInsfin.subset Set.inter_subset_right),
      Set.ncard_sdiff hSX'sub' (hInsfin.subset hSX'sub')]
    omega
  have hKXeq' : (E(H) \ S) ∩ Ins H X = E(H.induce X) \ (S ∩ Ins H X) := hKXeq
  have hex2 : ∃ u ∈ X, ∃ v ∈ X, Reach (H.induce X) (Ins H X \ SX') u v ∧
      ¬ Reach (H.induce X) ((E(H) \ S) ∩ Ins H X) u v := by
    by_contra hall
    push Not at hall
    have hceq : comps (H.induce X) (Ins H X \ SX') =
        comps (H.induce X) ((E(H) \ S) ∩ Ins H X) := by
      refine comps_congr (fun x y hx hy => ⟨fun h => hall x hx y hy h, fun h => ?_⟩)
      rw [hKXeq'] at h
      exact hSX'co x y h
    omega
  obtain ⟨u, hu, v, hv, huvK'', hnuv⟩ := hex2
  have huvK : Reach H (E(H) \ S) u v :=
    ((hR u).1 (hXR hu)).symm'.trans' ((hR v).1 (hXR hv))
  have hnr : ¬ Reach H ((E(H) \ S) ∩ Ins H X) u v := fun h =>
    hnuv ((reach_induce_iff hKXsub).2 h)
  obtain ⟨f, hfK, p, q, hfl, hup, hqv, hside⟩ :=
    boundary_edge (R := X) (hE.subset hKE) hKE hu huvK hnr
  have hfI : f ∉ Ins H X := fun hI => by
    obtain ⟨hp, hq⟩ := ins_of_link hI hfl
    rcases hside with ⟨_, h⟩ | ⟨_, h⟩ <;> contradiction
  have hfKt : f ∈ E(H) \ ((S \ Ins H X) ∪ SX') := by
    rw [hKt]; exact Or.inl ⟨hfK, hfI⟩
  have hstepK : ∀ s t, Reach H ((E(H) \ S) \ {f}) s t →
      Reach H ((E(H) \ ((S \ Ins H X) ∪ SX')) \ {f}) s t := by
    intro s t h
    refine reach_of_forall_step (fun g hg w z hl => ?_) h
    by_cases hgI : g ∈ Ins H X
    · obtain ⟨hw, hz⟩ := ins_of_link hgI hl
      have h1 : Reach (H.induce X) (E(H.induce X) \ (S ∩ Ins H X)) w z :=
        reach_of_isLink (e := g) ⟨hgI, fun hh => hg.1.2 hh.1⟩ ⟨hl, hw, hz⟩
      have h2 := hSX'co w z h1
      have h3 : Reach H (Ins H X \ SX') w z := (reach_induce_iff hK''sub).1 h2
      refine reach_mono ?_ h3
      rw [hKt]
      intro k hk
      refine ⟨Or.inr hk, fun hkf => hfI ?_⟩
      rw [Set.mem_singleton_iff] at hkf
      exact hkf ▸ hk.1
    · have : g ∈ E(H) \ ((S \ Ins H X) ∪ SX') := by
        rw [hKt]; exact Or.inl ⟨hg.1, hgI⟩
      exact reach_of_isLink ⟨this, hg.2⟩ hl
  have hup' := hstepK _ _ hup
  have hqv' := hstepK _ _ hqv
  have huv' : Reach H ((E(H) \ ((S \ Ins H X) ∪ SX')) \ {f}) u v := by
    refine reach_mono ?_ ((reach_induce_iff hK''sub).1 huvK'')
    rw [hKt]
    intro k hk
    refine ⟨Or.inr hk, fun hkf => hfI ?_⟩
    rw [Set.mem_singleton_iff] at hkf
    exact hkf ▸ hk.1
  have hpq : Reach H ((E(H) \ ((S \ Ins H X) ∪ SX')) \ {f}) p q :=
    hup'.symm'.trans' (huv'.trans' hqv'.symm')
  -- the new tree is in the class, and is again a minimiser
  have hcls : Cls H x0 x1 u0 e f0 f1 g ((S \ Ins H X) ∪ SX') :=
    glue_cls hV hE geo hS hnsa hR hXR hSX'sub' hStilde hKK hcnt
  have hcomps : comps H (E(H) \ ((S \ Ins H X) ∪ SX')) = comps H (E(H) \ S) :=
    comps_congr (fun x y _ _ => (hKK x y).symm)
  have hmin' : ∀ S', Cls H x0 x1 u0 e f0 f1 g S' →
      comps H (E(H) \ ((S \ Ins H X) ∪ SX')) ≤ comps H (E(H) \ S') := by
    intro S' h; rw [hcomps]; exact hmin S' h
  have hnsa' : Ns H x0 x1 u0 (E(H) \ ((S \ Ins H X) ∪ SX')) a :=
    ⟨fun h => hnsa.1 ((hKK _ _).2 h), fun h => hnsa.2.1 ((hKK _ _).2 h),
      fun h => hnsa.2.2 ((hKK _ _).2 h)⟩
  have hpR : Reach H (E(H) \ S) a p := by
    have := reach_mono (Set.sdiff_subset : (E(H) \ S) \ {f} ⊆ E(H) \ S) hup
    exact ((hR u).1 (hXR hu)).trans' this
  have hRset : {y | Reach H (E(H) \ ((S \ Ins H X) ∪ SX')) a y} = R :=
    Set.ext fun y => ((hR y).trans (hKK a y)).symm
  have hnrS : ¬ Reach H (S ∩ Ins H R) p q := by
    intro h
    rcases hside with ⟨hpX, hqX⟩ | ⟨hqX, hpX⟩
    · exact hqX ((hX q).2 (((hX p).1 hpX).trans' h))
    · exact hpX ((hX p).2 (((hX q).1 hqX).trans' h.symm'))
  have hnrS' : ¬ Reach H (((S \ Ins H X) ∪ SX') ∩ Ins H {y | Reach H
      (E(H) \ ((S \ Ins H X) ∪ SX')) a y}) p q := by
    rw [hRset]
    intro h
    exact hnrS ((glue_reach hXR hSX'sub' hSX'conn' hSXconn).1 h)
  exact claim_bridge' hV hE geo hcls hmin' haV hnsa' hfKt hfl ((hKK a p).1 hpR) hnrS' hpq

end Lax630294Proofs.ProtectedExt
