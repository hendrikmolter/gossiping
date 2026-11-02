import Lax630294Proofs.CallOrderForest

/-!
# Canonical ideal normalization (`lem:characterization-canonical-ideal`)
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- The conclusion of `lem:characterization-canonical-ideal`.  Here `I` is the ideal, `F` is
`E(H) \ I`, `X` the tree component of `H[I]`, `e = x0 x1` its last edge. -/
structure IsCanonical (H : Graph α β) (P : β → β → Prop) (I : Set β) (X : Set α) (e : β)
    (x0 x1 : α) : Prop where
  /-- `I` is an ideal. -/
  ideal : IsIdeal H P I
  /-- Item 1: `|I| = r - 2`. -/
  card_I : I.ncard + 2 = V(H).ncard
  /-- Item 1: `|F| = r - 2`. -/
  card_F : (E(H) \ I).ncard + 2 = V(H).ncard
  /-- `X` is a tree component of `H[I]`. -/
  tree : IsTreeComp H I X
  /-- Item 1: `|V(X)| ≥ 2`. -/
  two_le : 2 ≤ X.ncard
  /-- `e` is an edge of `X`, joining `x0` and `x1`. -/
  e_mem : e ∈ edgesIn H I X
  e_link : H.IsLink e x0 x1
  /-- Item 2: every other edge of `X` precedes `e` (so `e` is the unique maximal edge). -/
  e_max : ∀ g ∈ edgesIn H I X, g ≠ e → P g e
  /-- Item 3: `e <_P f` for every `f ∈ F`. -/
  e_lt : ∀ f ∈ E(H) \ I, P e f
  /-- Item 4: `H[F]` is a spanning forest with two trees rooted at `x0`, `x1`, ordered outward. -/
  forest : ∃ (par : α → α) (pe : α → β), IsRootedForest H P (E(H) \ I) x0 x1 par pe
  /-- Item 5: an increasing trail ending at `x0` or `x1` contains at most one edge of
  `F ∪ {e}`, and that edge is its last edge. -/
  trail : ∀ (u v : α) (es : List β), (v = x0 ∨ v = x1) → IncTrail H P u v es →
    ∀ g ∈ es.dropLast, g ∉ (E(H) \ I) ∪ {e}
  /-- Every `P`-minimal edge of `F` crosses the boundary of `X`. -/
  cross : ∀ f, IsMinOut H P I f → Crosses H X f

/-- A maximal edge of a nontrivial tree component. -/
lemma Admissible.exists_max_edge (hA : Admissible H P) {I : Set β} {X : Set α}
    (hR : IsReduced H P I X) (h2 : 2 ≤ X.ncard) :
    ∃ e ∈ edgesIn H I X, ∀ c ∈ edgesIn H I X, ¬ P e c := by
  have hedge : (edgesIn H I X).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have := hR.tree.2
    rw [hemp] at this
    simp at this
    omega
  exact hA.exists_max (edgesIn_subset I X) hedge

lemma Admissible.first_lt (hA : Admissible H P) {I : Set β} {ℓ : β → ℕ} {R : Set α}
    {φ : α → β} (hφ : ∀ v ∈ V(H) \ R, IsFirstAt H I ℓ v (φ v))
    (hinj : Set.InjOn φ (V(H) \ R)) {v u : α} (hv : v ∈ V(H) \ R) (hu : u ∈ V(H) \ R)
    (hl : H.IsLink (φ v) v u) : ℓ (φ u) < ℓ (φ v) := by
  refine (hφ u hu).2.2.2 (φ v) (hφ v hv).1 (hφ v hv).2.1 hl.inc_right ?_
  intro h
  exact hA.link_ne hl (hinj hv hu h)

/-- The first-call data for a linear extension `ℓ` placing `I` first and `e` last in `I`:
a bijection from the non-roots onto `F`, sending `v` to its first call outside `I`. -/
lemma Admissible.fam_data [Nonempty β] (hA : Admissible H P) {I : Set β} {X : Set α}
    (hR : IsReduced H P I X) {e : β} {x0 x1 : α} (he : e ∈ edgesIn H I X)
    (hemaxI : ∀ c ∈ I, ¬ P e c) (hl : H.IsLink e x0 x1) (hP3e : ∀ f ∈ E(H) \ I, P e f)
    (hF : (E(H) \ I).ncard + 2 = V(H).ncard) (hxne : x0 ≠ x1) {ℓ : β → ℕ}
    (hfam : IsFam H P I e ℓ) :
    ∃ φ : α → β, (∀ v ∈ V(H) \ {x0, x1}, IsFirstAt H I ℓ v (φ v)) ∧
      Set.InjOn φ (V(H) \ {x0, x1}) ∧
      ∀ f ∈ E(H) \ I, ∃ v ∈ V(H) \ {x0, x1}, φ v = f := by
  obtain ⟨φ, hφ, hinj⟩ := hA.first_call_inj hR.ideal hfam.inj hfam.mono (R := {x0, x1})
    (fun v hv hvR => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hvR
      exact hA.nonroot_need hR he hl hfam hv hvR.1 hvR.2)
    (fun f hf => by
      rcases hA.minout_touch hemaxI hl hP3e hf with h | h
      · exact ⟨x0, Or.inl rfl, h⟩
      · exact ⟨x1, Or.inr rfl, h⟩)
  refine ⟨φ, fun v hv => hφ v hv.1 hv.2, hinj, ?_⟩
  have hRsub : ({x0, x1} : Set α) ⊆ V(H) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hl.left_mem
    · exact hl.right_mem
  have hcardR : ({x0, x1} : Set α).ncard = 2 := Set.ncard_pair hxne
  have hcardVR : (V(H) \ {x0, x1}).ncard = V(H).ncard - 2 := by
    rw [Set.ncard_sdiff' hRsub hA.finV, hcardR]
  have himg : φ '' (V(H) \ {x0, x1}) = E(H) \ I := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (hA.finE.subset Set.sdiff_subset)
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨(hφ v hv.1 hv.2).1, (hφ v hv.1 hv.2).2.1⟩
    · rw [hinj.ncard_image, hcardVR]
      omega
  intro f hf
  rw [← himg] at hf
  obtain ⟨v, hv, rfl⟩ := hf
  exact ⟨v, hv, rfl⟩

/-- **Canonical ideal normalization** (`lem:characterization-canonical-ideal`). -/
theorem Admissible.canonical_ideal (hA : Admissible H P) (hr : 4 ≤ V(H).ncard)
    (hE : E(H).ncard = 2 * V(H).ncard - 4) :
    ∃ (I : Set β) (X : Set α) (e : β) (x0 x1 : α), IsCanonical H P I X e x0 x1 := by
  classical
  -- Step 0: a reduced pair `(I, X)`
  have hrE : V(H).ncard - 2 ≤ E(H).ncard := by omega
  obtain ⟨J, hJ, hJc⟩ := hA.exists_ideal_ncard hrE
  obtain ⟨A, B, hAt, hBt, hAB⟩ := exists_two_tree_comps hA.finV hA.finE hJ.1 (by omega)
  obtain ⟨J', hJ', hJ'c, Xc, hXct, hXcc⟩ := hA.exists_closed hJ hAt hBt hAB
  obtain ⟨I, X, hR, hJI, -, hP3⟩ := hA.closed_tree_reduction hJ' hXct hXcc
  have hbound := hA.card_F_lower hR hP3
  have hsplit : (E(H) \ I).ncard + I.ncard = E(H).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hR.ideal.1 hA.finE
  have hXfin : X.Finite := hA.finV.subset hR.tree.1.2.1
  have hIfin : I.Finite := hA.finE.subset hR.ideal.1
  have hXtwo : 2 ≤ X.ncard := by
    have hpos := (Set.ncard_pos hXfin).2 hR.tree.1.1
    by_contra hlt
    have h1 : X.ncard = 1 := by omega
    have := hbound.2 h1
    omega
  have hIcard : I.ncard + 2 = V(H).ncard := by omega
  have hFcard : (E(H) \ I).ncard + 2 = V(H).ncard := by omega
  -- Step 1: the maximal edge `e = x0 x1` of `X`
  obtain ⟨e, he, hemax⟩ := hA.exists_max_edge hR hXtwo
  have hemaxI := hA.max_in_ideal hR.ideal hR.tree.1 he hemax
  have heI : e ∈ I := he.1
  obtain ⟨x0, x1, hl, hx0, hx1⟩ := he.2
  have hxne : x0 ≠ x1 := hA.link_ne hl
  have heF : ∀ f ∈ E(H) \ I, P e f := hP3 e he hemax
  have : Nonempty β := ⟨e⟩
  -- Step 2: both roots take part in a call outside `I`
  have hXlt : X.ncard < V(H).ncard := by
    have h1 := Set.ncard_le_ncard (edgesIn_subset_S (H := H) I X) hIfin
    have h2 := hR.tree.2
    omega
  have hsX : ∃ s ∈ V(H), s ∉ X := by
    by_contra hcon
    push Not at hcon
    have := Set.ncard_le_ncard (fun s hs => hcon s hs) hXfin
    omega
  obtain ⟨s, hsV, hsX⟩ := hsX
  have hroot : ∀ x, (x = x0 ∨ x = x1) → ∃ f ∈ E(H), f ∉ I ∧ H.Inc f x := by
    intro x hx
    have hxX : x ∈ X := by
      rcases hx with rfl | rfl
      · exact hx0
      · exact hx1
    by_contra hnone
    have hnone' : ∀ f ∈ E(H) \ I, ¬ H.Inc f x := fun f hf hinc => hnone ⟨f, hf.1, hf.2, hinc⟩
    obtain ⟨ℓ, hfam⟩ := hA.exists_fam hR.ideal heI hemaxI
    have hc := need_conn hA hfam.inj hfam.mono hfam.Ifirst (hR.tree.1.2.1 hxX) hnone' hsV
    exact hsX (hR.tree.1.mem_of_conn hxX hc.symm)
  -- Step 3: first-call data of a fixed extension
  obtain ⟨ℓ0, hfam0⟩ := hA.exists_fam hR.ideal heI hemaxI
  obtain ⟨pe, hpeF, hpeinj, hpesurj⟩ := hA.fam_data hR he hemaxI hl heF hFcard hxne hfam0
  have hparex : ∀ v, ∃ u, v ∈ V(H) \ {x0, x1} → H.IsLink (pe v) v u := by
    intro v
    by_cases hv : v ∈ V(H) \ {x0, x1}
    · obtain ⟨u, hu⟩ := (hpeF v hv).2.2.1
      exact ⟨u, fun _ => hu⟩
    · exact ⟨v, fun h => absurd h hv⟩
  choose par0 hpar0 using hparex
  obtain ⟨par, hparval⟩ : ∃ par : α → α,
      ∀ v, par v = if v = x0 ∨ v = x1 then v else par0 v := ⟨_, fun _ => rfl⟩
  have hpar : ∀ v, v ∈ V(H) \ {x0, x1} → H.IsLink (pe v) v (par v) := by
    intro v hv
    have hv' : ¬ (v = x0 ∨ v = x1) := by
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      exact hv.2
    rw [hparval, if_neg hv']
    exact hpar0 v hv
  have hnonroot : ∀ v, v ∈ V(H) → v ≠ x0 → v ≠ x1 → v ∈ V(H) \ {x0, x1} := by
    intro v hv h0 h1
    refine ⟨hv, ?_⟩
    simp [h0, h1]
  -- Step 4: the first-call map is the same for every extension in the family
  have hsame : ∀ ℓ, IsFam H P I e ℓ → ∀ φ : α → β,
      (∀ v ∈ V(H) \ {x0, x1}, IsFirstAt H I ℓ v (φ v)) → Set.InjOn φ (V(H) \ {x0, x1}) →
      (∀ f ∈ E(H) \ I, ∃ v ∈ V(H) \ {x0, x1}, φ v = f) →
      ∀ v ∈ V(H) \ {x0, x1}, φ v = pe v := by
    intro ℓ hfam φ hφ hinj hsurj
    by_contra hbad
    push Not at hbad
    obtain ⟨v0, hv0, hv0ne⟩ := hbad
    obtain ⟨v, ⟨hv, hvne⟩, hvmin⟩ := Set.exists_min_image
      {v | v ∈ V(H) \ {x0, x1} ∧ φ v ≠ pe v} (fun v => ℓ0 (pe v))
      (hA.finV.subset (fun v hv => hv.1.1)) ⟨v0, hv0, hv0ne⟩
    obtain ⟨w, hw, hwv⟩ := hsurj (pe v) ⟨(hpeF v hv).1, (hpeF v hv).2.1⟩
    have hwne : w ≠ v := fun h => hvne (h ▸ hwv)
    have hwInc : H.Inc (pe v) w := by
      have := (hφ w hw).2.2.1
      rwa [hwv] at this
    have hwpar : w = par v := by
      rcases hwInc.eq_or_eq_of_isLink (hpar v hv) with h | h
      · exact absurd h hwne
      · exact h
    have hwbad : w ∈ {v | v ∈ V(H) \ {x0, x1} ∧ φ v ≠ pe v} := by
      refine ⟨hw, ?_⟩
      rw [hwv]
      intro h
      exact hwne (hpeinj hw hv h.symm)
    have hmin := hvmin w hwbad
    have hlt := hA.first_lt hpeF hpeinj hv hw (hwpar ▸ hpar v hv)
    omega
  -- Step 5: outward order
  have hout : ∀ v ∈ V(H), v ≠ x0 → v ≠ x1 → par v ≠ x0 → par v ≠ x1 →
      P (pe (par v)) (pe v) := by
    intro v hv hv0 hv1 hp0 hp1
    have hvR := hnonroot v hv hv0 hv1
    have hlv := hpar v hvR
    have hpR := hnonroot (par v) hlv.right_mem hp0 hp1
    by_contra hnot
    have hne : pe v ≠ pe (par v) := fun h => hA.link_ne hlv (hpeinj hvR hpR h)
    have hlt0 := hA.first_lt hpeF hpeinj hvR hpR hlv
    have hnot' : ¬ P (pe v) (pe (par v)) := by
      intro h
      have := hfam0.mono _ _ h
      omega
    obtain ⟨ℓ1, hfam1, hlt⟩ := hA.exists_fam_pair hR.ideal heI hemaxI
      (hpeF v hvR).1 (hpeF v hvR).2.1 (hpeF _ hpR).1 (hpeF _ hpR).2.1 hne hnot' hnot
    obtain ⟨φ1, hφ1, hinj1, hsurj1⟩ := hA.fam_data hR he hemaxI hl heF hFcard hxne hfam1
    have hs1 := hsame ℓ1 hfam1 φ1 hφ1 hinj1 hsurj1
    have h3 := hA.first_lt hφ1 hinj1 hvR hpR (by rw [hs1 v hvR]; exact hlv)
    rw [hs1 _ hpR, hs1 _ hvR] at h3
    omega
  -- Step 6: every vertex reaches a root
  have hreach : ∀ v ∈ V(H), ∃ n : ℕ, par^[n] v = x0 ∨ par^[n] v = x1 := by
    intro v0 hv0V
    by_contra hbad
    push Not at hbad
    obtain ⟨v, ⟨hvV, hvbad⟩, hvmin⟩ := Set.exists_min_image
      {v | v ∈ V(H) ∧ ∀ n : ℕ, par^[n] v ≠ x0 ∧ par^[n] v ≠ x1} (fun v => ℓ0 (pe v))
      (hA.finV.subset (fun v hv => hv.1)) ⟨v0, hv0V, hbad⟩
    have hv0 : v ≠ x0 := (hvbad 0).1
    have hv1 : v ≠ x1 := (hvbad 0).2
    have hvR := hnonroot v hvV hv0 hv1
    have hlv := hpar v hvR
    have hp0 : par v ≠ x0 := (hvbad 1).1
    have hp1 : par v ≠ x1 := (hvbad 1).2
    have hpbad : par v ∈ {v | v ∈ V(H) ∧ ∀ n : ℕ, par^[n] v ≠ x0 ∧ par^[n] v ≠ x1} := by
      refine ⟨hlv.right_mem, fun n => ?_⟩
      have := hvbad (n + 1)
      rwa [Function.iterate_succ_apply] at this
    have hmin := hvmin _ hpbad
    have hlt := hfam0.mono _ _ (hout v hvV hv0 hv1 hp0 hp1)
    omega
  -- Step 7: the unique maximal edge of `X`
  have hmaxeq : ∀ s ∈ edgesIn H I X, (∀ c ∈ edgesIn H I X, ¬ P s c) → s = e := by
    intro s hs hsmax
    have hsmaxI := hA.max_in_ideal hR.ideal hR.tree.1 hs hsmax
    have hsF := hP3 s hs hsmax
    have hinc : ∀ x, (x = x0 ∨ x = x1) → H.Inc s x := by
      intro x hx
      have hxX : x ∈ X := by
        rcases hx with rfl | rfl
        · exact hx0
        · exact hx1
      obtain ⟨f, hfE, hfI, hfx⟩ := hroot x hx
      obtain ⟨f1, hf1⟩ := exists_first hA hfam0.inj ⟨f, hfE, hfI, hfx⟩
      obtain ⟨xl, hxl⟩ := hf1.2.2.1
      obtain ⟨w, hw, hwf⟩ := hpesurj f1 ⟨hf1.1, hf1.2.1⟩
      have hwInc : H.Inc f1 w := by
        have := (hpeF w hw).2.2.1
        rwa [hwf] at this
      have hwxl : w = xl := by
        rcases hwInc.eq_or_eq_of_isLink hxl with h | h
        · exfalso
          rw [h] at hw
          rcases hx with rfl | rfl
          · exact hw.2 (Or.inl rfl)
          · exact hw.2 (Or.inr rfl)
        · exact h
      subst hwxl
      have hfw : IsFirstAt H I ℓ0 w f1 := by rw [← hwf]; exact hpeF w hw
      have hmin := isMinOut_of_first hA hR.ideal hfam0.mono hxl hf1 hfw
      have hwX : w ∉ X := by
        obtain ⟨p, q, hpq, hp, hq⟩ := hR.cross f1 hmin
        rcases hxl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hq
        · exact absurd hxX hq
      have hsf := hsF f1 ⟨hf1.1, hf1.2.1⟩
      have hcov : ∀ c, P s c → ¬ P c f1 := fun c hsc hcf => hsmaxI c (hmin.2.2 c hcf) hsc
      obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hsf hcov
      obtain ⟨p, q, hpq, hp, hq⟩ := hs.2
      have hyX : y ∈ X := by
        rcases hy1.eq_or_eq_of_isLink hpq with h | h
        · rw [h]; exact hp
        · rw [h]; exact hq
      rcases hy2.eq_or_eq_of_isLink hxl with h | h
      · rw [h] at hy1; exact hy1
      · rw [h] at hyX; exact absurd hyX hwX
    have hs01 : H.IsLink s x0 x1 :=
      link_of_inc_inc (hinc x0 (Or.inl rfl)) (hinc x1 (Or.inr rfl)) hxne
    exact hA.link_unique hs01 hl
  have hemax' : ∀ g ∈ edgesIn H I X, g ≠ e → P g e := by
    intro g hg hge
    obtain ⟨m, ⟨hmE, hgm⟩, hmmax⟩ := hA.exists_max
      (T := {c | c ∈ edgesIn H I X ∧ (g = c ∨ P g c)})
      (fun c hc => edgesIn_subset I X hc.1) ⟨g, hg, Or.inl rfl⟩
    have hm : ∀ c ∈ edgesIn H I X, ¬ P m c := by
      intro c hc hmc
      refine hmmax c ⟨hc, Or.inr ?_⟩ hmc
      rcases hgm with h | h
      · rw [h]; exact hmc
      · exact hA.trans h hmc
    have hme := hmaxeq m hmE hm
    rw [hme] at hgm
    rcases hgm with h | h
    · exact absurd h hge
    · exact h
  -- Step 8: assemble
  have hfor : IsRootedForest H P (E(H) \ I) x0 x1 par pe := by
    refine ⟨?_, ⟨?_, hpeinj, ?_⟩, hreach, hout, ?_, ?_⟩
    · intro v hv h0 h1
      have hvR := hnonroot v hv h0 h1
      exact ⟨⟨(hpeF v hvR).1, (hpeF v hvR).2.1⟩, hpar v hvR⟩
    · intro v hv
      exact ⟨(hpeF v hv).1, (hpeF v hv).2.1⟩
    · intro f hf
      obtain ⟨v, hv, hvf⟩ := hpesurj f hf
      exact ⟨v, hv, hvf⟩
    · rw [hparval]; simp
    · rw [hparval]; simp
  refine ⟨I, X, e, x0, x1, ⟨hR.ideal, hIcard, hFcard, hR.tree, hXtwo, he, hl, hemax', heF,
    ⟨par, pe, hfor⟩, ?_, hR.cross⟩⟩
  intro u v es hv ht
  exact hA.trail_dropLast hR.ideal heI hemaxI hl hfor ht hv

end Lax630294Proofs.CallOrder
