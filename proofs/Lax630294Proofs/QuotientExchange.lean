import Lax630294Proofs.QuotientTwoTree

/-!
# The spanning-tree exchange lemma (`lem:characterization-exchange`)

Everything is phrased with `Reach` (connectivity by an edge set) and the counting library of
`QuotientCore`; no walks or paths of Mathlib's `SimpleGraph` are needed.
-/

namespace Lax630294Proofs.QuotientExchange

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree

variable {α β : Type*} {H : Graph α β} {F K S T : Set β} {R X Y : Set α} {a b p q x y : α} {e f g : β}

/-- Every edge of `F` leaving `R` from an end in `R` stays in `R`. -/
def Closed (H : Graph α β) (F : Set β) (R : Set α) : Prop :=
  ∀ g ∈ F, ∀ x y, H.IsLink g x y → x ∈ R → y ∈ R

lemma reach_closed (hcl : Closed H F R) (ha : a ∈ R) (h : Reach H F a b) :
    b ∈ R ∧ Reach H (F ∩ Ins H R) a b := by
  induction h with
  | refl => exact ⟨ha, reach_refl⟩
  | @tail w y _ hs ih =>
    obtain ⟨g, hg, hl⟩ := hs
    have hy : y ∈ R := hcl g hg w y hl ih.1
    exact ⟨hy, ih.2.trans' (reach_of_isLink ⟨hg, mem_ins_of_link hl ih.1 hy⟩ hl)⟩

/-- A connection by `F` not using only edges inside `R` must use an edge of `F` with exactly one end
in `R`, and this edge is a cut edge for the connection. -/
lemma boundary_edge (hfin : F.Finite) (hFE : F ⊆ E(H)) (ha : a ∈ R) (hab : Reach H F a b)
    (hnr : ¬ Reach H (F ∩ Ins H R) a b) :
    ∃ f ∈ F, ∃ p q, H.IsLink f p q ∧ Reach H (F \ {f}) a p ∧ Reach H (F \ {f}) q b ∧
      ((p ∈ R ∧ q ∉ R) ∨ (q ∈ R ∧ p ∉ R)) := by
  let Bd : Set β := {g | ∃ x y, H.IsLink g x y ∧ x ∈ R ∧ y ∉ R}
  have hcl : Closed H (F \ Bd) R := fun g hg x y hl hx => by
    by_contra hy
    exact hg.2 ⟨x, y, hl, hx, hy⟩
  have h₀ : ¬ Reach H (F \ Bd) a b := fun h =>
    hnr (reach_mono (Set.inter_subset_inter_left _ Set.sdiff_subset) (reach_closed hcl ha h).2)
  obtain ⟨f, hf, p, q, hl, h1, h2⟩ := cut_lemma (Set.sdiff_subset) hfin hFE hab h₀
  have hfB : f ∈ Bd := by
    by_contra h
    exact hf.2 ⟨hf.1, h⟩
  obtain ⟨x, y, hl', hx, hy⟩ := hfB
  refine ⟨f, hf.1, p, q, hl, ?_, ?_, ?_⟩
  · exact h1
  · exact h2
  · rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩

/-- `S` is a spanning tree such that `H - E(S)` has components coarsening those of `H - E(T)`. -/
def Good (H : Graph α β) (T S : Set β) : Prop :=
  IsSpanningTree H S ∧ ∀ x y, Reach H (E(H) \ T) x y → Reach H (E(H) \ S) x y

/-- The *bridge property* of minimising trees (first paragraph of the paper's proof). -/
lemma claim_bridge (hV : V(H).Finite) (hE : E(H).Finite) (hS : Good H T S)
    (hmin : ∀ S', Good H T S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S'))
    {a0 : α} (he : e ∈ E(H) \ S) {a b : α} (hl : H.IsLink e a b)
    (ha : Reach H (E(H) \ S) a0 a)
    (hnr : ¬ Reach H (S ∩ Ins H {y | Reach H (E(H) \ S) a0 y}) a b) :
    ¬ Reach H ((E(H) \ S) \ {e}) a b := by
  intro hcon
  obtain ⟨hSt, hcoarse⟩ := hS
  have hSt' := (isSpanningTree_iff hV hE).1 hSt
  obtain ⟨hSE, hne, hconn, hcard⟩ := hSt'
  have hc := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
  have hforest : IsForest H S := isForest_of_card hV hE hSE (by omega)
  have hab : Reach H S a b := hconn a hl.left_mem b hl.right_mem
  obtain ⟨f, hfS, p, q, hfl, h1, h2, hside⟩ :=
    boundary_edge (hE.subset hSE) hSE (R := {y | Reach H (E(H) \ S) a0 y}) ha hab hnr
  have hnr' : ¬ Reach H (S \ {f}) a b := fun h =>
    forest_bridge hforest hfS hfl (h1.symm'.trans' (h.trans' h2.symm'))
  have hS' := tree_swap hV hE hSt hfS hl hnr'
  have heE : e ∈ E(H) := he.1
  have heS : e ∉ S := he.2
  have hK' : E(H) \ insert e (S \ {f}) = insert f ((E(H) \ S) \ {e}) := by
    ext g
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hgE, hg⟩
      by_cases hgS : g ∈ S
      · left; by_contra hgf; exact hg (Or.inr ⟨hgS, hgf⟩)
      · right; exact ⟨⟨hgE, hgS⟩, fun h => hg (Or.inl h)⟩
    · rintro (h | ⟨⟨hgE, hgS⟩, hge⟩)
      · subst h
        refine ⟨hSE hfS, fun h => ?_⟩
        rcases h with h | ⟨_, h⟩
        · exact heS (h ▸ hfS)
        · exact h rfl
      · exact ⟨hgE, fun h => by rcases h with h | ⟨h, _⟩ <;> [exact hge h; exact hgS h]⟩
  have hsub1 : (E(H) \ S) \ {e} ⊆ E(H) \ insert e (S \ {f}) := by
    rw [hK']; exact Set.subset_insert _ _
  have hcoarse' : ∀ x y, Reach H (E(H) \ S) x y → Reach H (E(H) \ insert e (S \ {f})) x y := by
    intro x y h
    induction h with
    | refl => exact reach_refl
    | @tail w z _ hs ih =>
      obtain ⟨g, hg, hgl⟩ := hs
      by_cases hge : g = e
      · subst hge
        rcases hl.eq_and_eq_or_eq_and_eq hgl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih.trans' (reach_mono hsub1 hcon)
        · exact ih.trans' (reach_mono hsub1 hcon).symm'
      · exact ih.trans' (reach_of_isLink (hsub1 ⟨hg, hge⟩) hgl)
  have hgood' : Good H T (insert e (S \ {f})) :=
    ⟨hS', fun x y h => hcoarse' x y (hcoarse x y h)⟩
  have hle := hmin _ hgood'
  have hnr_pq : ¬ Reach H ((E(H) \ S) \ {e}) p q := by
    intro h
    have h' : Reach H (E(H) \ S) p q := reach_mono Set.sdiff_subset h
    rcases hside with ⟨hp, hq⟩ | ⟨hq, hp⟩
    · have hp' : Reach H (E(H) \ S) a0 p := hp
      exact hq (hp'.trans' h')
    · have hq' : Reach H (E(H) \ S) a0 q := hq
      exact hp (hq'.trans' h'.symm')
  have hc1 : comps H (E(H) \ insert e (S \ {f})) + 1 = comps H ((E(H) \ S) \ {e}) := by
    rw [hK']; exact comps_insert_of_not_reach hV hfl hnr_pq
  have hc2 : comps H ((E(H) \ S) \ {e}) = comps H (E(H) \ S) :=
    comps_congr (fun x y _ _ =>
      ⟨fun h => reach_mono Set.sdiff_subset h, fun h => reach_remove_edge hl hcon h⟩)
  omega


lemma reach_of_forall_step {F F' : Set β} (h : ∀ g ∈ F, ∀ u v, H.IsLink g u v → Reach H F' u v)
    (hr : Reach H F x y) : Reach H F' x y := by
  induction hr with
  | refl => exact reach_refl
  | tail _ hs ih =>
    obtain ⟨g, hg, hl⟩ := hs
    exact ih.trans' (h g hg _ _ hl)

lemma isForest_iff_bridges (hfin : F.Finite) (hFE : F ⊆ E(H)) :
    IsForest H F ↔ ∀ e ∈ F, ∀ p q, H.IsLink e p q → ¬ Reach H (F \ {e}) p q := by
  constructor
  · intro hF e he p q hl
    exact forest_bridge hF he hl
  · intro h
    by_contra hnf
    obtain ⟨e, he, p, q, hl, hr⟩ := exists_nonbridge hfin hFE hnf
    exact h e he p q hl hr

lemma isForest_induce_iff (hE : E(H).Finite) (hF : F ⊆ Ins H X) :
    IsForest (H.induce X) F ↔ IsForest H F := by
  have hfin : F.Finite := (hE.subset ins_subset_edgeSet).subset hF
  rw [isForest_iff_bridges (H := H) hfin (hF.trans ins_subset_edgeSet),
    isForest_iff_bridges (H := H.induce X) hfin hF]
  constructor
  · intro h e he p q hl hr
    obtain ⟨hp, hq⟩ := ins_of_link (hF he) hl
    exact h e he p q ⟨hl, hp, hq⟩ ((reach_induce_iff (Set.sdiff_subset.trans hF)).2 hr)
  · intro h e he p q hl hr
    exact h e he p q hl.1 ((reach_induce_iff (Set.sdiff_subset.trans hF)).1 hr)

lemma isTwoTreeSet_of_induce (hX : X ⊆ V(H)) (hY : Y ⊆ X) (h : IsTwoTreeSet (H.induce X) Y) :
    IsTwoTreeSet H Y := by
  obtain ⟨hne, _, A, B, hA, hB, hAB⟩ := h
  rw [induce_induce hY] at hA hB
  exact ⟨hne, hY.trans hX, A, B, hA, hB, hAB⟩

/-- The bridge property of a tree `S` (see `claim_bridge`). -/
def BridgeProp (H : Graph α β) (S : Set β) : Prop :=
  ∀ (a0 : α) (e : β), e ∈ E(H) \ S → ∀ a b, H.IsLink e a b → Reach H (E(H) \ S) a0 a →
    ¬ Reach H (S ∩ Ins H {y | Reach H (E(H) \ S) a0 y}) a b → ¬ Reach H ((E(H) \ S) \ {e}) a b

lemma bridgeProp_of_min (hV : V(H).Finite) (hE : E(H).Finite) (hS : Good H T S)
    (hmin : ∀ S', Good H T S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S')) : BridgeProp H S :=
  fun _ _ he _ _ hl ha hnr => claim_bridge hV hE hS hmin he hl ha hnr

/-- A non-bridge `g` of `K = H - E(S)` lies inside a single component `X` of `S[R]`
(`R` the `K`-component of its end), and is not a bridge of `K[X]`. -/
lemma cycle_in_class (hE : E(H).Finite) (hbr : BridgeProp H S) {a b : α} {g : β}
    (hg : g ∈ E(H) \ S) (hl : H.IsLink g a b)
    (hr : Reach H ((E(H) \ S) \ {g}) a b) {R X : Set α}
    (hR : ∀ y, y ∈ R ↔ Reach H (E(H) \ S) a y)
    (hX : ∀ y, y ∈ X ↔ Reach H (S ∩ Ins H R) a y) :
    b ∈ X ∧ Reach H (((E(H) \ S) ∩ Ins H X) \ {g}) a b := by
  have hKE : E(H) \ S ⊆ E(H) := Set.sdiff_subset
  have hRset : {y | Reach H (E(H) \ S) a y} = R := Set.ext fun y => (hR y).symm
  let N : Set β := {h | h ∈ E(H) \ S ∧ ∃ p q, H.IsLink h p q ∧ Reach H ((E(H) \ S) \ {h}) p q}
  have hNg : Reach H (N \ {g}) a b := by
    by_contra hnot
    obtain ⟨f, hf, p, q, hfl, h1, h2⟩ := cut_lemma (G := H) (F₀ := N \ {g})
      (F' := (E(H) \ S) \ {g}) (Set.sdiff_subset_sdiff_left (fun h hh => hh.1))
      ((hE.subset hKE).subset Set.sdiff_subset) (Set.sdiff_subset.trans hKE) hr hnot
    have hfN : f ∉ N := fun hN => hf.2 ⟨hN, hf.1.2⟩
    apply hfN
    refine ⟨hf.1.1, p, q, hfl, ?_⟩
    have hsubK : ((E(H) \ S) \ {g}) \ {f} ⊆ (E(H) \ S) \ {f} := fun z hz => ⟨hz.1.1, hz.2⟩
    have hgK : g ∈ (E(H) \ S) \ {f} := ⟨hg, fun h => hf.1.2 h.symm⟩
    exact ((reach_mono hsubK h1).symm').trans'
      ((reach_of_isLink hgK hl).trans' (reach_mono hsubK h2).symm')
  have hXR : ∀ w, w ∈ X → w ∈ R := by
    intro w hw
    have hcl : Closed H (S ∩ Ins H R) R := fun g hg x y hl hx => (ins_of_link hg.2 hl).2
    have haR : a ∈ R := (hR a).2 reach_refl
    exact (reach_closed hcl haR ((hX w).1 hw)).1
  have key : ∀ x, Reach H (N \ {g}) a x →
      x ∈ X ∧ Reach H (((E(H) \ S) ∩ Ins H X) \ {g}) a x := by
    intro x h
    induction h with
    | refl => exact ⟨(hX a).2 reach_refl, reach_refl⟩
    | @tail w y _ hs ih =>
      obtain ⟨h, hh, hhl⟩ := hs
      obtain ⟨⟨hhK, p, q, hpql, hbr'⟩, hhg⟩ := hh
      have hwy : Reach H ((E(H) \ S) \ {h}) w y := by
        rcases hpql.eq_and_eq_or_eq_and_eq hhl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hbr'
        · exact hbr'.symm'
      have hwR : w ∈ R := hXR w ih.1
      have hSw : Reach H (S ∩ Ins H R) w y := by
        by_contra hnr
        refine hbr a h hhK w y hhl ((hR w).1 hwR) ?_ hwy
        rwa [hRset]
      have hyX : y ∈ X := (hX y).2 (((hX w).1 ih.1).trans' hSw)
      exact ⟨hyX, ih.2.trans' (reach_of_isLink ⟨⟨hhK, mem_ins_of_link hhl ih.1 hyX⟩, hhg⟩ hhl)⟩
  exact key b hNg

/-- Replacing the spanning tree `S[X]` of `X` by another spanning tree of `X`. -/
lemma glue_tree (hV : V(H).Finite) (hE : E(H).Finite) {S A' : Set β} {X : Set α}
    (hS : IsSpanningTree H S) (hA' : A' ⊆ Ins H X)
    (hAconn : ∀ u ∈ X, ∀ v ∈ X, Reach H A' u v)
    (hcard : A'.ncard + 1 = X.ncard) (hcard2 : (S ∩ Ins H X).ncard + 1 = X.ncard) :
    IsSpanningTree H ((S \ Ins H X) ∪ A') := by
  rw [isSpanningTree_iff hV hE] at hS ⊢
  obtain ⟨hSE, hne, hconn, hc⟩ := hS
  have hSfin : S.Finite := hE.subset hSE
  refine ⟨Set.union_subset (Set.sdiff_subset.trans hSE) (hA'.trans ins_subset_edgeSet), hne, ?_, ?_⟩
  · intro x hx y hy
    have key : ∀ {y : α}, Reach H S x y → Reach H ((S \ Ins H X) ∪ A') x y := by
      intro y h
      refine reach_of_forall_step (fun g hg u v hl => ?_) h
      by_cases hgI : g ∈ Ins H X
      · obtain ⟨hu, hv⟩ := ins_of_link hgI hl
        exact reach_mono Set.subset_union_right (hAconn u hu v hv)
      · exact reach_of_isLink (Set.mem_union_left _ ⟨hg, hgI⟩) hl
    exact key (hconn x hx y hy)
  · have hA'fin : A'.Finite := (hE.subset ins_subset_edgeSet).subset hA'
    have hdisj : Disjoint (S \ Ins H X) A' :=
      Set.disjoint_left.2 fun z hz hz' => hz.2 (hA' hz')
    rw [Set.ncard_union_eq hdisj (hSfin.subset Set.sdiff_subset) hA'fin]
    have h1 : (S \ Ins H X).ncard + (S ∩ Ins H X).ncard = S.ncard := by
      rw [← Set.ncard_union_eq (Set.disjoint_left.2 fun z hz hz' => hz.2 hz'.2)
        (hSfin.subset Set.sdiff_subset) (hSfin.subset Set.inter_subset_left),
        Set.sdiff_union_inter]
    omega

/-- Connectivity inside `R` is unaffected by replacing `S[X]` by another spanning tree of `X`. -/
lemma glue_reach {S A' : Set β} {X R : Set α} (hXR : X ⊆ R) (hA' : A' ⊆ Ins H X)
    (hAconn : ∀ u ∈ X, ∀ v ∈ X, Reach H A' u v)
    (hSX : ∀ u ∈ X, ∀ v ∈ X, Reach H (S ∩ Ins H X) u v) {x y : α} :
    Reach H (((S \ Ins H X) ∪ A') ∩ Ins H R) x y ↔ Reach H (S ∩ Ins H R) x y := by
  constructor
  · intro h
    refine reach_of_forall_step (fun g hg u v hl => ?_) h
    rcases hg with ⟨hg1 | hg1, hg2⟩
    · exact reach_of_isLink ⟨hg1.1, hg2⟩ hl
    · obtain ⟨hu, hv⟩ := ins_of_link (hA' hg1) hl
      exact reach_mono (Set.inter_subset_inter_right _ (ins_mono hXR)) (hSX u hu v hv)
  · intro h
    refine reach_of_forall_step (fun g hg u v hl => ?_) h
    by_cases hgI : g ∈ Ins H X
    · obtain ⟨hu, hv⟩ := ins_of_link hgI hl
      exact
        (reach_mono (Set.subset_inter_iff.2 ⟨Set.subset_union_right, hA'.trans (ins_mono hXR)⟩)
          (hAconn u hu v hv))
    · exact reach_of_isLink ⟨Or.inl ⟨hg.1, hgI⟩, hg.2⟩ hl


/-- The inductive step of the exchange lemma. -/
lemma forest_of_min (hV : V(H).Finite) (hE : E(H).Finite) (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X)
    (IH : ∀ X, X ⊆ V(H) → X.ncard < V(H).ncard → ∀ T', IsSpanningTree (H.induce X) T' →
      ∃ S', Good (H.induce X) T' S' ∧ IsForest (H.induce X) (E(H.induce X) \ S'))
    {T S : Set β} (hS : Good H T S)
    (hmin : ∀ S', Good H T S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S')) :
    IsForest H (E(H) \ S) := by
  by_contra hnf
  have hbr := bridgeProp_of_min hV hE hS hmin
  obtain ⟨hSt, hcoarse⟩ := hS
  obtain ⟨hSE, hne, hconn, hcard⟩ := (isSpanningTree_iff hV hE).1 hSt
  have hKE : E(H) \ S ⊆ E(H) := Set.sdiff_subset
  obtain ⟨g, hgK, a, b, hgl, hgr⟩ := exists_nonbridge (hE.subset hKE) hKE hnf
  have haV : a ∈ V(H) := hgl.left_mem
  obtain ⟨R, hR⟩ : ∃ R : Set α, ∀ y, y ∈ R ↔ Reach H (E(H) \ S) a y :=
    ⟨{y | Reach H (E(H) \ S) a y}, fun _ => Iff.rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Set α, ∀ y, y ∈ X ↔ Reach H (S ∩ Ins H R) a y :=
    ⟨{y | Reach H (S ∩ Ins H R) a y}, fun _ => Iff.rfl⟩
  obtain ⟨hbX, hrX⟩ := cycle_in_class hE hbr hgK hgl hgr hR hX
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
    have hab : a ≠ b := fun h => hloop g a (h ▸ hgl)
    have hbR : b ∈ R := (hR b).2 (reach_of_isLink hgK hgl)
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
  obtain ⟨SX', ⟨hSX't, hSX'co⟩, hSX'f⟩ := IH X hXV hlt _ hSXtree
  obtain ⟨hSX'sub, -, hSX'conn, hSX'card⟩ := (isSpanningTree_iff hV' hE').1 hSX't
  have hSX'sub' : SX' ⊆ Ins H X := hSX'sub
  have hSX'conn' : ∀ u ∈ X, ∀ v ∈ X, Reach H SX' u v := fun u hu v hv =>
    (reach_induce_iff hSX'sub').1 (hSX'conn u hu v hv)
  have hSX'card' : SX'.ncard + 1 = X.ncard := hSX'card
  -- the new tree
  have hStilde : IsSpanningTree H ((S \ Ins H X) ∪ SX') :=
    glue_tree hV hE hSt hSX'sub' hSX'conn' hSX'card' hSXcard
  have hKt : E(H) \ ((S \ Ins H X) ∪ SX') = ((E(H) \ S) \ Ins H X) ∪ (Ins H X \ SX') := by
    ext g
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨hgE, hn⟩
      by_cases hI : g ∈ Ins H X
      · exact Or.inr ⟨hI, fun h => hn (Or.inr h)⟩
      · exact Or.inl ⟨⟨hgE, fun hs => hn (Or.inl ⟨hs, hI⟩)⟩, hI⟩
    · rintro (⟨⟨hgE, hgS⟩, hgI⟩ | ⟨hgI, hgn⟩)
      · exact ⟨hgE, by rintro (⟨hs, _⟩ | hs'); exacts [hgS hs, hgI (hSX'sub' hs')]⟩
      · exact ⟨ins_subset_edgeSet hgI, by rintro (⟨_, hI⟩ | hs'); exacts [hI hgI, hgn hs']⟩
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
  have hgood : Good H T ((S \ Ins H X) ∪ SX') :=
    ⟨hStilde, fun x y h => (hKK x y).1 (hcoarse x y h)⟩
  have hcomps : comps H (E(H) \ ((S \ Ins H X) ∪ SX')) = comps H (E(H) \ S) :=
    comps_congr (fun x y _ _ => (hKK x y).symm)
  have hmin' : ∀ S', Good H T S' →
      comps H (E(H) \ ((S \ Ins H X) ∪ SX')) ≤ comps H (E(H) \ S') := by
    intro S' h; rw [hcomps]; exact hmin S' h
  have hbr' := bridgeProp_of_min hV hE hgood hmin'
  have hgI : g ∈ Ins H X := mem_ins_of_link hgl haX hbX
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
  have hnfX : ¬ IsForest (H.induce X) ((E(H) \ S) ∩ Ins H X) := by
    intro hF
    refine forest_bridge hF (e := g) ⟨hgK, hgI⟩ (p := a) (q := b) ⟨hgl, haX, hbX⟩ ?_
    exact (reach_induce_iff (A := ((E(H) \ S) ∩ Ins H X) \ {g})
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
    have hceq : comps (H.induce X) (Ins H X \ SX') = comps (H.induce X) ((E(H) \ S) ∩ Ins H X) := by
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
  -- apply the bridge property of the new tree
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
  exact hbr' a f hfKt p q hfl ((hKK a p).1 hpR) hnrS' hpq


/-- Induction on the number of vertices: the exchange lemma (internal form). -/
theorem exchange_aux : ∀ n : ℕ, ∀ (H : Graph α β), V(H).ncard = n → V(H).Finite → E(H).Finite →
    (∀ e x, ¬ H.IsLink e x x) → (∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X) →
    ∀ T, IsSpanningTree H T → ∃ S, Good H T S ∧ IsForest H (E(H) \ S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hV hE hloop hno T hT
    have hgood0 : Good H T T := ⟨hT, fun _ _ h => h⟩
    classical
    have hex : ∃ c, ∃ S, Good H T S ∧ comps H (E(H) \ S) = c := ⟨_, T, hgood0, rfl⟩
    obtain ⟨S, hS, hSc⟩ := Nat.find_spec hex
    have hmin : ∀ S', Good H T S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S') := by
      intro S' h
      rw [hSc]
      exact Nat.find_min' hex ⟨S', h, rfl⟩
    refine ⟨S, hS, forest_of_min hV hE hloop hno ?_ hS hmin⟩
    intro X hXV hlt T' hT'
    obtain ⟨hV', hE'⟩ := finite_induce hV hE hXV
    exact ih X.ncard (hn ▸ hlt) (H.induce X) rfl hV' hE' (fun e x h => hloop e x h.1)
      (fun Y hY h2 hTT => hno Y (hY.trans hXV) h2 (isTwoTreeSet_of_induce hXV hY hTT)) T' hT'

/-- **Spanning-tree exchange** (`lem:characterization-exchange`).  Let `H` be a finite loopless
multigraph without a two-tree set of size at least two.  For every spanning tree `T` of `H` there
is a spanning tree `S` such that `H - E(S)` is a spanning forest and every two vertices connected
in `H - E(T)` are connected in `H - E(S)` (the component partition of `H - E(S)` coarsens that of
`H - E(T)`). -/
theorem exchange (hV : V(H).Finite) (hE : E(H).Finite) (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X) {T : Set β}
    (hT : IsSpanningTree H T) :
    ∃ S : Set β, IsSpanningTree H S ∧ (∃ k : ℕ, IsSpanningForest H (E(H) \ S) k) ∧
      ∀ x y, Reach H (E(H) \ T) x y → Reach H (E(H) \ S) x y := by
  obtain ⟨S, ⟨hS, hco⟩, hF⟩ := exchange_aux _ H rfl hV hE hloop hno T hT
  exact ⟨S, hS, ⟨comps H (E(H) \ S), (isSpanningForest_iff hV hE).2
    ⟨Set.sdiff_subset, rfl, forest_card hV hE Set.sdiff_subset hF⟩⟩, hco⟩


lemma mem_ins_univ (he : e ∈ E(H)) : e ∈ Ins H V(H) := by
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  exact mem_ins_of_link hl hl.left_mem hl.right_mem

/-- **Edge bound** (`cor:characterization-edges`).  A connected finite loopless multigraph with
`r ≥ 2` vertices and no two-tree set of size at least two has at most `2r - 3` edges
(stated as `|E| + 3 ≤ 2r`). -/
theorem edges_add_three_le (hV : V(H).Finite) (hE : E(H).Finite) (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X) (hr : 2 ≤ V(H).ncard)
    (hconn : ∀ x ∈ V(H), ∀ y ∈ V(H), Reach H E(H) x y) :
    E(H).ncard + 3 ≤ 2 * V(H).ncard := by
  have hne : V(H).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨T, -, hT⟩ := exists_spanning_tree_subset hV hE _ E(H) rfl subset_rfl hne hconn
  obtain ⟨S, hS, ⟨k, hk⟩, -⟩ := exchange hV hE hloop hno hT
  obtain ⟨-, hkc, hkn⟩ := (isSpanningForest_iff hV hE).1 hk
  obtain ⟨hSE, -, hSconn, hSn⟩ := (isSpanningTree_iff hV hE).1 hS
  have hKS : (E(H) \ S).ncard = E(H).ncard - S.ncard := Set.ncard_sdiff hSE (hE.subset hSE)
  have hSle : S.ncard ≤ E(H).ncard := Set.ncard_le_ncard hSE hE
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hc : comps H (E(H) \ S) = 1 := hkc
    obtain ⟨-, hKconn⟩ := (comps_eq_one_iff hV).1 hc
    apply hno V(H) subset_rfl hr
    rw [isTwoTreeSet_iff hV hE]
    refine ⟨hne, subset_rfl, S, E(H) \ S, fun z hz => mem_ins_univ (hSE hz),
      fun z hz => mem_ins_univ hz.1, Set.disjoint_sdiff_right, hSconn, hKconn⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 0 < comps H (E(H) \ S) := by
      unfold comps
      have : Nonempty (CC H (E(H) \ S)) := ⟨Quotient.mk _ ⟨hne.some, hne.some_mem⟩⟩
      have : Finite (CC H (E(H) \ S)) := by
        have : Finite V(H) := hV.to_subtype
        infer_instance
      exact Nat.card_pos
    omega
  omega

/-- The graph-theoretic core of `cor:characterization-t-case`: a connected finite loopless
multigraph with `r ≥ 2` vertices, `2r - 3` edges and no two-tree set of size at least two has a
`T`-witness (the quotient `Q` of the paper is such a graph). -/
theorem exists_tWitness_of_card_eq (hV : V(H).Finite) (hE : E(H).Finite)
    (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X) (hr : 2 ≤ V(H).ncard)
    (hconn : ∀ x ∈ V(H), ∀ y ∈ V(H), Reach H E(H) x y)
    (hcard : E(H).ncard + 3 = 2 * V(H).ncard) :
    ∃ T₁ T₂ : Set β, Lax630294.TGraph.IsTWitness H T₁ T₂ := by
  have hne : V(H).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨T, -, hT⟩ := exists_spanning_tree_subset hV hE _ E(H) rfl subset_rfl hne hconn
  obtain ⟨S, hS, ⟨k, hk⟩, -⟩ := exchange hV hE hloop hno hT
  obtain ⟨-, hkc, hkn⟩ := (isSpanningForest_iff hV hE).1 hk
  obtain ⟨hSE, -, hSconn, hSn⟩ := (isSpanningTree_iff hV hE).1 hS
  have hKS : (E(H) \ S).ncard = E(H).ncard - S.ncard := Set.ncard_sdiff hSE (hE.subset hSE)
  have hSle : S.ncard ≤ E(H).ncard := Set.ncard_le_ncard hSE hE
  have hk2 : k = 2 := by omega
  obtain ⟨e, heS, p, q, hel, hpq⟩ :
      ∃ e ∈ S, ∃ p q, H.IsLink e p q ∧ ¬ Reach H (E(H) \ S) p q := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x ∈ V(H), ∀ y ∈ V(H), Reach H (E(H) \ S) x y := fun x hx y hy =>
      reach_of_forall_step (fun g hg u v hl => hcon g hg u v hl) (hSconn x hx y hy)
    have := (comps_eq_one_iff hV).2 ⟨hne, hall⟩
    omega
  have heK : e ∉ E(H) \ S := fun h => h.2 heS
  have hc2 := comps_insert_of_not_reach hV hel hpq
  refine ⟨S, insert e (E(H) \ S), hS, ?_, ?_⟩
  · rw [isSpanningTree_iff hV hE]
    refine ⟨Set.insert_subset (hSE heS) Set.sdiff_subset, hne, ?_, ?_⟩
    · have : comps H (insert e (E(H) \ S)) = 1 := by omega
      exact ((comps_eq_one_iff hV).1 this).2
    · rw [Set.ncard_insert_of_notMem heK (hE.subset Set.sdiff_subset)]
      omega
  · have : S ∩ insert e (E(H) \ S) = {e} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzS, rfl | ⟨_, hz⟩⟩
        · rfl
        · exact absurd hzS hz
      · rintro rfl; exact ⟨heS, Or.inl rfl⟩
    rw [this]
    simp

end Lax630294Proofs.QuotientExchange
