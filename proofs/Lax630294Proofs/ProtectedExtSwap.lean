import Lax630294Proofs.ProtectedExtCore

/-!
# Protected extension: the two moves that preserve the class `Cls`

* `swap_cls` : exchanging a non-bridge `h` of a non-special component of `K = E(H) \ S` against
  a boundary edge `f` of `S` keeps the class and decreases the number of components by one
  (the "merge" step of the paper's bridge property).
* `glue_cls` : replacing `S[X]` by another spanning tree of `X` (for `X` inside a non-special
  component) keeps the class and the components of `K`.
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β} {x0 x1 u0 u1 : α} {e f0 f1 g : β}

/-- The geometry of the four-cycle `x0 - x1 - u1 - u0 - x0`. -/
structure Geo (H : Graph α β) (x0 x1 u0 u1 : α) (e f0 f1 g : β) : Prop where
  le : H.IsLink e x0 x1
  lf0 : H.IsLink f0 x0 u0
  lf1 : H.IsLink f1 x1 u1
  lg : H.IsLink g u0 u1

/-- `a` is in a component of `K` containing none of the anchors. -/
def Ns (H : Graph α β) (x0 x1 u0 : α) (K : Set β) (a : α) : Prop :=
  ¬ Reach H K a x0 ∧ ¬ Reach H K a x1 ∧ ¬ Reach H K a u0

lemma reach_sdiff_iff {K : Set β} {h : β} {a b : α} (hl : H.IsLink h a b)
    (hcon : Reach H (K \ {h}) a b) {x y : α} : Reach H (K \ {h}) x y ↔ Reach H K x y :=
  ⟨reach_mono Set.sdiff_subset, reach_remove_edge hl hcon⟩

lemma Ns.ends {K : Set β} (geo : Geo H x0 x1 u0 u1 e f0 f1 g) (hgK : g ∈ K) {a0 : α}
    (hns : Ns H x0 x1 u0 K a0) :
    ¬ Reach H K a0 x0 ∧ ¬ Reach H K a0 x1 ∧ ¬ Reach H K a0 u0 ∧ ¬ Reach H K a0 u1 :=
  ⟨hns.1, hns.2.1, hns.2.2, fun h => hns.2.2 (h.trans' (reach_of_isLink hgK geo.lg.symm))⟩

/-- An edge with an end in a non-special component is none of the four cycle edges. -/
lemma prot_ne {K : Set β} (geo : Geo H x0 x1 u0 u1 e f0 f1 g) (hgK : g ∈ K) {a0 : α}
    (hns : Ns H x0 x1 u0 K a0) {f : β} {p q : α} (hfl : H.IsLink f p q) (hp : Reach H K a0 p) :
    f ≠ e ∧ f ≠ f0 ∧ f ≠ f1 ∧ f ≠ g := by
  obtain ⟨hx0, hx1, hu0, hu1⟩ := Ns.ends geo hgK hns
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    rcases hfl.eq_and_eq_or_eq_and_eq geo.le with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hx0 hp
    · exact hx1 hp
  · rintro rfl
    rcases hfl.eq_and_eq_or_eq_and_eq geo.lf0 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hx0 hp
    · exact hu0 hp
  · rintro rfl
    rcases hfl.eq_and_eq_or_eq_and_eq geo.lf1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hx1 hp
    · exact hu1 hp
  · rintro rfl
    rcases hfl.eq_and_eq_or_eq_and_eq geo.lg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hu0 hp
    · exact hu1 hp

lemma compl_swap {S : Set β} {h f : β} (hSE : S ⊆ E(H)) (hfS : f ∈ S) (hh : h ∈ E(H) \ S) :
    E(H) \ insert h (S \ {f}) = insert f ((E(H) \ S) \ {h}) := by
  ext k
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hgE, hg⟩
    by_cases hgS : k ∈ S
    · left; by_contra hgf; exact hg (Or.inr ⟨hgS, hgf⟩)
    · right; exact ⟨⟨hgE, hgS⟩, fun h' => hg (Or.inl h')⟩
  · rintro (h' | ⟨⟨hgE, hgS⟩, hge⟩)
    · subst h'
      refine ⟨hSE hfS, fun h' => ?_⟩
      rcases h' with h' | ⟨_, h'⟩
      · exact hh.2 (h' ▸ hfS)
      · exact h' rfl
    · exact ⟨hgE, fun h' => by rcases h' with h' | ⟨h', _⟩ <;> [exact hge h'; exact hgS h']⟩

/-- **The merge step.**  See the module docstring. -/
lemma swap_cls (hV : V(H).Finite) (hE : E(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    {S : Set β} (hS : Cls H x0 x1 u0 e f0 f1 g S) {a0 : α} (ha0 : a0 ∈ V(H))
    (hns : Ns H x0 x1 u0 (E(H) \ S) a0) {h : β} (hh : h ∈ E(H) \ S) {a b : α}
    (hl : H.IsLink h a b) (ha : Reach H (E(H) \ S) a0 a)
    (hcon : Reach H ((E(H) \ S) \ {h}) a b) {f : β} (hfS : f ∈ S) {p q : α}
    (hfl : H.IsLink f p q) (hp : Reach H (E(H) \ S) a0 p) (hq : ¬ Reach H (E(H) \ S) a0 q)
    (hnr : ¬ Reach H (S \ {f}) a b) :
    Cls H x0 x1 u0 e f0 f1 g (insert h (S \ {f})) ∧
      comps H (E(H) \ insert h (S \ {f})) + 1 = comps H (E(H) \ S) := by
  set K := E(H) \ S with hKdef
  have hSE : S ⊆ E(H) := hS.tree.1
  have hgK : g ∈ K := ⟨hS.hgE, hS.hgS⟩
  obtain ⟨hx0, hx1, hu0, hu1⟩ := Ns.ends geo hgK hns
  obtain ⟨hfe, hff0, hff1, hfg⟩ := prot_ne geo hgK hns hfl hp
  obtain ⟨hhe, hhf0, hhf1, hhg⟩ := prot_ne geo hgK hns hl ha
  have hSt' := tree_swap hV hE hS.tree hfS hl hnr
  have hK' : E(H) \ insert h (S \ {f}) = insert f (K \ {h}) := compl_swap hSE hfS hh
  have hKh : ∀ x y, Reach H (K \ {h}) x y ↔ Reach H K x y := fun x y => reach_sdiff_iff hl hcon
  obtain ⟨Z, hZ⟩ : ∃ Z : Set α, ∀ y, y ∈ Z ↔ Reach H K a0 y := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Set α, ∀ y, y ∈ W ↔ Reach H K q y := ⟨_, fun _ => Iff.rfl⟩
  have hqV : q ∈ V(H) := hfl.right_mem
  have hZV : Z ⊆ V(H) := fun y hy => reach_mem_of_mem ((hZ y).1 hy) ha0
  have hWV : W ⊆ V(H) := fun y hy => reach_mem_of_mem ((hW y).1 hy) hqV
  have hZW : ∀ y, y ∈ Z → y ∈ W → False := fun y h1 h2 =>
    hq (((hZ y).1 h1).trans' ((hW y).1 h2).symm')
  have hreach : ∀ x y, Reach H (insert f (K \ {h})) x y ↔
      Reach H K x y ∨ (x ∈ Z ∧ y ∈ W) ∨ (x ∈ W ∧ y ∈ Z) := by
    intro x y
    rw [reach_insert_iff hfl]
    simp only [hKh]
    have hxp : ∀ x, Reach H K x p ↔ x ∈ Z := fun x =>
      ⟨fun h' => (hZ x).2 (hp.trans' h'.symm'), fun h' => ((hZ x).1 h').symm'.trans' hp⟩
    have hxq : ∀ x, Reach H K x q ↔ x ∈ W := fun x =>
      ⟨fun h' => (hW x).2 h'.symm', fun h' => ((hW x).1 h').symm'⟩
    have hpy : ∀ y, Reach H K p y ↔ y ∈ Z := fun y =>
      ⟨fun h' => (hZ y).2 (hp.trans' h'), fun h' => hp.symm'.trans' ((hZ y).1 h')⟩
    have hqy : ∀ y, Reach H K q y ↔ y ∈ W := fun y => (hW y).symm
    simp only [hxp, hxq, hpy, hqy]
  have hx0Z : x0 ∉ Z := fun h' => hx0 ((hZ _).1 h')
  have hx1Z : x1 ∉ Z := fun h' => hx1 ((hZ _).1 h')
  have hu0Z : u0 ∉ Z := fun h' => hu0 ((hZ _).1 h')
  refine ⟨⟨hSt', ?_, ?_, ?_, hS.hgE, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Or.inr ⟨hS.he, hfe.symm⟩
  · exact Or.inr ⟨hS.hf0, hff0.symm⟩
  · exact Or.inr ⟨hS.hf1, hff1.symm⟩
  · rintro (h' | ⟨h', -⟩)
    · exact hhg h'.symm
    · exact hS.hgS h'
  · rw [hK']
    intro hr
    rcases (hreach _ _).1 hr with h' | ⟨h', -⟩ | ⟨-, h'⟩
    · exact hS.d01 h'
    · exact hx0Z h'
    · exact hx1Z h'
  · rw [hK']
    intro hr
    rcases (hreach _ _).1 hr with h' | ⟨h', -⟩ | ⟨-, h'⟩
    · exact hS.d0u h'
    · exact hx0Z h'
    · exact hu0Z h'
  · rw [hK']
    intro hr
    rcases (hreach _ _).1 hr with h' | ⟨h', -⟩ | ⟨-, h'⟩
    · exact hS.d1u h'
    · exact hx1Z h'
    · exact hu0Z h'
  · -- the invariant on non-special components
    rw [hK']
    intro A hA n0 n1 nu
    obtain ⟨v, hv⟩ := hA.1
    have hAeq : A = {y | CallOrder.Conn H (insert f (K \ {h})) v y} := hA.eq_comp hv
    have hmemA : ∀ y, y ∈ A ↔ Reach H (insert f (K \ {h})) v y := fun y => by
      rw [hAeq]; exact Iff.rfl
    have hKfin : K.Finite := hE.subset Set.sdiff_subset
    have hfK : f ∉ K := fun h' => h'.2 hfS
    by_cases hvZW : v ∈ Z ∨ v ∈ W
    · -- `A = Z ∪ W`
      have hAZW : ∀ y, y ∈ A ↔ y ∈ Z ∨ y ∈ W := by
        intro y
        rw [hmemA, hreach]
        constructor
        · rintro (h' | ⟨-, h'⟩ | ⟨-, h'⟩)
          · rcases hvZW with hvz | hvw
            · exact Or.inl ((hZ y).2 (((hZ v).1 hvz).trans' h'))
            · exact Or.inr ((hW y).2 (((hW v).1 hvw).trans' h'))
          · exact Or.inr h'
          · exact Or.inl h'
        · rintro (hy | hy)
          · rcases hvZW with hvz | hvw
            · exact Or.inl (((hZ v).1 hvz).symm'.trans' ((hZ y).1 hy))
            · exact Or.inr (Or.inr ⟨hvw, hy⟩)
          · rcases hvZW with hvz | hvw
            · exact Or.inr (Or.inl ⟨hvz, hy⟩)
            · exact Or.inl (((hW v).1 hvw).symm'.trans' ((hW y).1 hy))
      have hAset : A = Z ∪ W := Set.ext fun y => (hAZW y).trans (Set.mem_union y Z W).symm
      have hn0W : x0 ∉ W := fun h' => n0 ((hAZW _).2 (Or.inr h'))
      have hn1W : x1 ∉ W := fun h' => n1 ((hAZW _).2 (Or.inr h'))
      have hnuW : u0 ∉ W := fun h' => nu ((hAZW _).2 (Or.inr h'))
      have hZc : CallOrder.IsComp H K Z := by
        have : Z = {y | CallOrder.Conn H K a0 y} := Set.ext fun y => hZ y
        rw [this]; exact CallOrder.isComp_comp ha0
      have hWc : CallOrder.IsComp H K W := by
        have : W = {y | CallOrder.Conn H K q y} := Set.ext fun y => hW y
        rw [this]; exact CallOrder.isComp_comp hqV
      have hiZ : Z.ncard ≤ (CallOrder.edgesIn H K Z).ncard := hS.inv Z hZc hx0Z hx1Z hu0Z
      have hiW : W.ncard ≤ (CallOrder.edgesIn H K W).ncard := hS.inv W hWc hn0W hn1W hnuW
      have hZfin : Z.Finite := hV.subset hZV
      have hWfin : W.Finite := hV.subset hWV
      have hAcard : A.ncard = Z.ncard + W.ncard := by
        rw [hAset, Set.ncard_union_eq (Set.disjoint_left.2 fun y h1 h2 => hZW y h1 h2) hZfin hWfin]
      have hhZ : h ∈ CallOrder.edgesIn H K Z := by
        refine ⟨hh, a, b, hl, (hZ a).2 ha, (hZ b).2 (ha.trans' (reach_of_isLink hh hl))⟩
      have hEZfin : (CallOrder.edgesIn H K Z).Finite := hKfin.subset (fun k hk => hk.1)
      have hEWfin : (CallOrder.edgesIn H K W).Finite := hKfin.subset (fun k hk => hk.1)
      have hdisj : Disjoint (CallOrder.edgesIn H K Z \ {h}) (CallOrder.edgesIn H K W) := by
        refine Set.disjoint_left.2 fun k hk1 hk2 => ?_
        obtain ⟨x, y, hxy, hx, -⟩ := hk1.1.2
        have := hk2.2.ends_mem hxy
        exact hZW x hx this.1
      have hfn : f ∉ (CallOrder.edgesIn H K Z \ {h}) ∪ CallOrder.edgesIn H K W := by
        rintro (h' | h')
        · exact hfK h'.1.1
        · exact hfK h'.1
      have hsub : insert f ((CallOrder.edgesIn H K Z \ {h}) ∪ CallOrder.edgesIn H K W) ⊆
          CallOrder.edgesIn H (insert f (K \ {h})) A := by
        intro k hk
        rcases hk with rfl | hk | hk
        · refine ⟨Set.mem_insert _ _, p, q, hfl, ?_, ?_⟩
          · exact (hAZW p).2 (Or.inl ((hZ p).2 hp))
          · exact (hAZW q).2 (Or.inr ((hW q).2 reach_refl))
        · refine ⟨Or.inr ⟨hk.1.1, hk.2⟩, hk.1.2.mono ?_⟩
          rw [hAset]; exact Set.subset_union_left
        · refine ⟨Or.inr ⟨hk.1, ?_⟩, hk.2.mono ?_⟩
          · rintro rfl
            have := hk.2.ends_mem hl
            exact hZW a ((hZ a).2 ha) this.1
          · rw [hAset]; exact Set.subset_union_right
      have hEfin : (CallOrder.edgesIn H (insert f (K \ {h})) A).Finite :=
        hE.subset (CallOrder.edgesIn_subset _ _)
      have hc1 := Set.ncard_le_ncard hsub hEfin
      rw [Set.ncard_insert_of_notMem hfn ((hEZfin.sdiff).union hEWfin),
        Set.ncard_union_eq hdisj hEZfin.sdiff hEWfin,
        Set.ncard_sdiff_singleton_of_mem hhZ] at hc1
      have hpos : 0 < (CallOrder.edgesIn H K Z).ncard := (Set.ncard_pos hEZfin).2 ⟨h, hhZ⟩
      omega
    · -- `A` is a component of `K` away from `Z` and `W`
      push Not at hvZW
      obtain ⟨hvZ, hvW⟩ := hvZW
      have hmemA' : ∀ y, y ∈ A ↔ Reach H K v y := by
        intro y
        rw [hmemA, hreach]
        constructor
        · rintro (h' | ⟨h', -⟩ | ⟨h', -⟩)
          · exact h'
          · exact absurd h' hvZ
          · exact absurd h' hvW
        · exact Or.inl
      have hvV : v ∈ V(H) := hA.2.1 hv
      have hAc : CallOrder.IsComp H K A := by
        have : A = {y | CallOrder.Conn H K v y} := Set.ext fun y => hmemA' y
        rw [this]; exact CallOrder.isComp_comp hvV
      have hi : A.ncard ≤ (CallOrder.edgesIn H K A).ncard := hS.inv A hAc n0 n1 nu
      have hEfin : (CallOrder.edgesIn H (insert f (K \ {h})) A).Finite :=
        hE.subset (CallOrder.edgesIn_subset _ _)
      refine hi.trans (Set.ncard_le_ncard ?_ hEfin)
      intro k hk
      refine ⟨Or.inr ⟨hk.1, ?_⟩, hk.2⟩
      rintro rfl
      have hendA := hk.2.ends_mem hl
      have hva : Reach H K v a := (hmemA' a).1 hendA.1
      exact hvZ ((hZ v).2 (ha.trans' hva.symm'))
  · rw [hK']
    have hpq : ¬ Reach H (K \ {h}) p q := fun h' => hq (hp.trans' ((hKh _ _).1 h'))
    have h1 := comps_insert_of_not_reach hV hfl hpq
    have h2 : comps H (K \ {h}) = comps H K :=
      comps_congr (fun x y _ _ => hKh x y)
    omega

end Lax630294Proofs.ProtectedExt
