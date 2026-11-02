import Lax630294Proofs.CallOrderDefs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Components of `H[S]`, edge counting and tree components

Elementary theory of the components `IsComp H S A` of a spanning subgraph `H[S]`:
every component has at least `|A| - 1` edges (`ncard_le_edgesIn`), adding edges away from `A`
keeps `A` a component, deleting an edge of a tree component splits it into two tree components,
and `|S| - |V| + #components` is the sum of the *excess* `|E(A)| + 1 - |A|` of the components.
-/

namespace Lax630294Proofs.CallOrder

open Graph

variable {α β : Type*} {H : Graph α β}

section Conn

variable {S S' : Set β} {x y z : α}

lemma Conn.refl (x : α) : Conn H S x x := Relation.ReflTransGen.refl

lemma Conn.trans (h1 : Conn H S x y) (h2 : Conn H S y z) : Conn H S x z :=
  Relation.ReflTransGen.trans h1 h2

lemma Conn.single {e : β} (he : e ∈ S) (h : H.IsLink e x y) : Conn H S x y :=
  Relation.ReflTransGen.single ⟨e, he, h⟩

lemma Conn.symm (h : Conn H S x y) : Conn H S y x := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ hbc ih =>
    obtain ⟨e, he, hl⟩ := hbc
    exact (Conn.single he hl.symm).trans ih

lemma Conn.mono (hSS : S ⊆ S') (h : Conn H S x y) : Conn H S' x y := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ hbc ih =>
    obtain ⟨e, he, hl⟩ := hbc
    exact ih.trans (Conn.single (hSS he) hl)

lemma Conn.right_mem (h : Conn H S x y) (hx : x ∈ V(H)) : y ∈ V(H) := by
  induction h with
  | refl => exact hx
  | tail _ hbc _ =>
    obtain ⟨e, _, hl⟩ := hbc
    exact hl.right_mem

/-- Leaving a set along a walk uses an edge from inside to outside. -/
lemma Conn.exit_edge {B : Set α} (h : Conn H S x y) (hx : x ∈ B) (hy : y ∉ B) :
    ∃ u ∈ B, ∃ w, w ∉ B ∧ ∃ e ∈ S, H.IsLink e u w := by
  revert hy
  induction h with
  | refl => intro hy; exact absurd hx hy
  | tail _ hbc ih =>
    rename_i b c _
    intro hc
    by_cases hbB : b ∈ B
    · obtain ⟨e, he, hl⟩ := hbc
      exact ⟨b, hbB, c, hc, e, he, hl⟩
    · exact ih hbB

lemma conn_remove {J : Set β} {a : β} {u v : α} (hl : H.IsLink a u v) {y : α}
    (h : Conn H J u y) : Conn H (J \ {a}) u y ∨ Conn H (J \ {a}) v y := by
  induction h with
  | refl => exact Or.inl (Conn.refl _)
  | tail _ hbc ih =>
    rename_i b c _
    obtain ⟨e, he, hl'⟩ := hbc
    by_cases hea : e = a
    · subst hea
      rcases hl'.right_eq_or_eq hl with rfl | rfl
      · exact Or.inl (Conn.refl _)
      · exact Or.inr (Conn.refl _)
    · have hmem : e ∈ J \ {a} := ⟨he, hea⟩
      rcases ih with ih | ih
      · exact Or.inl (ih.trans (Conn.single hmem hl'))
      · exact Or.inr (ih.trans (Conn.single hmem hl'))

end Conn

section Comp

variable {S S' : Set β} {A B : Set α} {x y z : α} {e : β}

lemma Internal.ends_mem (h : Internal H A e) {u v : α} (hl : H.IsLink e u v) :
    u ∈ A ∧ v ∈ A := by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  rcases hl.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hx, hy⟩
  · exact ⟨hy, hx⟩

lemma Internal.mono (h : Internal H A e) (hAB : A ⊆ B) : Internal H B e := by
  obtain ⟨x, y, hl, hx, hy⟩ := h
  exact ⟨x, y, hl, hAB hx, hAB hy⟩

lemma IsComp.mem_of_conn (h : IsComp H S A) (hx : x ∈ A) (hxy : Conn H S x y) : y ∈ A := by
  induction hxy with
  | refl => exact hx
  | tail _ hbc ih =>
    obtain ⟨e, he, hl⟩ := hbc
    exact h.2.2.1 e he _ _ hl ih

lemma IsComp.link_iff (h : IsComp H S A) (he : e ∈ S) {x y : α} (hl : H.IsLink e x y) :
    x ∈ A ↔ y ∈ A :=
  ⟨h.2.2.1 e he _ _ hl, h.2.2.1 e he _ _ hl.symm⟩

lemma isComp_comp (hx : x ∈ V(H)) : IsComp H S {y | Conn H S x y} :=
  ⟨⟨x, Conn.refl x⟩, fun _ hy => hy.right_mem hx,
    fun _ he _ _ hl ha => ha.trans (Conn.single he hl), fun _ ha _ hb => ha.symm.trans hb⟩

lemma IsComp.eq_comp (h : IsComp H S A) (hx : x ∈ A) : A = {y | Conn H S x y} :=
  Set.ext fun _ => ⟨fun hy => h.2.2.2 x hx _ hy, fun hy => h.mem_of_conn hx hy⟩

lemma IsComp.eq_of_mem (hA : IsComp H S A) (hB : IsComp H S B) (hx : x ∈ A) (hxB : x ∈ B) :
    A = B :=
  (hA.eq_comp hx).trans (hB.eq_comp hxB).symm

lemma IsComp.disjoint_of_ne (hA : IsComp H S A) (hB : IsComp H S B) (hne : A ≠ B) :
    Disjoint A B :=
  Set.disjoint_left.2 fun _ hxA hxB => hne (hA.eq_of_mem hB hxA hxB)

lemma edgesIn_subset (S : Set β) (A : Set α) : edgesIn H S A ⊆ E(H) := by
  rintro e ⟨-, x, y, hl, -, -⟩
  exact hl.edge_mem

lemma edgesIn_subset_S (S : Set β) (A : Set α) : edgesIn H S A ⊆ S := fun _ h => h.1

/-- A component spans a connected piece, so it has at least `|A| - 1` edges. -/
lemma ncard_le_edgesIn (hV : V(H).Finite) (hE : E(H).Finite) (h : IsComp H S A) :
    A.ncard ≤ (edgesIn H S A).ncard + 1 := by
  have hAfin : A.Finite := hV.subset h.2.1
  have hEfin : (edgesIn H S A).Finite := hE.subset (edgesIn_subset S A)
  obtain ⟨a0, ha0⟩ := h.1
  have key : ∀ k : ℕ, k + 1 ≤ A.ncard → ∃ B ⊆ A, B.ncard = k + 1 ∧ ∃ T ⊆ edgesIn H S A,
      (∀ e ∈ T, Internal H B e) ∧ T.ncard + 1 = B.ncard := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨{a0}, by simpa using ha0, by simp, ∅, by simp, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨B, hBA, hBc, T, hTsub, hTint, hTc⟩ := ih (by omega)
      have hBfin : B.Finite := hAfin.subset hBA
      have hTfin : T.Finite := hEfin.subset hTsub
      have hexists : ∃ y ∈ A, y ∉ B := by
        by_contra hcon
        have hAB : A ⊆ B := fun y hy => by
          by_contra hyB
          exact hcon ⟨y, hy, hyB⟩
        have := Set.ncard_le_ncard hAB hBfin
        omega
      obtain ⟨y, hyA, hyB⟩ := hexists
      have hB0 : B.Nonempty := (Set.ncard_pos hBfin).1 (by omega)
      obtain ⟨b0, hb0⟩ := hB0
      obtain ⟨u, huB, w, hwB, e, heS, hl⟩ :=
        (h.2.2.2 b0 (hBA hb0) y hyA).exit_edge hb0 hyB
      have hwA : w ∈ A := h.2.2.1 e heS u w hl (hBA huB)
      have heT : e ∉ T := by
        intro heT
        obtain ⟨x', y', hxy, hx', hy'⟩ := hTint e heT
        rcases hl.right_eq_or_eq hxy with rfl | rfl
        · exact hwB hx'
        · exact hwB hy'
      refine ⟨insert w B, Set.insert_subset hwA hBA, ?_, insert e T, ?_, ?_, ?_⟩
      · rw [Set.ncard_insert_of_notMem hwB hBfin, hBc]
      · exact Set.insert_subset ⟨heS, u, w, hl, hBA huB, hwA⟩ hTsub
      · intro e' he'
        rcases he' with rfl | he'
        · exact ⟨u, w, hl, Set.mem_insert_of_mem _ huB, Set.mem_insert _ _⟩
        · exact (hTint e' he').mono (Set.subset_insert _ _)
      · rw [Set.ncard_insert_of_notMem heT hTfin, Set.ncard_insert_of_notMem hwB hBfin]
        omega
  have hpos : 0 < A.ncard := (Set.ncard_pos hAfin).2 ⟨a0, ha0⟩
  obtain ⟨B, -, hBc, T, hTsub, -, hTc⟩ := key (A.ncard - 1) (by omega)
  have := Set.ncard_le_ncard hTsub hEfin
  omega

/-- Adding edges that do not touch `A` keeps `A` a component with the same edges. -/
lemma IsComp.mono_edges (h : IsComp H S A) (hSS : S ⊆ S')
    (hnew : ∀ e ∈ S', e ∉ S → ∀ x y, H.IsLink e x y → x ∉ A ∧ y ∉ A) :
    IsComp H S' A ∧ edgesIn H S' A = edgesIn H S A := by
  refine ⟨⟨h.1, h.2.1, ?_, fun x hx y hy => (h.2.2.2 x hx y hy).mono hSS⟩, ?_⟩
  · intro e he x y hl hx
    by_cases heS : e ∈ S
    · exact h.2.2.1 e heS x y hl hx
    · exact absurd hx (hnew e he heS x y hl).1
  · ext e
    constructor
    · rintro ⟨he, hint⟩
      refine ⟨?_, hint⟩
      by_contra heS
      obtain ⟨x, y, hl, hx, -⟩ := hint
      exact (hnew e he heS x y hl).1 hx
    · rintro ⟨he, hint⟩
      exact ⟨hSS he, hint⟩

/-- Deleting an edge of a tree component splits it into two tree components. -/
lemma tree_split (hV : V(H).Finite) (hE : E(H).Finite) {J : Set β} {A : Set α}
    (hA : IsTreeComp H J A) {a : β} (ha : a ∈ edgesIn H J A) {u v : α} (hl : H.IsLink a u v) :
    ∃ A1 A2, IsTreeComp H (J \ {a}) A1 ∧ IsTreeComp H (J \ {a}) A2 ∧ Disjoint A1 A2 ∧
      A1 ∪ A2 = A ∧ u ∈ A1 ∧ v ∈ A2 := by
  obtain ⟨hAc, hcard⟩ := hA
  have hSJ : J \ {a} ⊆ J := fun e he => he.1
  obtain ⟨huA, hvA⟩ := ha.2.ends_mem hl
  have huV : u ∈ V(H) := hl.left_mem
  have hvV : v ∈ V(H) := hl.right_mem
  let A1 : Set α := {y | Conn H (J \ {a}) u y}
  let A2 : Set α := {y | Conn H (J \ {a}) v y}
  have hA1 : IsComp H (J \ {a}) A1 := isComp_comp huV
  have hA2 : IsComp H (J \ {a}) A2 := isComp_comp hvV
  have hcov : A ⊆ A1 ∪ A2 := by
    intro x hx
    rcases conn_remove hl (hAc.2.2.2 u huA x hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsub1 : A1 ⊆ A := fun y hy => hAc.mem_of_conn huA (hy.mono hSJ)
  have hsub2 : A2 ⊆ A := fun y hy => hAc.mem_of_conn hvA (hy.mono hSJ)
  have hunion : A1 ∪ A2 = A := Set.Subset.antisymm (Set.union_subset hsub1 hsub2) hcov
  have hEA : edgesIn H (J \ {a}) A = edgesIn H J A \ {a} := by
    ext e
    constructor
    · rintro ⟨⟨he, hne⟩, hint⟩
      exact ⟨⟨he, hint⟩, hne⟩
    · rintro ⟨⟨he, hint⟩, hne⟩
      exact ⟨⟨he, hne⟩, hint⟩
  have hEfin : (edgesIn H J A).Finite := hE.subset (edgesIn_subset J A)
  have hdisj : Disjoint A1 A2 := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have hAS' : IsComp H (J \ {a}) A := by
      refine ⟨hAc.1, hAc.2.1, fun e he x y hl hx => hAc.2.2.1 e (hSJ he) x y hl hx, ?_⟩
      intro x hx x' hx'
      have key : ∀ z ∈ A, Conn H (J \ {a}) u z := by
        intro z hz
        rcases hcov hz with h | h
        · exact h
        · exact (hy1.trans hy2.symm).trans h
      exact (key x hx).symm.trans (key x' hx')
    have h1 := ncard_le_edgesIn hV hE hAS'
    rw [hEA, Set.ncard_sdiff_singleton_of_mem ha] at h1
    have hpos : 0 < (edgesIn H J A).ncard := (Set.ncard_pos hEfin).2 ⟨a, ha⟩
    omega
  have hE1fin : (edgesIn H (J \ {a}) A1).Finite := hE.subset (edgesIn_subset _ _)
  have hE2fin : (edgesIn H (J \ {a}) A2).Finite := hE.subset (edgesIn_subset _ _)
  have hE12 : Disjoint (edgesIn H (J \ {a}) A1) (edgesIn H (J \ {a}) A2) :=
    Set.disjoint_left.2 fun e h1 h2 => by
      obtain ⟨x, y, hxy, hx1, hy1⟩ := h1.2
      obtain ⟨x', y', hxy', hx2, hy2⟩ := h2.2
      rcases hxy.left_eq_or_eq hxy' with rfl | rfl
      · exact Set.disjoint_left.1 hdisj hx1 hx2
      · exact Set.disjoint_left.1 hdisj hx1 hy2
  have hEdecomp : edgesIn H J A =
      insert a (edgesIn H (J \ {a}) A1 ∪ edgesIn H (J \ {a}) A2) := by
    ext e
    constructor
    · intro h
      by_cases hea : e = a
      · exact Or.inl hea
      · right
        obtain ⟨heJ, x, y, hxy, hx, hy⟩ := h
        have heS : e ∈ J \ {a} := ⟨heJ, hea⟩
        rcases hcov hx with hx1 | hx2
        · exact Or.inl ⟨heS, x, y, hxy, hx1, (hA1.link_iff heS hxy).1 hx1⟩
        · exact Or.inr ⟨heS, x, y, hxy, hx2, (hA2.link_iff heS hxy).1 hx2⟩
    · intro h
      rcases h with rfl | h | h
      · exact ha
      · exact ⟨hSJ h.1, h.2.mono hsub1⟩
      · exact ⟨hSJ h.1, h.2.mono hsub2⟩
  have haN : a ∉ edgesIn H (J \ {a}) A1 ∪ edgesIn H (J \ {a}) A2 := by
    rintro (h | h)
    · exact h.1.2 rfl
    · exact h.1.2 rfl
  have hcE : (edgesIn H J A).ncard =
      (edgesIn H (J \ {a}) A1).ncard + (edgesIn H (J \ {a}) A2).ncard + 1 := by
    rw [hEdecomp, Set.ncard_insert_of_notMem haN (hE1fin.union hE2fin),
      Set.ncard_union_eq hE12 hE1fin hE2fin]
  have hA1fin : A1.Finite := hV.subset hA1.2.1
  have hA2fin : A2.Finite := hV.subset hA2.2.1
  have hcA : A.ncard = A1.ncard + A2.ncard := by
    rw [← hunion, Set.ncard_union_eq hdisj hA1fin hA2fin]
  have k1 := ncard_le_edgesIn hV hE hA1
  have k2 := ncard_le_edgesIn hV hE hA2
  exact ⟨A1, A2, ⟨hA1, by omega⟩, ⟨hA2, by omega⟩, hdisj, hunion, Conn.refl u, Conn.refl v⟩

end Comp

section Sums

variable {S : Set β} {A : Set α}

open Classical in
/-- The (finite) set of vertex sets of the components of `H[S]`. -/
noncomputable def comps (hV : V(H).Finite) (S : Set β) : Finset (Set α) :=
  hV.toFinset.image (fun x => {y | Conn H S x y})

lemma mem_comps (hV : V(H).Finite) : A ∈ comps hV S ↔ IsComp H S A := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    exact isComp_comp (hV.mem_toFinset.1 hx)
  · intro h
    obtain ⟨x, hx⟩ := h.1
    exact Finset.mem_image.2 ⟨x, hV.mem_toFinset.2 (h.2.1 hx), (h.eq_comp hx).symm⟩

lemma sum_card_comps (hV : V(H).Finite) :
    ∑ A ∈ comps hV S, A.ncard = V(H).ncard := by
  classical
  have h1 := Finset.card_eq_sum_card_fiberwise (s := hV.toFinset) (t := comps hV S)
    (f := fun x => {y | Conn H S x y}) (fun x hx => by
      unfold comps
      exact Finset.mem_image_of_mem _ hx)
  rw [Set.ncard_eq_toFinset_card V(H) hV, h1]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAc := (mem_comps hV).1 hA
  rw [Set.ncard_eq_toFinset_card A (hV.subset hAc.2.1)]
  symm
  congr 1
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨-, hx⟩
    rw [← hx]
    exact Conn.refl x
  · intro hx
    exact ⟨hAc.2.1 hx, (hAc.eq_comp hx).symm⟩

lemma sum_edges_comps (hV : V(H).Finite) (hE : E(H).Finite) (hS : S ⊆ E(H)) :
    ∑ A ∈ comps hV S, (edgesIn H S A).ncard = S.ncard := by
  classical
  have hSfin : S.Finite := hE.subset hS
  by_cases hS0 : S = ∅
  · subst hS0
    rw [Set.ncard_empty]
    refine Finset.sum_eq_zero fun A _ => ?_
    have : edgesIn H (∅ : Set β) A = ∅ := by
      ext e; simp [edgesIn]
    simp [this]
  obtain ⟨e0, he0⟩ := Set.nonempty_iff_ne_empty.2 hS0
  obtain ⟨x0, hx0⟩ := exists_isLink_of_mem_edgeSet (hS he0)
  obtain ⟨y0, hy0⟩ := hx0
  have : Nonempty α := ⟨x0⟩
  have hinc : ∀ e ∈ S, ∃ x, H.Inc e x := fun e he => by
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet (hS he)
    exact ⟨x, y, hl⟩
  choose! g hg using hinc
  have h1 := Finset.card_eq_sum_card_fiberwise (s := hSfin.toFinset) (t := comps hV S)
    (f := fun e => {y | Conn H S (g e) y}) (fun e he => by
      have heS := hSfin.mem_toFinset.1 he
      unfold comps
      exact Finset.mem_image_of_mem _ (hV.mem_toFinset.2 (hg e heS).vertex_mem))
  rw [Set.ncard_eq_toFinset_card S hSfin, h1]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAc := (mem_comps hV).1 hA
  rw [Set.ncard_eq_toFinset_card _ (hE.subset (edgesIn_subset S A))]
  symm
  congr 1
  ext e
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨heS, hcomp⟩
    refine ⟨heS, ?_⟩
    obtain ⟨w, hw⟩ := hg e heS
    have hgA : g e ∈ A := by rw [← hcomp]; exact Conn.refl _
    exact ⟨g e, w, hw, hgA, hAc.2.2.1 e heS _ _ hw hgA⟩
  · rintro ⟨heS, hint⟩
    refine ⟨heS, ?_⟩
    obtain ⟨w, hw⟩ := hg e heS
    have hgA : g e ∈ A := (hint.ends_mem hw).1
    exact (hAc.eq_comp hgA).symm

/-- The excess `|E(A)| + 1 - |A|` of a component. -/
noncomputable def excess (H : Graph α β) (S : Set β) (A : Set α) : ℕ := (edgesIn H S A).ncard + 1 - A.ncard

lemma isTreeComp_iff (hV : V(H).Finite) (hE : E(H).Finite) (h : IsComp H S A) :
    IsTreeComp H S A ↔ excess H S A = 0 := by
  have := ncard_le_edgesIn hV hE h
  unfold excess IsTreeComp
  simp only [h, true_and]
  omega

lemma sum_excess (hV : V(H).Finite) (hE : E(H).Finite) (hS : S ⊆ E(H)) :
    S.ncard + (comps hV S).card = V(H).ncard + ∑ A ∈ comps hV S, excess H S A := by
  have h1 := sum_edges_comps hV hE hS
  have h2 := sum_card_comps (S := S) hV
  have h3 : ∑ A ∈ comps hV S, ((edgesIn H S A).ncard + 1) = S.ncard + (comps hV S).card := by
    rw [Finset.sum_add_distrib, h1]; simp
  have h4 : ∑ A ∈ comps hV S, (A.ncard + excess H S A) =
      ∑ A ∈ comps hV S, ((edgesIn H S A).ncard + 1) := by
    refine Finset.sum_congr rfl fun A hA => ?_
    have := ncard_le_edgesIn hV hE ((mem_comps hV).1 hA)
    unfold excess
    omega
  rw [Finset.sum_add_distrib, h2] at h4
  omega

/-- `|S| = |V| - 2` forces at least two tree components. -/
lemma exists_two_tree_comps (hV : V(H).Finite) (hE : E(H).Finite) (hS : S ⊆ E(H))
    (hcard : S.ncard + 2 = V(H).ncard) :
    ∃ A B, IsTreeComp H S A ∧ IsTreeComp H S B ∧ A ≠ B := by
  classical
  have hid := sum_excess hV hE hS
  set C := comps hV S with hC
  have hTN : (C.filter (fun A => excess H S A = 0)).card +
      (C.filter (fun A => ¬ excess H S A = 0)).card = C.card :=
    Finset.card_filter_add_card_filter_not _
  have hN : (C.filter (fun A => ¬ excess H S A = 0)).card ≤ ∑ A ∈ C, excess H S A := by
    calc (C.filter (fun A => ¬ excess H S A = 0)).card
        = ∑ A ∈ C.filter (fun A => ¬ excess H S A = 0), 1 := by simp
      _ ≤ ∑ A ∈ C.filter (fun A => ¬ excess H S A = 0), excess H S A :=
          Finset.sum_le_sum (fun A hA => Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hA).2)
      _ ≤ ∑ A ∈ C, excess H S A := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 : 1 < (C.filter (fun A => excess H S A = 0)).card := by omega
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.1 h2
  rw [Finset.mem_filter, hC, mem_comps hV] at hA hB
  exact ⟨A, B, (isTreeComp_iff hV hE hA.1).2 hA.2, (isTreeComp_iff hV hE hB.1).2 hB.2, hAB⟩

/-- If `|S| = |V| - 2` and the tree components are exactly `X` and `Y`, all other components
are unicyclic. -/
lemma unicyclic_of_two_trees (hV : V(H).Finite) (hE : E(H).Finite) (hS : S ⊆ E(H))
    (hcard : S.ncard + 2 = V(H).ncard) {X Y : Set α} (hX : IsTreeComp H S X)
    (hY : IsTreeComp H S Y) (hXY : X ≠ Y) (hall : ∀ A, IsTreeComp H S A → A = X ∨ A = Y)
    {D : Set α} (hD : IsComp H S D) (hDX : D ≠ X) (hDY : D ≠ Y) : IsUnicyclicComp H S D := by
  classical
  have hid := sum_excess hV hE hS
  set C := comps hV S with hC
  set T := C.filter (fun A => excess H S A = 0) with hT
  set N := C.filter (fun A => ¬ excess H S A = 0) with hN
  have hTN : T.card + N.card = C.card := Finset.card_filter_add_card_filter_not _
  have hTeq : T = {X, Y} := by
    ext A
    simp only [hT, Finset.mem_filter, hC, mem_comps hV, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hA, h0⟩
      exact hall A ((isTreeComp_iff hV hE hA).2 h0)
    · rintro (rfl | rfl)
      · exact ⟨hX.1, (isTreeComp_iff hV hE hX.1).1 hX⟩
      · exact ⟨hY.1, (isTreeComp_iff hV hE hY.1).1 hY⟩
  have hT2 : T.card = 2 := by rw [hTeq]; exact Finset.card_pair hXY
  have hsplit : ∑ A ∈ C, excess H S A = ∑ A ∈ N, excess H S A := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun A => excess H S A = 0)]
    have : ∑ A ∈ T, excess H S A = 0 :=
      Finset.sum_eq_zero fun A hA => (Finset.mem_filter.1 hA).2
    rw [this, zero_add]
  have hDN : D ∈ N := by
    rw [hN, Finset.mem_filter, hC, mem_comps hV]
    refine ⟨hD, fun h0 => ?_⟩
    rcases hall D ((isTreeComp_iff hV hE hD).2 h0) with h | h
    · exact hDX h
    · exact hDY h
  have hge : ∀ A ∈ N, 1 ≤ excess H S A := fun A hA =>
    Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hA).2
  have hexD : excess H S D = 1 := by
    by_contra hne
    have hlt : ∑ A ∈ N, 1 < ∑ A ∈ N, excess H S A :=
      Finset.sum_lt_sum hge ⟨D, hDN, by have := hge D hDN; omega⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt
    omega
  have := ncard_le_edgesIn hV hE hD
  unfold excess at hexD
  exact ⟨hD, by omega⟩

end Sums

end Lax630294Proofs.CallOrder
