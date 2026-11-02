import Lax630294.MGraph
import Lax630294Proofs.ThreePhase
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Core multigraph library for the necessity proof

Connectivity by an edge set (`Reach`), the number of components of a spanning subgraph (`comps`),
and the counting characterisation of forests and spanning trees:

* `rank_ineq`:  `|V| ≤ |F| + comps F`, with equality iff `F` is a forest;
* `isSpanningTree_iff`, `isSpanningForest_iff` : count characterisations of the frozen notions.
-/

namespace Lax630294Proofs.QuotientCore

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase

variable {α β : Type*} {G : Graph α β} {F F' : Set β} {x y z a b : α} {e f : β}

/-- `x` and `y` are connected by edges of `F`. -/
abbrev Reach (G : Graph α β) (F : Set β) : α → α → Prop :=
  Relation.ReflTransGen (step G F)

lemma reach_refl : Reach G F x x := Relation.ReflTransGen.refl

lemma Reach.trans' {x y z : α} (h1 : Reach G F x y) (h2 : Reach G F y z) : Reach G F x z :=
  Relation.ReflTransGen.trans h1 h2

lemma Reach.symm' {x y : α} (h : Reach G F x y) : Reach G F y x :=
  rtg_symm (fun _ _ => step_symm) h

lemma reach_of_isLink (he : e ∈ F) (h : G.IsLink e x y) : Reach G F x y :=
  Relation.ReflTransGen.single ⟨e, he, h⟩

lemma reach_mono (h : F ⊆ F') (hr : Reach G F x y) : Reach G F' x y :=
  by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => obtain ⟨e, he, hl⟩ := hs; exact ih.tail ⟨e, h he, hl⟩

lemma reach_mem_of_mem (h : Reach G F x y) (hx : x ∈ V(G)) : y ∈ V(G) := by
  induction h with
  | refl => exact hx
  | tail _ hs _ => obtain ⟨e, _, hl⟩ := hs; exact hl.right_mem

lemma reach_eq_or_mem (h : Reach G F x y) (hxy : x ≠ y) : x ∈ V(G) := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨e, _, hl⟩, _⟩
  · exact absurd h hxy
  · exact hl.left_mem

/-- The setoid of connectivity on the vertex set. -/
def reachSetoid (G : Graph α β) (F : Set β) : Setoid V(G) where
  r x y := Reach G F x y
  iseqv := ⟨fun _ => reach_refl, fun h => h.symm', fun h1 h2 => h1.trans' h2⟩

/-- The set of connected components of the spanning subgraph `(V(G), F)`. -/
abbrev CC (G : Graph α β) (F : Set β) : Type _ := Quotient (reachSetoid G F)

/-- The number of connected components of the spanning subgraph `(V(G), F)`. -/
noncomputable def comps (G : Graph α β) (F : Set β) : ℕ := Nat.card (CC G F)

lemma comps_congr (hr : ∀ x y, x ∈ V(G) → y ∈ V(G) → (Reach G F x y ↔ Reach G F' x y)) :
    comps G F = comps G F' :=
  Nat.card_congr (Quotient.congr (Equiv.refl _) (fun x y => hr x y x.2 y.2))

lemma reach_insert_iff {a b : α} (hl : G.IsLink e a b) :
    Reach G (insert e F) x y ↔
      Reach G F x y ∨ (Reach G F x a ∧ Reach G F b y) ∨ (Reach G F x b ∧ Reach G F a y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl reach_refl
    | @tail w y _ hs ih =>
      obtain ⟨f, hf, hfl⟩ := hs
      rcases hf with rfl | hf
      · rcases hl.eq_and_eq_or_eq_and_eq hfl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inl ⟨h, reach_refl⟩)
          · exact Or.inl (h1.trans' h2.symm')
          · exact Or.inl h1
        · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inr ⟨h, reach_refl⟩)
          · exact Or.inl h1
          · exact Or.inl (h1.trans' h2.symm')
      · have hst : Reach G F w y := reach_of_isLink hf hfl
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans' hst)
        · exact Or.inr (Or.inl ⟨h1, h2.trans' hst⟩)
        · exact Or.inr (Or.inr ⟨h1, h2.trans' hst⟩)
  · have hm : ∀ {u v}, Reach G F u v → Reach G (insert e F) u v :=
      fun h => reach_mono (Set.subset_insert _ _) h
    have he : Reach G (insert e F) a b := reach_of_isLink (Set.mem_insert _ _) hl
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hm h
    · exact (hm h1).trans' (he.trans' (hm h2))
    · exact (hm h1).trans' (he.symm'.trans' (hm h2))

lemma comps_insert_of_reach {a b : α} (hl : G.IsLink e a b) (h : Reach G F a b) :
    comps G (insert e F) = comps G F := by
  refine comps_congr (fun x y _ _ => ?_)
  rw [reach_insert_iff hl]
  constructor
  · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h'
    · exact h1.trans' (h.trans' h2)
    · exact h1.trans' (h.symm'.trans' h2)
  · exact Or.inl

lemma comps_insert_of_not_reach (hV : V(G).Finite) {a b : α} (hl : G.IsLink e a b)
    (h : ¬ Reach G F a b) : comps G (insert e F) + 1 = comps G F := by
  have hfin : Finite V(G) := hV.to_subtype
  have ha : a ∈ V(G) := hl.left_mem
  have hb : b ∈ V(G) := hl.right_mem
  -- the canonical surjection
  let f : CC G F → CC G (insert e F) :=
    Quotient.map' id (fun x y h => reach_mono (Set.subset_insert _ _) h)
  let u : CC G F := Quotient.mk _ ⟨a, ha⟩
  let w : CC G F := Quotient.mk _ ⟨b, hb⟩
  have hfeq : ∀ c d : CC G F, f c = f d → c = d ∨ (c = u ∧ d = w) ∨ (c = w ∧ d = u) := by
    intro c d
    induction c using Quotient.inductionOn with | _ c =>
    induction d using Quotient.inductionOn with | _ d =>
    intro hcd
    have : Reach G (insert e F) c d := Quotient.exact hcd
    rw [reach_insert_iff hl] at this
    rcases this with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Quotient.sound h')
    · refine Or.inr (Or.inl ⟨Quotient.sound h1, Quotient.sound h2.symm'⟩)
    · refine Or.inr (Or.inr ⟨Quotient.sound h1, Quotient.sound h2.symm'⟩)
  have hfu : f u = f w := by
    apply Quotient.sound
    exact (reach_of_isLink (Set.mem_insert _ _) hl)
  have hfsurj : Function.Surjective f := by
    intro z
    induction z using Quotient.inductionOn with | _ z =>
    exact ⟨Quotient.mk _ z, rfl⟩
  have huw : u ≠ w := by
    intro h'
    exact h (Quotient.exact h')
  let g : {c : CC G F // c ≠ w} → CC G (insert e F) := fun c => f c.1
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
      have := hfeq c d hcd
      rcases this with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h'
      · exact absurd h2 hd
      · exact absurd h1 hc
    · intro z
      obtain ⟨c, rfl⟩ := hfsurj z
      by_cases hc : c = w
      · refine ⟨⟨u, huw⟩, ?_⟩
        simp only [g]
        rw [hfu, hc]
      · exact ⟨⟨c, hc⟩, rfl⟩
  have h1 : Nat.card {c : CC G F // c ≠ w} = comps G (insert e F) :=
    Nat.card_congr (Equiv.ofBijective g hg)
  have h2 : Nat.card {c : CC G F // c ≠ w} + 1 = comps G F := by
    classical
    have := Fintype.ofFinite (CC G F)
    unfold comps
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card (CC G F) := Fintype.card_pos_iff.2 ⟨w⟩
    omega
  omega

lemma reach_empty_iff : Reach G (∅ : Set β) x y ↔ x = y := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨e, he, _⟩, _⟩
    · exact h
    · exact absurd he (Set.notMem_empty _)
  · rintro rfl; exact reach_refl

lemma comps_empty : comps G (∅ : Set β) = Nat.card V(G) := by
  unfold comps
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift (fun x : V(G) => x) ?_) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (reach_empty_iff.1 h)
  · intro c d
    induction c using Quotient.inductionOn with | _ c =>
    induction d using Quotient.inductionOn with | _ d =>
    intro h
    have hcd : c = d := h
    subst hcd
    rfl
  · intro x; exact ⟨Quotient.mk _ x, rfl⟩

/-! ### Interaction with Mathlib's simple graphs -/

lemma underlying_adj {F : Set β} {u v : V(G)} :
    (underlying G F).Adj u v ↔ u ≠ v ∧ ∃ f ∈ F, G.IsLink f u v := by
  exact Iff.rfl

lemma underlying_reachable_iff (u v : V(G)) :
    (underlying G F).Reachable u v ↔ Reach G F u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact reach_refl
    | tail _ hs ih =>
      obtain ⟨_, f, hf, hl⟩ := underlying_adj.1 hs
      exact ih.tail ⟨f, hf, hl⟩
  · intro h
    have key : ∀ {w : α}, Reach G F u w → ∀ hw : w ∈ V(G),
        Relation.ReflTransGen (underlying G F).Adj u ⟨w, hw⟩ := by
      intro w hr
      induction hr with
      | refl => intro hw; exact Relation.ReflTransGen.refl
      | @tail m w' hr hs ih =>
        intro hw
        obtain ⟨f, hf, hl⟩ := hs
        have hm : m ∈ V(G) := hl.left_mem
        by_cases hmw : m = w'
        · subst hmw; exact ih hm
        · exact (ih hm).tail (underlying_adj.2 ⟨fun h => hmw (congrArg Subtype.val h), f, hf, hl⟩)
    exact key h v.2

lemma underlying_mono (h : F ⊆ F') : underlying G F ≤ underlying G F' := by
  intro u v huv
  obtain ⟨hne, f, hf, hl⟩ := underlying_adj.1 huv
  exact underlying_adj.2 ⟨hne, f, h hf, hl⟩

lemma underlying_insert {a b : α} (hl : G.IsLink e a b) :
    underlying G (insert e F) = underlying G F ⊔
      SimpleGraph.edge (⟨a, hl.left_mem⟩ : V(G)) ⟨b, hl.right_mem⟩ := by
  ext u v
  rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj, underlying_adj, underlying_adj]
  constructor
  · rintro ⟨hne, f, hf, hfl⟩
    rcases hf with rfl | hf
    · right
      refine ⟨?_, hne⟩
      rcases hl.eq_and_eq_or_eq_and_eq hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨Subtype.ext h1.symm, Subtype.ext h2.symm⟩
      · right; exact ⟨Subtype.ext h2.symm, Subtype.ext h1.symm⟩
    · exact Or.inl ⟨hne, f, hf, hfl⟩
  · rintro (⟨hne, f, hf, hfl⟩ | ⟨hs, hne⟩)
    · exact ⟨hne, f, Or.inr hf, hfl⟩
    · refine ⟨hne, e, Or.inl rfl, ?_⟩
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hl
      · rw [h1, h2]; exact hl.symm

/-! ### Forests and the rank inequality -/

/-- `F` is a forest of `G`: it is simple (no loops, no parallel edges) and acyclic. -/
def IsForest (G : Graph α β) (F : Set β) : Prop :=
  (G.restrict F).Simple ∧ (underlying G F).IsAcyclic

lemma simple_restrict_empty : (G.restrict (∅ : Set β)).Simple :=
  { not_isLoopAt := fun e x h => by simp [Graph.IsLoopAt] at h
    eq_of_isLink := fun e f x y he _ => by simp at he }

lemma underlying_empty : underlying G (∅ : Set β) = ⊥ := by
  ext u v
  rw [underlying_adj]
  simp

lemma isForest_empty : IsForest G (∅ : Set β) :=
  ⟨simple_restrict_empty, by rw [underlying_empty]; exact SimpleGraph.isAcyclic_bot⟩

lemma IsForest.mono (h : IsForest G F') (hss : F ⊆ F') : IsForest G F := by
  obtain ⟨hs, ha⟩ := h
  exact ⟨Graph.Simple.anti (G := G.restrict F') (Graph.restrict_mono_right G hss),
    ha.anti (underlying_mono hss)⟩

lemma reach_of_link_same_ends {g : β} {a b x y : α} (hg : g ∈ F) (hl : G.IsLink e a b)
    (hgl : G.IsLink g x y) (hel : G.IsLink e x y) : Reach G F a b := by
  rcases hl.eq_and_eq_or_eq_and_eq hel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact reach_of_isLink hg hgl
  · exact reach_of_isLink hg hgl.symm

lemma isForest_insert_iff_of_not_reach {a b : α} (hl : G.IsLink e a b) (h : ¬ Reach G F a b) :
    IsForest G (insert e F) ↔ IsForest G F := by
  refine ⟨fun h' => h'.mono (Set.subset_insert _ _), fun ⟨hs, ha⟩ => ⟨?_, ?_⟩⟩
  · refine { not_isLoopAt := fun f x hf => ?_, eq_of_isLink := fun f g x y hf hg => ?_ }
    · obtain ⟨hfm, hfl⟩ := hf
      rcases hfm with rfl | hfm
      · rcases hl.eq_and_eq_or_eq_and_eq hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hab : a = b := h1.trans h2.symm
          subst hab; exact h reach_refl
        · have hab : a = b := h1.trans h2.symm
          subst hab; exact h reach_refl
      · exact hs.not_isLoopAt f x ⟨hfm, hfl⟩
    · obtain ⟨hfm, hfl⟩ := hf
      obtain ⟨hgm, hgl⟩ := hg
      rcases hfm with rfl | hfm <;> rcases hgm with rfl | hgm
      · rfl
      · exact absurd (reach_of_link_same_ends hgm hl hgl hfl) h
      · exact absurd (reach_of_link_same_ends hfm hl hfl hgl) h
      · exact hs.eq_of_isLink ⟨hfm, hfl⟩ ⟨hgm, hgl⟩
  · rw [underlying_insert hl]
    refine (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable _ _ ?_).2 ha
    rw [underlying_reachable_iff]
    exact h

lemma not_isForest_insert_of_reach {a b : α} (hl : G.IsLink e a b) (he : e ∉ F)
    (h : Reach G F a b) : ¬ IsForest G (insert e F) := by
  rintro ⟨hs, ha⟩
  by_cases hab : a = b
  · subst hab
    exact hs.not_isLoopAt e a ⟨Set.mem_insert _ _, hl⟩
  · have hnadj : ¬ (underlying G F).Adj ⟨a, hl.left_mem⟩ ⟨b, hl.right_mem⟩ := by
      intro hadj
      obtain ⟨_, g, hg, hgl⟩ := underlying_adj.1 hadj
      have : e = g := hs.eq_of_isLink ⟨Set.mem_insert _ _, hl⟩ ⟨Set.mem_insert_of_mem _ hg, hgl⟩
      exact he (this ▸ hg)
    rw [underlying_insert hl] at ha
    have := (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.1 ha).2
      ((underlying_reachable_iff _ _).2 h)
    rcases this with h1 | h1
    · exact hab (congrArg Subtype.val h1)
    · exact hnadj h1

theorem rank_ineq (hV : V(G).Finite) {F : Set β} (hF : F.Finite) :
    F ⊆ E(G) → V(G).ncard ≤ F.ncard + comps G F ∧
      (V(G).ncard = F.ncard + comps G F ↔ IsForest G F) := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _
    rw [comps_empty, Set.ncard_empty, Nat.card_coe_set_eq]
    exact ⟨by omega, ⟨fun _ => isForest_empty, fun _ => by omega⟩⟩
  | @insert e F hnot hfin ih =>
    intro hsub
    have he : e ∈ E(G) := hsub (Set.mem_insert _ _)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem _ hx))
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    rw [Set.ncard_insert_of_notMem hnot hfin]
    by_cases hr : Reach G F a b
    · rw [comps_insert_of_reach hl hr]
      refine ⟨by omega, ⟨fun h => by omega, fun h => ?_⟩⟩
      exact absurd h (not_isForest_insert_of_reach hl hnot hr)
    · have := comps_insert_of_not_reach hV hl hr
      refine ⟨by omega, ?_⟩
      rw [isForest_insert_iff_of_not_reach hl hr, ← ih2]
      omega

/-! ### Counting characterisation of the frozen notions -/

lemma natCard_cc (G : Graph α β) (F : Set β) :
    Nat.card (underlying G F).ConnectedComponent = comps G F :=
  Nat.card_congr (Quot.congr (Equiv.refl _) (fun x y => underlying_reachable_iff x y))

lemma comps_eq_one_iff (_hV : V(G).Finite) :
    comps G F = 1 ↔ V(G).Nonempty ∧ ∀ x ∈ V(G), ∀ y ∈ V(G), Reach G F x y := by
  unfold comps
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, ⟨c⟩⟩
    induction c using Quotient.inductionOn with | _ c =>
    refine ⟨⟨c, c.2⟩, fun x hx y hy => ?_⟩
    have := @Subsingleton.elim _ hsub (Quotient.mk _ ⟨x, hx⟩) (Quotient.mk _ ⟨y, hy⟩)
    exact Quotient.exact this
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨fun c d => ?_⟩, ⟨Quotient.mk _ ⟨x, hx⟩⟩⟩
    induction c using Quotient.inductionOn with | _ c =>
    induction d using Quotient.inductionOn with | _ d =>
    exact Quotient.sound (h _ c.2 _ d.2)

theorem isSpanningForest_iff (hV : V(G).Finite) (hE : E(G).Finite) {F : Set β} {k : ℕ} :
    IsSpanningForest G F k ↔ F ⊆ E(G) ∧ comps G F = k ∧ F.ncard + k = V(G).ncard := by
  have : Finite V(G) := hV.to_subtype
  constructor
  · rintro ⟨hFE, hs, ha, hk⟩
    have hc : comps G F = k := by
      rw [ENat.card_eq_coe_natCard, natCard_cc] at hk
      exact_mod_cast hk
    obtain ⟨_, h2⟩ := rank_ineq hV (hE.subset hFE) hFE
    have := h2.2 ⟨hs, ha⟩
    exact ⟨hFE, hc, by omega⟩
  · rintro ⟨hFE, hc, hn⟩
    obtain ⟨_, h2⟩ := rank_ineq hV (hE.subset hFE) hFE
    obtain ⟨hs, ha⟩ := h2.1 (by omega)
    refine ⟨hFE, hs, ha, ?_⟩
    rw [ENat.card_eq_coe_natCard, natCard_cc, hc]

theorem isSpanningTree_iff (hV : V(G).Finite) (hE : E(G).Finite) {T : Set β} :
    IsSpanningTree G T ↔ T ⊆ E(G) ∧ V(G).Nonempty ∧
      (∀ x ∈ V(G), ∀ y ∈ V(G), Reach G T x y) ∧ T.ncard + 1 = V(G).ncard := by
  have : Finite V(G) := hV.to_subtype
  constructor
  · rintro ⟨hTE, hs, hconn, hac⟩
    have hne : V(G).Nonempty := by
      obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
      exact ⟨x, hx⟩
    have hr : ∀ x ∈ V(G), ∀ y ∈ V(G), Reach G T x y := fun x hx y hy =>
      (underlying_reachable_iff ⟨x, hx⟩ ⟨y, hy⟩).1 (hconn.preconnected _ _)
    have hc := (comps_eq_one_iff hV).2 ⟨hne, hr⟩
    obtain ⟨_, h2⟩ := rank_ineq hV (hE.subset hTE) hTE
    have := h2.2 ⟨hs, hac⟩
    exact ⟨hTE, hne, hr, by omega⟩
  · rintro ⟨hTE, hne, hr, hn⟩
    have hc := (comps_eq_one_iff hV).2 ⟨hne, hr⟩
    obtain ⟨_, h2⟩ := rank_ineq hV (hE.subset hTE) hTE
    obtain ⟨hs, ha⟩ := h2.1 (by omega)
    have : Nonempty V(G) := hne.to_subtype
    exact ⟨hTE, hs, ⟨fun u v => (underlying_reachable_iff u v).2 (hr _ u.2 _ v.2)⟩, ha⟩

/-! ### Forest toolbox -/

lemma forest_card (hV : V(G).Finite) (hE : E(G).Finite) (hFE : F ⊆ E(G)) (hF : IsForest G F) :
    F.ncard + comps G F = V(G).ncard :=
  ((rank_ineq hV (hE.subset hFE) hFE).2.2 hF).symm

lemma isForest_of_card (hV : V(G).Finite) (hE : E(G).Finite) (hFE : F ⊆ E(G))
    (h : F.ncard + comps G F = V(G).ncard) : IsForest G F :=
  (rank_ineq hV (hE.subset hFE) hFE).2.1 h.symm

/-- In a forest every edge is a bridge. -/
lemma forest_bridge {p q : α} (hF : IsForest G F) (he : e ∈ F) (hl : G.IsLink e p q) :
    ¬ Reach G (F \ {e}) p q := by
  intro h
  have := not_isForest_insert_of_reach hl (by simp) h
  rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem he] at this
  exact this hF

lemma exists_nonbridge (hFfin : F.Finite) (hFE : F ⊆ E(G)) (hF : ¬ IsForest G F) :
    ∃ e ∈ F, ∃ p q, G.IsLink e p q ∧ Reach G (F \ {e}) p q := by
  by_contra hcon
  push Not at hcon
  apply hF
  clear hF
  induction F, hFfin using Set.Finite.induction_on with
  | empty => exact isForest_empty
  | @insert e F hnot hfin ih =>
    have ih' : IsForest G F := by
      refine ih (fun x hx => hFE (Set.mem_insert_of_mem _ hx)) (fun f hf p q hl hr => ?_)
      exact hcon f (Set.mem_insert_of_mem _ hf) p q hl
        (reach_mono (Set.sdiff_subset_sdiff_left (Set.subset_insert _ _)) hr)
    have he : e ∈ E(G) := hFE (Set.mem_insert _ _)
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    rw [isForest_insert_iff_of_not_reach hl]
    · exact ih'
    · intro hr
      refine hcon e (Set.mem_insert _ _) a b hl ?_
      rwa [Set.insert_sdiff_self_of_notMem hnot]

lemma reach_remove_edge {p q : α} (hl : G.IsLink e p q) (hpq : Reach G (F \ {e}) p q)
    (h : Reach G F x y) : Reach G (F \ {e}) x y := by
  induction h with
  | refl => exact reach_refl
  | tail _ hs ih =>
    obtain ⟨f, hf, hfl⟩ := hs
    by_cases hfe : f = e
    · subst hfe
      rcases hl.eq_and_eq_or_eq_and_eq hfl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans' hpq
      · exact ih.trans' hpq.symm'
    · exact ih.trans' (reach_of_isLink ⟨hf, hfe⟩ hfl)

/-- A connected edge set contains a spanning tree. -/
theorem exists_spanning_tree_subset (hV : V(G).Finite) (hE : E(G).Finite) :
    ∀ n : ℕ, ∀ F : Set β, F.ncard = n → F ⊆ E(G) → V(G).Nonempty →
      (∀ x ∈ V(G), ∀ y ∈ V(G), Reach G F x y) → ∃ T ⊆ F, IsSpanningTree G T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hn hFE hne hconn
    by_cases hF : IsForest G F
    · refine ⟨F, subset_rfl, (isSpanningTree_iff hV hE).2 ⟨hFE, hne, hconn, ?_⟩⟩
      have := forest_card hV hE hFE hF
      have hc := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
      omega
    · obtain ⟨e, he, p, q, hl, hr⟩ := exists_nonbridge (hE.subset hFE) hFE hF
      have hfin : F.Finite := hE.subset hFE
      have hcard : (F \ {e}).ncard < n := by
        rw [Set.ncard_sdiff_singleton_of_mem he]
        have : 0 < F.ncard := Set.ncard_pos hfin |>.2 ⟨e, he⟩
        omega
      obtain ⟨T, hT, hTt⟩ := ih _ hcard (F \ {e}) rfl (Set.sdiff_subset.trans hFE) hne
        (fun x hx y hy => reach_remove_edge hl hr (hconn x hx y hy))
      exact ⟨T, hT.trans Set.sdiff_subset, hTt⟩

/-- Cut lemma: if `a` and `b` are connected by `F'` but not by the subset `F₀`, some edge `f` of
`F' \ F₀` has ends `p, q` with `a ~ p` and `q ~ b` in `F' \ {f}`. -/
lemma cut_lemma {F₀ F' : Set β} (hsub : F₀ ⊆ F') (hfin : F'.Finite) (hF'E : F' ⊆ E(G))
    {a b : α} (h' : Reach G F' a b) (h₀ : ¬ Reach G F₀ a b) :
    ∃ f ∈ F' \ F₀, ∃ p q, G.IsLink f p q ∧ Reach G (F' \ {f}) a p ∧ Reach G (F' \ {f}) q b := by
  have key : ∀ D : Set β, D.Finite → D ⊆ F' \ F₀ → Reach G (F₀ ∪ D) a b →
      ∃ f ∈ D, ∃ p q, G.IsLink f p q ∧ Reach G (F₀ ∪ (D \ {f})) a p ∧
        Reach G (F₀ ∪ (D \ {f})) q b := by
    intro D hD
    induction D, hD using Set.Finite.induction_on with
    | empty => intro _ h; simp at h; exact absurd h h₀
    | @insert d D hnot hDfin ih =>
      intro hsubD h
      have hdE : d ∈ E(G) := hF'E (hsubD (Set.mem_insert _ _)).1
      obtain ⟨p, q, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hdE
      have heq : F₀ ∪ insert d D = insert d (F₀ ∪ D) := by
        rw [Set.union_insert]
      rw [heq, reach_insert_iff hl] at h
      have hD' : F₀ ∪ (insert d D \ {d}) = F₀ ∪ D := by
        rw [Set.insert_sdiff_self_of_notMem hnot]
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨f, hf, p', q', hl', h1', h2'⟩ :=
          ih (fun x hx => hsubD (Set.mem_insert_of_mem _ hx)) h
        have hmono : F₀ ∪ (D \ {f}) ⊆ F₀ ∪ (insert d D \ {f}) :=
          Set.union_subset_union_right _ (Set.sdiff_subset_sdiff_left (Set.subset_insert _ _))
        exact ⟨f, Set.mem_insert_of_mem _ hf, p', q', hl', reach_mono hmono h1',
          reach_mono hmono h2'⟩
      · exact ⟨d, Set.mem_insert _ _, p, q, hl, by rw [hD']; exact h1, by rw [hD']; exact h2⟩
      · exact ⟨d, Set.mem_insert _ _, q, p, hl.symm, by rw [hD']; exact h1,
          by rw [hD']; exact h2⟩
  obtain ⟨f, hf, p, q, hl, h1, h2⟩ := key (F' \ F₀) (hfin.subset Set.sdiff_subset) subset_rfl
    (by rwa [Set.union_sdiff_cancel hsub])
  refine ⟨f, hf, p, q, hl, reach_mono ?_ h1, reach_mono ?_ h2⟩ <;>
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨hsub hx, fun h => hf.2 (h ▸ hx)⟩
    · exact ⟨hx.1.1, hx.2⟩

/-- Exchanging an edge of a spanning tree. -/
lemma tree_swap (hV : V(G).Finite) (hE : E(G).Finite) {S : Set β} (hS : IsSpanningTree G S)
    (hfS : f ∈ S) {a b : α} (hl : G.IsLink e a b) (hnr : ¬ Reach G (S \ {f}) a b) :
    IsSpanningTree G (insert e (S \ {f})) := by
  rw [isSpanningTree_iff hV hE] at hS ⊢
  obtain ⟨hSE, hne, hconn, hcard⟩ := hS
  have hSfin : S.Finite := hE.subset hSE
  obtain ⟨p, q, hfl⟩ := Graph.exists_isLink_of_mem_edgeSet (hSE hfS)
  have hc := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
  have hforest : IsForest G S := isForest_of_card hV hE hSE (by omega)
  have hpq : ¬ Reach G (S \ {f}) p q := forest_bridge hforest hfS hfl
  have hS' : insert f (S \ {f}) = S := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hfS]
  have hside : ∀ x ∈ V(G), Reach G (S \ {f}) x p ∨ Reach G (S \ {f}) x q := by
    intro x hx
    have := hconn x hx p hfl.left_mem
    rw [← hS', reach_insert_iff hfl] at this
    rcases this with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  have hmono : ∀ {u v}, Reach G (S \ {f}) u v → Reach G (insert e (S \ {f})) u v :=
    fun h => reach_mono (Set.subset_insert _ _) h
  have hab' : Reach G (insert e (S \ {f})) a b := reach_of_isLink (Set.mem_insert _ _) hl
  have hpq' : Reach G (insert e (S \ {f})) p q := by
    rcases hside a hl.left_mem with ha | ha <;> rcases hside b hl.right_mem with hb | hb
    · exact absurd (ha.trans' hb.symm') hnr
    · exact (hmono ha.symm').trans' (hab'.trans' (hmono hb))
    · exact (hmono hb.symm').trans' (hab'.symm'.trans' (hmono ha))
    · exact absurd (ha.trans' hb.symm') hnr
  refine ⟨?_, hne, ?_, ?_⟩
  · exact Set.insert_subset hl.edge_mem (Set.sdiff_subset.trans hSE)
  · intro x hx y hy
    have key : ∀ {y : α}, Reach G S x y → Reach G (insert e (S \ {f})) x y := by
      intro y h
      induction h with
      | refl => exact reach_refl
      | tail _ hs ih =>
        obtain ⟨g, hg, hgl⟩ := hs
        by_cases hgf : g = f
        · subst hgf
          rcases hfl.eq_and_eq_or_eq_and_eq hgl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans' hpq'
          · exact ih.trans' hpq'.symm'
        · exact ih.trans' (hmono (reach_of_isLink ⟨hg, hgf⟩ hgl))
    exact key (hconn x hx y hy)
  · have hen : e ∉ S \ {f} := fun h => hnr (reach_of_isLink h hl)
    rw [Set.ncard_insert_of_notMem hen (hSfin.subset Set.sdiff_subset),
      Set.ncard_sdiff_singleton_of_mem hfS]
    have : 0 < S.ncard := Set.ncard_pos hSfin |>.2 ⟨f, hfS⟩
    omega

end Lax630294Proofs.QuotientCore
