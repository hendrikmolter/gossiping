import Lax630294.Gossiping
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Data.Set.Card
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Card

/-!
# Call orders on a simple graph: definitions and order-theoretic basics

Setting.  `H : Graph α β` is a finite simple graph, `P : β → β → Prop` a strict partial order
on its edges (`Admissible H P` below).  An *ideal* is a `P`-downward closed set of edges.
For a set `S` of edges, `Conn H S` is connectivity in the spanning subgraph `H[S]`; a
*component* of `H[S]` is recorded by its vertex set `A` (`IsComp H S A`).
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*}

/-- Hypotheses of the section "Causal Orders and Canonical Form": `H` is a finite simple graph,
`P` is a strict partial order on `E(H)` such that every linear extension is a complete call order
(`IsTemporallyConnected`) and every cover relation of `P` relates two edges sharing an
endpoint.  (The cover relation: `P a b` and no `c` with `P a c`, `P c b`.) -/
structure Admissible (H : Graph α β) (P : β → β → Prop) : Prop where
  simple : H.Simple
  finV : V(H).Finite
  finE : E(H).Finite
  irrefl : ∀ e, ¬ P e e
  trans : ∀ {a b c}, P a b → P b c → P a c
  mem_left : ∀ {a b}, P a b → a ∈ E(H)
  mem_right : ∀ {a b}, P a b → b ∈ E(H)
  complete : ∀ ℓ : β → ℕ, Set.InjOn ℓ E(H) → (∀ a b, P a b → ℓ a < ℓ b) →
    IsTemporallyConnected H ℓ
  cover_adj : ∀ {a b}, P a b → (∀ c, P a c → ¬ P c b) → ∃ x, H.Inc a x ∧ H.Inc b x

/-- An ideal: a `P`-downward closed set of edges of `H`. -/
def IsIdeal (H : Graph α β) (P : β → β → Prop) (I : Set β) : Prop :=
  I ⊆ E(H) ∧ ∀ a b, P a b → b ∈ I → a ∈ I

/-- Connectivity in the spanning subgraph `H[S]` (edge set `S`). -/
def Conn (H : Graph α β) (S : Set β) : α → α → Prop :=
  Relation.ReflTransGen (fun x y => ∃ e ∈ S, H.IsLink e x y)

/-- The edge `e` has both ends in `A`. -/
def Internal (H : Graph α β) (A : Set α) (e : β) : Prop :=
  ∃ x y, H.IsLink e x y ∧ x ∈ A ∧ y ∈ A

/-- The edge `e` has exactly one end in `A`. -/
def Crosses (H : Graph α β) (A : Set α) (e : β) : Prop :=
  ∃ x y, H.IsLink e x y ∧ x ∈ A ∧ y ∉ A

/-- The edges of `S` with both ends in `A`. -/
def edgesIn (H : Graph α β) (S : Set β) (A : Set α) : Set β :=
  {e | e ∈ S ∧ Internal H A e}

/-- `A` is the vertex set of a connected component of `H[S]`: nonempty, closed under the edges
of `S`, and connected by edges of `S`. -/
def IsComp (H : Graph α β) (S : Set β) (A : Set α) : Prop :=
  A.Nonempty ∧ A ⊆ V(H) ∧ (∀ e ∈ S, ∀ x y, H.IsLink e x y → x ∈ A → y ∈ A) ∧
    ∀ x ∈ A, ∀ y ∈ A, Conn H S x y

/-- A tree component of `H[S]`: a component with `|E| = |V| - 1`. -/
def IsTreeComp (H : Graph α β) (S : Set β) (A : Set α) : Prop :=
  IsComp H S A ∧ (edgesIn H S A).ncard + 1 = A.ncard

/-- A unicyclic component of `H[S]`: a component with `|E| = |V|`. -/
def IsUnicyclicComp (H : Graph α β) (S : Set β) (A : Set α) : Prop :=
  IsComp H S A ∧ (edgesIn H S A).ncard = A.ncard

/-- `f` is a `P`-minimal edge of the complement `E(H) \ I`. -/
def IsMinOut (H : Graph α β) (P : β → β → Prop) (I : Set β) (f : β) : Prop :=
  f ∈ E(H) ∧ f ∉ I ∧ ∀ g, P g f → g ∈ I

/-- A (tree) component `A` of the ideal `I` is *closed* if no minimal edge outside `I` is internal
to `A`.  (The paper's definition -- no larger ideal keeps `A` as a component and adds an internal
edge -- is equivalent; only this criterion, which the paper states as an equivalent form, is
used.) -/
def IsClosed (H : Graph α β) (P : β → β → Prop) (I : Set β) (A : Set α) : Prop :=
  ∀ f, IsMinOut H P I f → ¬ Internal H A f

section Order

variable {H : Graph α β} {P : β → β → Prop}

lemma Admissible.exists_min (hA : Admissible H P) {T : Set β} (hT : T ⊆ E(H))
    (hne : T.Nonempty) : ∃ x ∈ T, ∀ y ∈ T, ¬ P y x := by
  have : Finite E(H) := hA.finE.to_subtype
  let r : E(H) → E(H) → Prop := fun a b => P a b
  have : IsTrans E(H) r := ⟨fun a b c => hA.trans⟩
  have : Std.Irrefl r := ⟨fun a => hA.irrefl a⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨x, hx, hmin⟩ := wf.has_min {x : E(H) | x.1 ∈ T}
    (by obtain ⟨t, ht⟩ := hne; exact ⟨⟨t, hT ht⟩, ht⟩)
  exact ⟨x.1, hx, fun y hy hP => hmin ⟨y, hT hy⟩ hy hP⟩

lemma Admissible.exists_max (hA : Admissible H P) {T : Set β} (hT : T ⊆ E(H))
    (hne : T.Nonempty) : ∃ x ∈ T, ∀ y ∈ T, ¬ P x y := by
  have : Finite E(H) := hA.finE.to_subtype
  let r : E(H) → E(H) → Prop := fun a b => P b a
  have : IsTrans E(H) r := ⟨fun a b c h1 h2 => hA.trans h2 h1⟩
  have : Std.Irrefl r := ⟨fun a => hA.irrefl a⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨x, hx, hmin⟩ := wf.has_min {x : E(H) | x.1 ∈ T}
    (by obtain ⟨t, ht⟩ := hne; exact ⟨⟨t, hT ht⟩, ht⟩)
  exact ⟨x.1, hx, fun y hy hP => hmin ⟨y, hT hy⟩ hy hP⟩

lemma Admissible.asymm (hA : Admissible H P) {a b : β} (h : P a b) : ¬ P b a :=
  fun h' => hA.irrefl a (hA.trans h h')

/-- Below `f` and outside the ideal `J` there is a cover of `f`. -/
lemma Admissible.exists_cover_below (hA : Admissible H P) {J : Set β} (hJ : IsIdeal H P J)
    {f : β} (hf : ∃ g, P g f ∧ g ∉ J) :
    ∃ g, P g f ∧ g ∉ J ∧ ∀ c, P g c → ¬ P c f := by
  obtain ⟨g0, hg0, hg0J⟩ := hf
  obtain ⟨g, ⟨hgf, hgJ⟩, hmax⟩ := hA.exists_max (T := {g | P g f ∧ g ∉ J})
    (fun g hg => hA.mem_left hg.1) ⟨g0, hg0, hg0J⟩
  refine ⟨g, hgf, hgJ, fun c hgc hcf => ?_⟩
  have hcJ : c ∉ J := fun hc => hgJ (hJ.2 _ _ hgc hc)
  exact hmax c ⟨hcf, hcJ⟩ hgc

/-- Above `e`, inside the ideal `I`, there is a cover of `e`. -/
lemma Admissible.exists_cover_above (hA : Admissible H P) {I : Set β} (hI : IsIdeal H P I)
    {e : β} (hf : ∃ c ∈ I, P e c) :
    ∃ c ∈ I, P e c ∧ ∀ d, P e d → ¬ P d c := by
  obtain ⟨c0, hc0, hc0e⟩ := hf
  obtain ⟨c, ⟨hcI, hec⟩, hmin⟩ := hA.exists_min (T := {c | c ∈ I ∧ P e c})
    (fun c hc => hI.1 hc.1) ⟨c0, hc0, hc0e⟩
  refine ⟨c, hcI, hec, fun d hed hdc => ?_⟩
  exact hmin d ⟨hI.2 _ _ hdc hcI, hed⟩ hdc

lemma isIdeal_empty : IsIdeal H P ∅ := ⟨Set.empty_subset _, fun _ _ _ hb => hb.elim⟩

lemma IsIdeal.insert {I : Set β} (hI : IsIdeal H P I) {f : β} (hf : IsMinOut H P I f) :
    IsIdeal H P (insert f I) := by
  refine ⟨Set.insert_subset hf.1 hI.1, fun a b hab hb => ?_⟩
  rcases hb with rfl | hb
  · exact Or.inr (hf.2.2 a hab)
  · exact Or.inr (hI.2 a b hab hb)

/-- Every edge outside an ideal lies above-or-equal a minimal edge outside the ideal. -/
lemma Admissible.exists_minOut_le (hA : Admissible H P) {I : Set β}
    {g : β} (hgE : g ∈ E(H)) (hgI : g ∉ I) :
    ∃ f, IsMinOut H P I f ∧ (f = g ∨ P f g) := by
  obtain ⟨f, ⟨hfE, hfI, hfg⟩, hmin⟩ := hA.exists_min
    (T := {h | h ∈ E(H) ∧ h ∉ I ∧ (h = g ∨ P h g)})
    (fun h hh => hh.1) ⟨g, hgE, hgI, Or.inl rfl⟩
  refine ⟨f, ⟨hfE, hfI, fun h hh => ?_⟩, hfg⟩
  by_contra hhI
  refine hmin h ⟨hA.mem_left hh, hhI, Or.inr ?_⟩ hh
  rcases hfg with rfl | hfg
  · exact hh
  · exact hA.trans hh hfg

/-- Ideals of every size up to `|E(H)|` exist. -/
lemma Admissible.exists_ideal_ncard (hA : Admissible H P) {n : ℕ} (hn : n ≤ E(H).ncard) :
    ∃ I, IsIdeal H P I ∧ I.ncard = n := by
  induction n with
  | zero => exact ⟨∅, isIdeal_empty, by simp⟩
  | succ n ih =>
    obtain ⟨I, hI, hIn⟩ := ih (by omega)
    have hne : (E(H) \ I).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
      have := Set.ncard_le_ncard hcon (hA.finE.subset hI.1)
      omega
    obtain ⟨f, ⟨hfE, hfI⟩, _⟩ := hA.exists_min (T := E(H) \ I) Set.sdiff_subset hne
    obtain ⟨f', hfm, -⟩ := hA.exists_minOut_le (I := I) hfE hfI
    refine ⟨insert f' I, hI.insert hfm, ?_⟩
    rw [Set.ncard_insert_of_notMem hfm.2.1 (hA.finE.subset hI.1), hIn]

end Order

end Lax630294Proofs.CallOrder
