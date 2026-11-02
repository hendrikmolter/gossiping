import Lax630294Proofs.CallOrderExt
import Lax630294Proofs.CallOrderComp
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Information flow: translating completeness of linear extensions

For a linear extension `ℓ` of `P` that places the ideal `I` before all other edges, a vertex
`v` incident to no edge outside `I` can only receive secrets along temporal paths inside `I`
(`need_conn`, `need_conn_last`).  This gives the "first call" injection of the paper.
-/

namespace Lax630294Proofs.CallOrder

open Graph Lax630294.Gossiping

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop}

/-- The edges of a path (in the `HasTemporalPath` encoding) lying in `S` connect its ends. -/
lemma conn_of_path {S : Set β} {k : ℕ} {x : Fin (k + 1) → α} {e : Fin k → β}
    (hl : ∀ i : Fin k, H.IsLink (e i) (x i.castSucc) (x i.succ)) (hS : ∀ i, e i ∈ S) :
    Conn H S (x 0) (x (Fin.last k)) := by
  have : ∀ n (hn : n ≤ k), Conn H S (x 0) (x ⟨n, by omega⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Conn.refl _
    | succ n ih =>
      intro hn
      exact (ih (by omega)).trans (Conn.single (hS ⟨n, by omega⟩) (hl ⟨n, by omega⟩))
  exact this k le_rfl

/-- A temporal path ending at a vertex without incident edges outside the ideal `I`
(for a labeling placing `I` first) only uses edges of `I`. -/
lemma path_edges_in_ideal {I : Set β} {ℓ : β → ℕ}
    (hIF : ∀ g ∈ I, ∀ f ∈ E(H) \ I, ℓ g < ℓ f) {v : α}
    (hv : ∀ f ∈ E(H) \ I, ¬ H.Inc f v) {k : ℕ} {x : Fin (k + 1) → α} {e : Fin k → β}
    (hxk : x (Fin.last k) = v) (hl : ∀ i : Fin k, H.IsLink (e i) (x i.castSucc) (x i.succ))
    (hmono : StrictMono (fun i => ℓ (e i))) : ∀ i, e i ∈ I := by
  intro i
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := i.2; omega⟩
  have hlast := hl (Fin.last k')
  rw [Fin.succ_last, hxk] at hlast
  have hlastI : e (Fin.last k') ∈ I := by
    by_contra hnot
    exact hv _ ⟨hlast.edge_mem, hnot⟩ hlast.inc_right
  by_contra hi
  have h1 := hIF _ hlastI (e i) ⟨(hl i).edge_mem, hi⟩
  have h2 : ℓ (e i) ≤ ℓ (e (Fin.last k')) := hmono.monotone (Fin.le_last i)
  omega

/-- A vertex outside the edges `E \ I` receives every secret along edges of `I`. -/
lemma need_conn (hA : Admissible H P) {I : Set β} {ℓ : β → ℕ} (hinj : Set.InjOn ℓ E(H))
    (hP : ∀ a b, P a b → ℓ a < ℓ b)
    (hIF : ∀ g ∈ I, ∀ f ∈ E(H) \ I, ℓ g < ℓ f) {v : α} (hv : v ∈ V(H))
    (hnone : ∀ f ∈ E(H) \ I, ¬ H.Inc f v) {s : α} (hs : s ∈ V(H)) : Conn H I s v := by
  obtain ⟨k, x, e, hx0, hxk, -, hl, hmono⟩ := hA.complete ℓ hinj hP s hs v hv
  have := path_edges_in_ideal hIF hnone hxk hl hmono
  have h := conn_of_path (S := I) hl this
  rwa [hx0, hxk] at h

/-- Variant when `e ∈ I` is the last edge of `I`: either `s` reaches `v` in `I \ {e}`, or `v` is
an end of `e`. -/
lemma need_conn_last (hA : Admissible H P) {I : Set β} {ℓ : β → ℕ} (hinj : Set.InjOn ℓ E(H))
    (hP : ∀ a b, P a b → ℓ a < ℓ b)
    (hIF : ∀ g ∈ I, ∀ f ∈ E(H) \ I, ℓ g < ℓ f) {e : β} (_heI : e ∈ I)
    (hlast : ∀ g ∈ I, g ≠ e → ℓ g < ℓ e) {v : α} (hv : v ∈ V(H))
    (hnone : ∀ f ∈ E(H) \ I, ¬ H.Inc f v) {s : α} (hs : s ∈ V(H)) :
    Conn H (I \ {e}) s v ∨ H.Inc e v := by
  obtain ⟨k, x, e', hx0, hxk, -, hl, hmono⟩ := hA.complete ℓ hinj hP s hs v hv
  have hall := path_edges_in_ideal hIF hnone hxk hl hmono
  by_cases hex : ∃ j, e' j = e
  · right
    obtain ⟨j, hj⟩ := hex
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := j.2; omega⟩
    have hjl : j = Fin.last k' := by
      by_contra hne
      have hlt : j < Fin.last k' := lt_of_le_of_ne (Fin.le_last j) hne
      have h1 : ℓ (e' j) < ℓ (e' (Fin.last k')) := hmono hlt
      rw [hj] at h1
      by_cases heq : e' (Fin.last k') = e
      · rw [heq] at h1; exact lt_irrefl _ h1
      · exact absurd (hlast _ (hall _) heq) (not_lt.2 h1.le)
    subst hjl
    have hlk := hl (Fin.last k')
    rw [Fin.succ_last, hxk, hj] at hlk
    exact hlk.inc_right
  · left
    push Not at hex
    have h := conn_of_path (S := I \ {e}) hl (fun i => ⟨hall i, hex i⟩)
    rwa [hx0, hxk] at h

/-- There is a complete linear extension. -/
lemma Admissible.exists_extension (hA : Admissible H P) :
    ∃ ℓ : β → ℕ, Set.InjOn ℓ E(H) ∧ ∀ a b, P a b → ℓ a < ℓ b := by
  obtain ⟨ℓ, h1, h2, -⟩ := exists_linear_ext hA.finE P hA.irrefl hA.trans
    (fun h => ⟨hA.mem_left h, hA.mem_right h⟩) (fun _ => 0) (fun _ => le_rfl)
  exact ⟨ℓ, h1, h2⟩

/-- Completeness implies connectivity of `H`. -/
lemma Admissible.conn_all (hA : Admissible H P) {x y : α} (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    Conn H E(H) x y := by
  obtain ⟨ℓ, hinj, hP⟩ := hA.exists_extension
  obtain ⟨k, z, e, hx0, hxk, -, hl, -⟩ := hA.complete ℓ hinj hP x hx y hy
  have h := conn_of_path (S := E(H)) hl (fun i => (hl i).edge_mem)
  rwa [hx0, hxk] at h

lemma Admissible.card_vertices_le (hA : Admissible H P) (hne : V(H).Nonempty) :
    V(H).ncard ≤ E(H).ncard + 1 := by
  have hc : IsComp H E(H) V(H) :=
    ⟨hne, le_rfl, fun e he x y hl _ => hl.right_mem, fun x hx y hy => hA.conn_all hx hy⟩
  have h := ncard_le_edgesIn hA.finV hA.finE hc
  have : edgesIn H E(H) V(H) = E(H) := by
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨he, x, y, hl, hl.left_mem, hl.right_mem⟩
  rwa [this] at h

/-! ### First calls -/

/-- `f` is the first edge outside `I` at the vertex `v` in the order `ℓ`. -/
def IsFirstAt (H : Graph α β) (I : Set β) (ℓ : β → ℕ) (v : α) (f : β) : Prop :=
  f ∈ E(H) ∧ f ∉ I ∧ H.Inc f v ∧ ∀ g ∈ E(H), g ∉ I → H.Inc g v → g ≠ f → ℓ f < ℓ g

lemma exists_first (hA : Admissible H P) {I : Set β} {ℓ : β → ℕ} (hinj : Set.InjOn ℓ E(H))
    {v : α} (h : ∃ f ∈ E(H), f ∉ I ∧ H.Inc f v) : ∃ f, IsFirstAt H I ℓ v f := by
  obtain ⟨f0, hf0E, hf0I, hf0v⟩ := h
  obtain ⟨f, ⟨hfE, hfI, hfv⟩, hmin⟩ := Set.exists_min_image
    {f | f ∈ E(H) ∧ f ∉ I ∧ H.Inc f v} ℓ (hA.finE.subset fun f hf => hf.1)
    ⟨f0, hf0E, hf0I, hf0v⟩
  refine ⟨f, hfE, hfI, hfv, fun g hgE hgI hgv hgf => ?_⟩
  exact lt_of_le_of_ne (hmin g ⟨hgE, hgI, hgv⟩) (fun h => hgf (hinj hfE hgE h).symm)

lemma link_of_inc_inc {f : β} {u v : α} (hu : H.Inc f u) (hv : H.Inc f v) (huv : u ≠ v) :
    H.IsLink f u v := by
  obtain ⟨w, hw⟩ := hu
  rcases hv.eq_or_eq_of_isLink hw with h | h
  · exact absurd h.symm huv
  · rwa [h]

/-- An edge outside `I` that is first at both of its ends is minimal outside `I`. -/
lemma isMinOut_of_first (hA : Admissible H P) {I : Set β} (hI : IsIdeal H P I) {ℓ : β → ℕ}
    (hP : ∀ a b, P a b → ℓ a < ℓ b) {a b : α} {g : β}
    (hl : H.IsLink g a b) (ha : IsFirstAt H I ℓ a g) (hb : IsFirstAt H I ℓ b g) :
    IsMinOut H P I g := by
  refine ⟨ha.1, ha.2.1, fun h hh => ?_⟩
  by_contra hhI
  obtain ⟨g', hg'g, hg'I, hcov⟩ := hA.exists_cover_below hI ⟨h, hh, hhI⟩
  obtain ⟨y, hy1, hy2⟩ := hA.cover_adj hg'g hcov
  have hg'E := hA.mem_left hg'g
  have hne : g' ≠ g := fun h => hA.irrefl g (h ▸ hg'g)
  have hlt := hP _ _ hg'g
  rcases hy2.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (ha.2.2.2 g' hg'E hg'I hy1 hne) (not_lt.2 hlt.le)
  · exact absurd (hb.2.2.2 g' hg'E hg'I hy1 hne) (not_lt.2 hlt.le)

end Lax630294Proofs.CallOrder
