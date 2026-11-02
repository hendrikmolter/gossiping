import Lax630294Proofs.MSufficiencyDichotomy
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.VecNotation

/-!
# The four-interval structure of an `M`-witness (`lem:four-intervals`)

Encoding.  The cycle `C` of the witness is presented as `c : Cyc G n` (vertices `c.v : ZMod n → α`,
edges `c.e : ZMod n → β`, `c.e i` joins `c.v i` and `c.v (i+1)`, `range c.e = C`).  The four
essential edges `b₁,…,b₄` of the paper are `c.e (k 0), …, c.e (k 3)` for natural numbers
`k 0 < k 1 < k 2 < k 3 < n`.  The interval `X j` (`j : Fin 4`, 0-based, `X 0` is `X₁`, …) is the
set of vertices `c.v m` at positions `m < n` with `k (j-1) < m ≤ k j`; the first interval wraps
around: `X 0` consists of the positions `m ≤ k 0` and `m > k 3`.  Thus `b_j = c.e (k j)` joins
`X j` to `X (j+1)` (indices in `Fin 4`, i.e. modulo four).
-/

namespace Lax630294Proofs.FourIntervals

open Graph Lax630294.SpanningStructures Lax630294.MGraph Lax630294.TGraph
  Lax630294Proofs.MSufficiencyCyc Lax630294Proofs.MSufficiencyDichotomy

variable {α β : Type*} {G : Graph α β}

/-- Position `m` lies in the `j`-th interval determined by the cut positions `k`. -/
def InIv (k : Fin 4 → ℕ) (j : Fin 4) (m : ℕ) : Prop :=
  ![(m ≤ k 0 ∨ k 3 < m), (k 0 < m ∧ m ≤ k 1), (k 1 < m ∧ m ≤ k 2), (k 2 < m ∧ m ≤ k 3)] j

/-- The `j`-th interval `X_j` of vertices of the cycle. -/
def X {n : ℕ} (c : Cyc G n) (k : Fin 4 → ℕ) (j : Fin 4) : Set α :=
  {x | ∃ m : ℕ, m < n ∧ InIv k j m ∧ c.v (m : ZMod n) = x}

/-- The vertices (of `G`) of the component `K` of the forest `F`. -/
def compVerts (G : Graph α β) (F : Set β) (K : (underlying G F).ConnectedComponent) : Set α :=
  {x | ∃ hx : x ∈ V(G), (underlying G F).connectedComponentMk ⟨x, hx⟩ = K}

/-- `B` is a matching: distinct edges of `B` share no end. -/
def IsMatching (G : Graph α β) (B : Set β) : Prop :=
  ∀ f ∈ B, ∀ g ∈ B, f ≠ g → ∀ x, G.Inc f x → ¬ G.Inc g x

/-- Not a cut position. -/
def NC (k : Fin 4 → ℕ) (q : ℕ) : Prop := q ≠ k 0 ∧ q ≠ k 1 ∧ q ≠ k 2 ∧ q ≠ k 3

lemma kfacts {k : Fin 4 → ℕ} (hk : StrictMono k) : k 0 < k 1 ∧ k 1 < k 2 ∧ k 2 < k 3 :=
  ⟨hk (by decide), hk (by decide), hk (by decide)⟩

lemma k_lt {n : ℕ} {k : Fin 4 → ℕ} (hk : StrictMono k) (hk3 : k 3 < n) (t : Fin 4) : k t < n := by
  have : t ≤ 3 := by revert t; decide
  exact lt_of_le_of_lt (hk.monotone this) hk3

lemma exists_iv {k : Fin 4 → ℕ} (m : ℕ) : ∃ j, InIv k j m := by
  by_cases h0 : m ≤ k 0 ∨ k 3 < m
  · exact ⟨0, h0⟩
  by_cases h1 : m ≤ k 1
  · exact ⟨1, by simp only [InIv]; push Not at h0; simp; omega⟩
  by_cases h2 : m ≤ k 2
  · exact ⟨2, by simp only [InIv]; push Not at h0 h1; simp; omega⟩
  · exact ⟨3, by simp only [InIv]; push Not at h0 h1 h2; simp; omega⟩

lemma iv_unique {k : Fin 4 → ℕ} (hk : StrictMono k) {i j : Fin 4} {m : ℕ}
    (hi : InIv k i m) (hj : InIv k j m) : i = j := by
  obtain ⟨h01, h12, h23⟩ := kfacts hk
  fin_cases i <;> fin_cases j <;> simp [InIv] at hi hj ⊢ <;> omega

/-- Sorting four cut residues. -/
lemma sort_cuts {n : ℕ} [NeZero n] (W : Finset (ZMod n)) (hW : W.card = 4) :
    ∃ k : Fin 4 → ℕ, StrictMono k ∧ k 3 < n ∧
      ∀ q, q < n → (((q : ℕ) : ZMod n) ∈ W ↔ ∃ j, q = k j) := by
  classical
  let Wn : Finset ℕ := W.image ZMod.val
  have hcard : Wn.card = 4 := by
    rw [Finset.card_image_of_injective _ (ZMod.val_injective n)]; exact hW
  refine ⟨Wn.orderEmbOfFin hcard, (Wn.orderEmbOfFin hcard).strictMono, ?_, ?_⟩
  · have := Finset.orderEmbOfFin_mem Wn hcard 3
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 this
    rw [← hw]; exact ZMod.val_lt _
  · intro q hq
    constructor
    · intro h
      have : q ∈ Wn := Finset.mem_image.2 ⟨_, h, ZMod.val_natCast_of_lt hq⟩
      have : q ∈ Set.range (Wn.orderEmbOfFin hcard) := by
        rw [Finset.range_orderEmbOfFin]; exact this
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      have := Finset.orderEmbOfFin_mem Wn hcard j
      obtain ⟨w, hw, hwj⟩ := Finset.mem_image.1 this
      rw [← hwj, ZMod.natCast_zmod_val]; exact hw

section Chain

variable {n : ℕ} (c : Cyc G n) (k : Fin 4 → ℕ) (F : Set β)

/-- Reachability along runs of non-cut positions. -/
lemma chain (hr : ∀ q, q < n → NC k q →
      (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1))) :
    ∀ d a, a + d ≤ n → (∀ q, a ≤ q → q < a + d → NC k q) →
      (underlying G F).Reachable (c.vv (a : ZMod n)) (c.vv ((a + d : ℕ) : ZMod n)) := by
  intro d
  induction d with
  | zero => intro a _ _; exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    intro a had hnc
    have h1 := ih a (by omega) (fun q h1 h2 => hnc q h1 (by omega))
    have h2 := hr (a + d) (by omega) (hnc (a + d) (by omega) (by omega))
    have h3 : (((a + (d + 1) : ℕ)) : ZMod n) = ((a + d : ℕ) : ZMod n) + 1 := by push_cast; ring
    rw [h3]
    exact h1.trans h2

/-- Base position of the `j`-th interval. -/
def base (j : Fin 4) : ℕ := ![0, k 0 + 1, k 1 + 1, k 2 + 1] j

lemma reach_base (hk : StrictMono k) (hk3 : k 3 < n)
    (hr : ∀ q, q < n → NC k q →
      (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1)))
    (j : Fin 4) (m : ℕ) (hm : m < n) (hj : InIv k j m) :
    (underlying G F).Reachable (c.vv ((base k j : ℕ) : ZMod n)) (c.vv (m : ZMod n)) := by
  obtain ⟨h01, h12, h23⟩ := kfacts hk
  have key : ∀ a, a ≤ m → (∀ q, a ≤ q → q < m → NC k q) →
      (underlying G F).Reachable (c.vv (a : ZMod n)) (c.vv (m : ZMod n)) := by
    intro a ham hnc
    have := chain c k F hr (m - a) a (by omega) (fun q h1 h2 => hnc q h1 (by omega))
    rwa [show a + (m - a) = m by omega] at this
  fin_cases j
  · simp only [InIv, base] at hj ⊢
    simp at hj
    rcases hj with hj | hj
    · exact key 0 (by omega) (fun q _ hq => by unfold NC; omega)
    · have e1 := key (k 3 + 1) (by omega) (fun q h1 hq => by unfold NC; omega)
      have e2 := chain c k F hr (n - (k 3 + 1)) (k 3 + 1) (by omega)
        (fun q h1 hq => by unfold NC; omega)
      rw [show k 3 + 1 + (n - (k 3 + 1)) = n by omega, ZMod.natCast_self] at e2
      have e4 := e2.symm.trans e1
      show (underlying G F).Reachable (c.vv ((0 : ℕ) : ZMod n)) _
      rw [Nat.cast_zero]
      exact e4
  · simp only [InIv, base] at hj ⊢
    simp at hj
    exact key (k 0 + 1) (by omega) (fun q h1 hq => by unfold NC; omega)
  · simp only [InIv, base] at hj ⊢
    simp at hj
    exact key (k 1 + 1) (by omega) (fun q h1 hq => by unfold NC; omega)
  · simp only [InIv, base] at hj ⊢
    simp at hj
    exact key (k 2 + 1) (by omega) (fun q h1 hq => by unfold NC; omega)

end Chain

section Facts

variable {n : ℕ} (c : Cyc G n) (k : Fin 4 → ℕ)

lemma pos_mem (hk : StrictMono k) (hk3 : k 3 < n) (t : Fin 4) :
    c.v ((k t : ℕ) : ZMod n) ∈ X c k t := by
  obtain ⟨h01, h12, h23⟩ := kfacts hk
  refine ⟨k t, k_lt hk hk3 t, ?_, rfl⟩
  fin_cases t <;> simp [InIv] <;> omega

lemma pos_succ_mem (hk : StrictMono k) (hk3 : k 3 < n) (t : Fin 4) :
    c.v (((k t : ℕ) : ZMod n) + 1) ∈ X c k (t + 1) := by
  obtain ⟨h01, h12, h23⟩ := kfacts hk
  have hlt := k_lt hk hk3 t
  by_cases hl : k t + 1 < n
  · refine ⟨k t + 1, hl, ?_, by push_cast; rfl⟩
    fin_cases t <;> simp [InIv] <;> omega
  · have hne : k t + 1 = n := by omega
    have h0 : ((k t : ℕ) : ZMod n) + 1 = 0 := by
      have : ((k t + 1 : ℕ) : ZMod n) = 0 := by rw [hne, ZMod.natCast_self]
      push_cast at this
      exact this
    have : NeZero n := ⟨by omega⟩
    refine ⟨0, NeZero.pos n, ?_, by rw [h0]; simp⟩
    have ht3 : t ≤ 3 := Fin.le_last t
    rcases lt_or_eq_of_le ht3 with h3 | rfl
    · have := hk h3
      omega
    · simp [InIv]

lemma X_disj (hk : StrictMono k) (hk3 : k 3 < n) {i j : Fin 4} {x : α}
    (hi : x ∈ X c k i) (hj : x ∈ X c k j) : i = j := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm, hmi, rfl⟩ := hi
  obtain ⟨m', hm', hmj, h⟩ := hj
  have := c.vinj h
  have h2 : m' = m := by
    rw [← ZMod.val_natCast_of_lt hm, ← ZMod.val_natCast_of_lt hm', this]
  subst h2
  exact iv_unique hk hmi hmj

lemma X_sub {C : Set β} (hrange : Set.range c.e = C) (j : Fin 4) :
    X c k j ⊆ incidentVertices G C := by
  rintro x ⟨m, hm, -, rfl⟩
  exact ⟨c.e (m : ZMod n), hrange ▸ ⟨_, rfl⟩, ⟨c.v ((m : ZMod n) + 1), c.link _⟩⟩

lemma exists_X {C : Set β} (hrange : Set.range c.e = C) {x : α}
    (hx : x ∈ incidentVertices G C) : ∃ j, x ∈ X c k j := by
  have : NeZero n := ⟨by have := c.four; omega⟩
  obtain ⟨f', hfC, hinc⟩ := hx
  rw [← hrange] at hfC
  obtain ⟨m, rfl⟩ := hfC
  obtain ⟨y, hy⟩ := hinc
  have : ∃ i : ZMod n, x = c.v i := by
    rcases (c.link m).isLink_iff.1 hy with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ⟨m, h1.symm⟩
    · exact ⟨m + 1, h2.symm⟩
  obtain ⟨i, rfl⟩ := this
  obtain ⟨j, hj⟩ := exists_iv (k := k) i.val
  exact ⟨j, i.val, ZMod.val_lt _, hj, by rw [ZMod.natCast_zmod_val]⟩

/-- Structure of the components of a forest `F` meeting the cycle, given that the cycle edges
outside the cuts join connected vertices. -/
lemma comp_structure {C F : Set β} (hk : StrictMono k) (hk3 : k 3 < n)
    (hrange : Set.range c.e = C) (hF : IsFourComponentForestMeeting G C F)
    (hr : ∀ q, q < n → NC k q →
      (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1))) :
    ∃ φ : Fin 4 → (underlying G F).ConnectedComponent, Function.Injective φ ∧
      (∀ j m, m < n → InIv k j m →
        (underlying G F).connectedComponentMk (c.vv (m : ZMod n)) = φ j) ∧
      ∀ K, ∃ j, K = φ j := by
  have hphi : ∀ j m, m < n → InIv k j m →
      (underlying G F).connectedComponentMk (c.vv (m : ZMod n)) =
        (underlying G F).connectedComponentMk (c.vv ((base k j : ℕ) : ZMod n)) :=
    fun j m hm hj => (SimpleGraph.ConnectedComponent.sound (reach_base c k F hk hk3 hr j m hm hj)).symm
  refine ⟨fun j => (underlying G F).connectedComponentMk (c.vv ((base k j : ℕ) : ZMod n)),
    ?_, hphi, ?_⟩
  swap
  · intro K
    induction K using SimpleGraph.ConnectedComponent.ind with | h y =>
    obtain ⟨c', hc', hr'⟩ := hF.2 y
    obtain ⟨j, hj⟩ := exists_X c k hrange hc'
    obtain ⟨m, hm, hmj, hmc⟩ := hj
    refine ⟨j, ?_⟩
    have e1 : (underlying G F).connectedComponentMk y = (underlying G F).connectedComponentMk c' :=
      SimpleGraph.ConnectedComponent.sound hr'
    have e2 : c.vv (m : ZMod n) = c' := Subtype.ext hmc
    rw [e1, ← e2]
    exact hphi j m hm hmj
  · have hfin : Finite (underlying G F).ConnectedComponent := by
      by_contra hinf
      rw [not_finite_iff_infinite] at hinf
      have := hF.1.2.2.2
      rw [ENat.card_eq_top_of_infinite] at this
      exact absurd this (by simp)
    have h4 : Nat.card (underlying G F).ConnectedComponent = 4 := by
      have := hF.1.2.2.2
      rw [ENat.card_eq_coe_natCard] at this
      exact_mod_cast this
    have hsurj : Function.Surjective
        (fun j : Fin 4 => (underlying G F).connectedComponentMk (c.vv ((base k j : ℕ) : ZMod n))) := by
      intro K
      induction K using SimpleGraph.ConnectedComponent.ind with | h y =>
      obtain ⟨c', hc', hr'⟩ := hF.2 y
      obtain ⟨j, hj⟩ := exists_X c k hrange hc'
      obtain ⟨m, hm, hmj, hmc⟩ := hj
      refine ⟨j, ?_⟩
      have e1 : (underlying G F).connectedComponentMk y =
          (underlying G F).connectedComponentMk c' := SimpleGraph.ConnectedComponent.sound hr'
      have e2 : c.vv (m : ZMod n) = c' := Subtype.ext hmc
      rw [e1, ← e2]
      exact (hphi j m hm hmj).symm
    exact hsurj.injective_of_finite (Finite.equivFinOfCardEq h4).symm

end Facts

section Main

variable {n : ℕ} (c : Cyc G n) (k : Fin 4 → ℕ)

lemma nc_iff (q : ℕ) : NC k q ↔ ∀ j, q ≠ k j := by
  unfold NC
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

/-- Components of the forest meet `V(C)` exactly in the intervals. -/
lemma comp_inter {C F : Set β} (hk : StrictMono k) (hk3 : k 3 < n)
    (hrange : Set.range c.e = C) (hF : IsFourComponentForestMeeting G C F)
    (hr : ∀ q, q < n → NC k q →
      (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1))) :
    (∀ K, ∃ j, compVerts G F K ∩ incidentVertices G C = X c k j) ∧
      ∀ j, ∃ K, compVerts G F K ∩ incidentVertices G C = X c k j := by
  obtain ⟨φ, hinj, hφ, hsurj⟩ := comp_structure c k hk hk3 hrange hF hr
  have core : ∀ j, compVerts G F (φ j) ∩ incidentVertices G C = X c k j := by
    intro j
    ext x
    constructor
    · rintro ⟨⟨hx, hmk⟩, hxC⟩
      obtain ⟨j', m, hm, hmj, hmc⟩ := exists_X c k hrange hxC
      have e2 : c.vv (m : ZMod n) = ⟨x, hx⟩ := Subtype.ext hmc
      have := hφ j' m hm hmj
      rw [e2, hmk] at this
      have := hinj this
      subst this
      exact ⟨m, hm, hmj, hmc⟩
    · rintro hx
      obtain ⟨m, hm, hmj, rfl⟩ := hx
      exact ⟨⟨(c.link _).left_mem, hφ j m hm hmj⟩, X_sub c k hrange j ⟨m, hm, hmj, rfl⟩⟩
  exact ⟨fun K => by obtain ⟨j, rfl⟩ := hsurj K; exact ⟨j, core j⟩, fun j => ⟨φ j, core j⟩⟩

lemma iv_step (hk : StrictMono k) (hk3 : k 3 < n) {q : ℕ} {j : Fin 4} (hq : q < n)
    (hnc : NC k q) (hj : InIv k j q) :
    (q + 1 < n ∧ InIv k j (q + 1)) ∨ (q + 1 = n ∧ InIv k j 0) := by
  obtain ⟨h01, h12, h23⟩ := kfacts hk
  obtain ⟨n0, n1, n2, n3⟩ := hnc
  by_cases h : q + 1 < n
  · left
    refine ⟨h, ?_⟩
    fin_cases j <;> simp [InIv] at hj ⊢ <;> omega
  · right
    refine ⟨by omega, ?_⟩
    fin_cases j <;> simp [InIv] at hj ⊢ <;> omega

/-- The cut edges are recovered from the interval description. -/
lemma reach_of_comp {C F : Set β} (hk : StrictMono k) (hk3 : k 3 < n)
    (hrange : Set.range c.e = C)
    (hcomp : ∀ K, ∃ j, compVerts G F K ∩ incidentVertices G C = X c k j)
    {q : ℕ} (hq : q < n) (hnc : NC k q) :
    (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1)) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨j, hj⟩ := hcomp ((underlying G F).connectedComponentMk (c.vv (q : ZMod n)))
  have hv : c.v (q : ZMod n) ∈ incidentVertices G C :=
    ⟨c.e (q : ZMod n), hrange ▸ ⟨_, rfl⟩, ⟨_, c.link _⟩⟩
  have hv1 : c.v (q : ZMod n) ∈ compVerts G F
      ((underlying G F).connectedComponentMk (c.vv (q : ZMod n))) :=
    ⟨(c.link _).left_mem, rfl⟩
  have hX : c.v (q : ZMod n) ∈ X c k j := hj ▸ ⟨hv1, hv⟩
  obtain ⟨m, hm, hmj, hmc⟩ := hX
  have hmq : m = q := by
    have := c.vinj hmc
    rw [← ZMod.val_natCast_of_lt hm, ← ZMod.val_natCast_of_lt hq, this]
  subst hmq
  have hX1 : c.v ((m : ZMod n) + 1) ∈ X c k j := by
    rcases iv_step k hk hk3 hm hnc hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨m + 1, h1, h2, by push_cast; rfl⟩
    · refine ⟨0, NeZero.pos n, h2, ?_⟩
      have : ((m + 1 : ℕ) : ZMod n) = 0 := by rw [h1, ZMod.natCast_self]
      push_cast at this
      rw [this]; simp
  rw [← hj] at hX1
  obtain ⟨⟨hx, hmk⟩, -⟩ := hX1
  exact SimpleGraph.ConnectedComponent.exact hmk.symm

lemma cut_card (hk : StrictMono k) (hk3 : k 3 < n) [NeZero n] :
    (Finset.univ.image (fun j : Fin 4 => ((k j : ℕ) : ZMod n))).card = 4 := by
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  have h' := congrArg ZMod.val (show ((k i : ℕ) : ZMod n) = ((k j : ℕ) : ZMod n) from h)
  rw [ZMod.val_natCast_of_lt (k_lt hk hk3 i), ZMod.val_natCast_of_lt (k_lt hk hk3 j)] at h'
  exact hk.injective h'

/-- From the interval description of `F`: all cycle edges other than the four essential edges
join vertices connected in `F`. -/
theorem reach_of_four_intervals [NeZero n] {C F : Set β} (hk : StrictMono k) (hk3 : k 3 < n)
    (hrange : Set.range c.e = C)
    (hcomp : ∀ K, ∃ j, compVerts G F K ∩ incidentVertices G C = X c k j) :
    ∀ i : ZMod n, i ∉ Finset.univ.image (fun j : Fin 4 => ((k j : ℕ) : ZMod n)) →
      (underlying G F).Reachable (c.vv i) (c.vv (i + 1)) := by
  intro i hi
  have h := reach_of_comp c k hk hk3 hrange hcomp (q := i.val) (ZMod.val_lt _) (by
    rw [nc_iff]
    intro j hj
    apply hi
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by rw [← hj, ZMod.natCast_zmod_val]⟩)
  rwa [ZMod.natCast_zmod_val] at h

end Main

section Matchings

variable {n : ℕ} (c : Cyc G n) (k : Fin 4 → ℕ)

/-- The matching `{b_s, b_{s+2}}` (0-based). -/
def Bset (s : Fin 4) : Set β := {c.e ((k s : ℕ) : ZMod n), c.e ((k (s + 2) : ℕ) : ZMod n)}

lemma inc_cut (t : Fin 4) (x : α) :
    G.Inc (c.e ((k t : ℕ) : ZMod n)) x ↔
      x = c.v ((k t : ℕ) : ZMod n) ∨ x = c.v (((k t : ℕ) : ZMod n) + 1) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases (c.link _).isLink_iff.1 hy with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  · rintro (rfl | rfl)
    · exact ⟨_, c.link _⟩
    · exact ⟨_, (c.link _).symm⟩

lemma not_inc_both (hk : StrictMono k) (hk3 : k 3 < n) (t : Fin 4) (x : α)
    (h1 : G.Inc (c.e ((k t : ℕ) : ZMod n)) x) (h2 : G.Inc (c.e ((k (t + 2) : ℕ) : ZMod n)) x) :
    False := by
  have hd : ∀ t : Fin 4, t ≠ t + 2 ∧ t ≠ t + 2 + 1 ∧ t + 1 ≠ t + 2 ∧ t + 1 ≠ t + 2 + 1 := by
    decide
  obtain ⟨d1, d2, d3, d4⟩ := hd t
  rw [inc_cut] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · exact d1 (X_disj c k hk hk3 (pos_mem c k hk hk3 t) (h2 ▸ pos_mem c k hk hk3 (t + 2)))
  · exact d2 (X_disj c k hk hk3 (pos_mem c k hk hk3 t) (h2 ▸ pos_succ_mem c k hk hk3 (t + 2)))
  · exact d3 (X_disj c k hk hk3 (pos_succ_mem c k hk hk3 t) (h2 ▸ pos_mem c k hk hk3 (t + 2)))
  · exact d4 (X_disj c k hk hk3 (pos_succ_mem c k hk hk3 t)
      (h2 ▸ pos_succ_mem c k hk hk3 (t + 2)))

lemma bset_matching (hk : StrictMono k) (hk3 : k 3 < n) (s : Fin 4) :
    IsMatching G (Bset c k s) := by
  have hss : s + 2 + 2 = s := by revert s; decide
  intro f hf g hg hfg x hfx hgx
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact hfg rfl
  · exact not_inc_both c k hk hk3 s x hfx hgx
  · refine not_inc_both c k hk hk3 (s + 2) x hfx ?_
    rw [hss]; exact hgx
  · exact hfg rfl

lemma bset_sub {C : Set β} (hrange : Set.range c.e = C) (s : Fin 4) : Bset c k s ⊆ C := by
  rintro f (rfl | rfl)
  · exact hrange ▸ ⟨_, rfl⟩
  · exact hrange ▸ ⟨_, rfl⟩

lemma unique_vertex (hk : StrictMono k) (hk3 : k 3 < n) (s j : Fin 4) :
    ∃! x, x ∈ X c k j ∧ x ∈ incidentVertices G (Bset c k s) := by
  let P : Fin 4 → α := ![c.v ((k s : ℕ) : ZMod n), c.v (((k s : ℕ) : ZMod n) + 1),
    c.v ((k (s + 2) : ℕ) : ZMod n), c.v (((k (s + 2) : ℕ) : ZMod n) + 1)]
  have hP : ∀ r, P r ∈ X c k (s + r) := by
    intro r
    fin_cases r
    · simpa [P] using pos_mem c k hk hk3 s
    · simpa [P] using pos_succ_mem c k hk hk3 s
    · simpa [P] using pos_mem c k hk hk3 (s + 2)
    · have := pos_succ_mem c k hk hk3 (s + 2)
      have e : ∀ s : Fin 4, s + 2 + 1 = s + 3 := by decide
      rw [e s] at this
      simpa [P] using this
  have hV : ∀ x, x ∈ incidentVertices G (Bset c k s) ↔ ∃ r, x = P r := by
    intro x
    constructor
    · rintro ⟨f, rfl | rfl, hinc⟩
      · rcases (inc_cut c k s x).1 hinc with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · rcases (inc_cut c k (s + 2) x).1 hinc with h | h
        · exact ⟨2, h⟩
        · exact ⟨3, h⟩
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨_, Or.inl rfl, (inc_cut c k s _).2 (Or.inl rfl)⟩
      · exact ⟨_, Or.inl rfl, (inc_cut c k s _).2 (Or.inr rfl)⟩
      · exact ⟨_, Or.inr rfl, (inc_cut c k (s + 2) _).2 (Or.inl rfl)⟩
      · exact ⟨_, Or.inr rfl, (inc_cut c k (s + 2) _).2 (Or.inr rfl)⟩
  refine ⟨P (j - s), ⟨?_, (hV _).2 ⟨_, rfl⟩⟩, ?_⟩
  · have := hP (j - s)
    rwa [add_sub_cancel] at this
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨r, rfl⟩ := (hV _).1 hy2
    have h1 := X_disj c k hk hk3 hy1 (hP r)
    have h2 : r = j - s := by rw [h1, add_sub_cancel_left]
    rw [h2]

end Matchings

-- DEVIATION (encoding): the paper's intervals `X₁,…,X₄` are encoded by a cyclic presentation
-- `c : Cyc G n` of `C` (`range c.e = C`) and four cut positions `k 0 < k 1 < k 2 < k 3 < n`;
-- `X c k j` is the set of vertices at the positions strictly after the previous cut up to the
-- cut `k j` (the first interval wraps around).  "Component meets `V(C)` in `X_j`" is stated with
-- the connected components of the simple graph underlying `F_j`.  Indices are 0-based, so the
-- paper's `b₁,b₃` / `b₂,b₄` are `c.e (k 0), c.e (k 2)` / `c.e (k 1), c.e (k 3)`.
-- DEVIATION (proof): as in the paper the statement is derived from the cross-bases dichotomy
-- (`MSufficiencyDichotomy.dichotomy`), whose matroid-free form uses the rank-three lemma for
-- 3-sets rather than for matroids.  The four arcs of `C - W` lie in distinct components because
-- the forest has exactly four components, each meeting `C` (a counting argument as in the paper).
-- The hypothesis `E(G).Finite` is not needed.
/-- **Lemma `lem:four-intervals`.** For an `M`-witness `(C,F₁,F₂)` of a graph that is not a
`T`-graph there is a presentation of `C` and cut positions such that: the `X j` partition `V(C)`
into four nonempty consecutive intervals, `b_j = c.e (k j)` joins `X j` to `X (j+1)`, the
components of each `F_i` meet `V(C)` exactly in the `X j`, `B₁ = {b₀,b₂}` and `B₂ = {b₁,b₃}` are
edge-disjoint matchings, and every component of each forest contains exactly one vertex of
`V(B₁)` and exactly one of `V(B₂)`. -/
theorem four_intervals {α β : Type*} {G : Graph α β} (hV : V(G).Finite) {C F₁ F₂ : Set β}
    (hW : IsMWitness G C F₁ F₂) (hnT : ¬ IsTGraph G) :
    ∃ (n : ℕ) (_ : NeZero n) (c : Cyc G n) (k : Fin 4 → ℕ),
      Set.range c.e = C ∧ StrictMono k ∧ k 3 < n ∧
      -- `X 0, …, X 3` partition `V(C)` into nonempty intervals
      (∀ j, (X c k j).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (X c k i) (X c k j)) ∧
      (⋃ j, X c k j) = incidentVertices G C ∧
      -- `b_j` joins `X j` to `X (j+1)`
      (∀ j : Fin 4, G.IsLink (c.e (k j)) (c.v (k j)) (c.v ((k j : ZMod n) + 1)) ∧
        c.v (k j) ∈ X c k j ∧ c.v ((k j : ZMod n) + 1) ∈ X c k (j + 1)) ∧
      -- common intervals
      (∀ F ∈ ({F₁, F₂} : Set (Set β)),
        (∀ K, ∃ j, compVerts G F K ∩ incidentVertices G C = X c k j) ∧
        ∀ j, ∃ K, compVerts G F K ∩ incidentVertices G C = X c k j) ∧
      -- alternating matchings
      Disjoint ({c.e (k 0), c.e (k 2)} : Set β) {c.e (k 1), c.e (k 3)} ∧
      IsMatching G ({c.e (k 0), c.e (k 2)} : Set β) ∧
      IsMatching G ({c.e (k 1), c.e (k 3)} : Set β) ∧
      (∀ F ∈ ({F₁, F₂} : Set (Set β)), ∀ K,
        (∃! x, x ∈ compVerts G F K ∧ x ∈ incidentVertices G ({c.e (k 0), c.e (k 2)} : Set β)) ∧
        (∃! x, x ∈ compVerts G F K ∧ x ∈ incidentVertices G ({c.e (k 1), c.e (k 3)} : Set β))) := by
  obtain ⟨n, hn, c, W, hrange, hWc, hreach⟩ := dichotomy hV hW hnT
  obtain ⟨-, -, hF1, hF2, -, -, -⟩ := hW
  obtain ⟨k, hk, hk3, hkW⟩ := sort_cuts W hWc
  have hr : ∀ F : Set β, (∀ i, i ∉ W → (underlying G F).Reachable (c.vv i) (c.vv (i + 1))) →
      ∀ q, q < n → NC k q →
        (underlying G F).Reachable (c.vv (q : ZMod n)) (c.vv ((q : ZMod n) + 1)) := by
    intro F hF q hq hnc
    refine hF _ (fun hmem => ?_)
    obtain ⟨j, hj⟩ := (hkW q hq).1 hmem
    exact (nc_iff k q).1 hnc j hj
  have hc1 := comp_inter c k hk hk3 hrange hF1 (hr F₁ (fun i hi => (hreach i hi).1))
  have hc2 := comp_inter c k hk hk3 hrange hF2 (hr F₂ (fun i hi => (hreach i hi).2))
  have hcomp : ∀ F ∈ ({F₁, F₂} : Set (Set β)),
      (∀ K, ∃ j, compVerts G F K ∩ incidentVertices G C = X c k j) ∧
        ∀ j, ∃ K, compVerts G F K ∩ incidentVertices G C = X c k j := by
    intro F hF
    rcases hF with rfl | rfl
    · exact hc1
    · exact hc2
  have hB1 : ({c.e (k 0), c.e (k 2)} : Set β) = Bset c k 0 := rfl
  have hB2 : ({c.e (k 1), c.e (k 3)} : Set β) = Bset c k 1 := rfl
  refine ⟨n, hn, c, k, hrange, hk, hk3, ?_, ?_, ?_, ?_, hcomp, ?_, ?_, ?_, ?_⟩
  · exact fun j => ⟨_, pos_mem c k hk hk3 j⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    exact hij (X_disj c k hk hk3 hi hj)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun j => X_sub c k hrange j)
    · intro x hx
      obtain ⟨j, hj⟩ := exists_X c k hrange hx
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  · exact fun j => ⟨c.link _, pos_mem c k hk hk3 j, pos_succ_mem c k hk hk3 j⟩
  · rw [Set.disjoint_left]
    have hinj : ∀ i j : Fin 4, c.e ((k i : ℕ) : ZMod n) = c.e ((k j : ℕ) : ZMod n) → i = j := by
      intro i j h
      have h' := congrArg ZMod.val (c.einj h)
      rw [ZMod.val_natCast_of_lt (k_lt hk hk3 i), ZMod.val_natCast_of_lt (k_lt hk hk3 j)] at h'
      exact hk.injective h'
    rintro f (rfl | rfl) (h | h)
    · exact absurd (hinj _ _ h) (by decide)
    · exact absurd (hinj _ _ h) (by decide)
    · exact absurd (hinj _ _ h) (by decide)
    · exact absurd (hinj _ _ h) (by decide)
  · rw [hB1]; exact bset_matching c k hk hk3 0
  · rw [hB2]; exact bset_matching c k hk hk3 1
  · intro F hF K
    obtain ⟨j, hj⟩ := (hcomp F hF).1 K
    have key : ∀ s : Fin 4, ∃! x, x ∈ compVerts G F K ∧ x ∈ incidentVertices G (Bset c k s) := by
      intro s
      obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := unique_vertex c k hk hk3 s j
      have hsub : incidentVertices G (Bset c k s) ⊆ incidentVertices G C := by
        rintro y ⟨f, hf, hy⟩
        exact ⟨f, bset_sub c k hrange s hf, hy⟩
      refine ⟨x, ⟨?_, hx2⟩, ?_⟩
      · have : x ∈ compVerts G F K ∩ incidentVertices G C := hj ▸ hx1
        exact this.1
      · rintro y ⟨hy1, hy2⟩
        refine hu y ⟨?_, hy2⟩
        have : y ∈ compVerts G F K ∩ incidentVertices G C := ⟨hy1, hsub hy2⟩
        exact hj ▸ this
    exact ⟨key 0, key 1⟩

end Lax630294Proofs.FourIntervals
