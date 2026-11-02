import Lax630294.SpanningStructures
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# Cycle data and the simple graph underlying an edge set
-/

namespace Lax630294Proofs.MSufficiencyCyc

open Graph Lax630294.SpanningStructures

variable {α β : Type*}

/-- Adjacency in the simple graph underlying the spanning subgraph with edge set `T`. -/
lemma underlying_adj {G : Graph α β} {T : Set β} {x y : V(G)} :
    (underlying G T).Adj x y ↔ x ≠ y ∧ ∃ f ∈ T, G.IsLink f x.1 y.1 := Iff.rfl

lemma underlying_mono {G : Graph α β} {T T' : Set β} (h : T ⊆ T') :
    underlying G T ≤ underlying G T' := by
  intro x y hxy
  rw [underlying_adj] at hxy ⊢
  obtain ⟨hne, f, hf, hl⟩ := hxy
  exact ⟨hne, f, h hf, hl⟩

lemma adj_of_isLink {G : Graph α β} {T : Set β} {f : β} {x y : α} (hf : f ∈ T)
    (h : G.IsLink f x y) (hne : x ≠ y) :
    (underlying G T).Adj ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
  underlying_adj.2 ⟨fun h' => hne (congrArg Subtype.val h'), f, hf, h⟩

/-- A cycle of length `n ≥ 4` in `G`, given by an explicit cyclic sequence. -/
structure Cyc (G : Graph α β) (n : ℕ) where
  v : ZMod n → α
  e : ZMod n → β
  four : 4 ≤ n
  vinj : Function.Injective v
  einj : Function.Injective e
  link : ∀ i, G.IsLink (e i) (v i) (v (i + 1))

namespace Cyc

variable {G : Graph α β} {n : ℕ} (c : Cyc G n)

include c

lemma two_ne_zero : (2 : ZMod n) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by omega) h'
  have := c.four
  omega

lemma one_ne_zero : (1 : ZMod n) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by omega) h'
  have := c.four
  omega

lemma succ_ne (i : ZMod n) : i + 1 ≠ i := by
  intro h
  exact c.one_ne_zero (by simpa using h)

lemma v_succ_ne (i : ZMod n) : c.v (i + 1) ≠ c.v i :=
  fun h => c.succ_ne i (c.vinj h)

lemma succ_succ_ne (k : ZMod n) : k + 1 + 1 ≠ k := by
  intro h
  apply c.two_ne_zero
  have h3 : k + 2 = k + 0 := by
    rw [add_zero]
    calc k + 2 = k + 1 + 1 := by ring
      _ = k := h
  exact add_left_cancel h3

lemma not_loop (i : ZMod n) (x : α) : ¬ G.IsLink (c.e i) x x := by
  intro h
  rcases (c.link i).isLink_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact c.v_succ_ne i (h2.trans h1.symm)

lemma edge_mem (i : ZMod n) : c.e i ∈ E(G) := (c.link i).edge_mem

/-- Two cycle edges with the same ends are equal. -/
lemma index_unique {i k : ZMod n} {x y : α} (hi : G.IsLink (c.e i) x y)
    (hk : G.IsLink (c.e k) x y) : i = k := by
  have hx : (c.v i = x ∧ c.v (i + 1) = y) ∨ (c.v i = y ∧ c.v (i + 1) = x) :=
    (c.link i).isLink_iff.1 hi
  have hx' : (c.v k = x ∧ c.v (k + 1) = y) ∨ (c.v k = y ∧ c.v (k + 1) = x) :=
    (c.link k).isLink_iff.1 hk
  rcases hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hx' with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact c.vinj (a1.trans b1.symm)
  · have e1 : i = k + 1 := c.vinj (a1.trans b2.symm)
    have e2 : i + 1 = k := c.vinj (a2.trans b1.symm)
    exfalso
    apply c.succ_succ_ne k
    rw [← e1]; exact e2
  · have e1 : i = k + 1 := c.vinj (a1.trans b2.symm)
    have e2 : i + 1 = k := c.vinj (a2.trans b1.symm)
    exfalso
    apply c.succ_succ_ne k
    rw [← e1]; exact e2
  · have : i + 1 = k + 1 := c.vinj (a2.trans b2.symm)
    exact add_right_cancel this

/-- The vertex `v i` as an element of `V(G)`. -/
def vv (i : ZMod n) : V(G) := ⟨c.v i, (c.link i).left_mem⟩

lemma vv_ne (i : ZMod n) : c.vv i ≠ c.vv (i + 1) :=
  fun h => c.v_succ_ne i (congrArg Subtype.val h).symm

lemma vv_inj : Function.Injective c.vv := fun _ _ h => c.vinj (congrArg Subtype.val h)

/-- The (unordered) pair of ends of the `i`-th cycle edge. -/
def pair (i : ZMod n) : Sym2 V(G) := s(c.vv i, c.vv (i + 1))

lemma pair_inj : Function.Injective c.pair := by
  intro i k h
  unfold pair at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact c.vv_inj h1
  · exfalso
    have e1 : i = k + 1 := c.vv_inj h1
    have e2 : i + 1 = k := c.vv_inj h2
    apply c.succ_succ_ne k
    rw [← e1]; exact e2

lemma link_of_pair {i : ZMod n} {a b : V(G)} (h : s(a, b) = c.pair i) :
    G.IsLink (c.e i) a.1 b.1 := by
  unfold pair at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact c.link i
  · rw [h1, h2]; exact (c.link i).symm

lemma pair_of_link {i : ZMod n} {a b : V(G)} (h : G.IsLink (c.e i) a.1 b.1) :
    s(a, b) = c.pair i := by
  unfold pair
  rcases (c.link i).isLink_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Sym2.eq_iff]; left; exact ⟨Subtype.ext h1.symm, Subtype.ext h2.symm⟩
  · rw [Sym2.eq_iff]; right; exact ⟨Subtype.ext h2.symm, Subtype.ext h1.symm⟩

end Cyc

end Lax630294Proofs.MSufficiencyCyc
