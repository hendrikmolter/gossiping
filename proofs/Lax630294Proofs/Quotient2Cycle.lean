import Lax630294.SpanningStructures
import Lax630294Proofs.QuotientTwoTree

/-!
# Walks as lists, and the splice lemma for cycles

`Chain G a vs es b` is a walk from `a` to `b` with vertex list `vs` (the final vertex `b` is not
listed) and edge list `es`.  Concatenation of walks is `Chain.append`; a closed walk with
duplicate-free vertex and edge lists is a cycle in the sense of the frozen `IsCycle`
(`isCycle_of_chain`).  `IsPathSet G p q P`: `P` is the edge set of a (possibly trivial) path from
`p` to `q`.
-/

namespace Lax630294Proofs.Quotient2Cycle

open Graph Lax630294.SpanningStructures Lax630294Proofs.QuotientTwoTree

variable {α β : Type*} {G : Graph α β}

inductive Chain (G : Graph α β) : α → List α → List β → α → Prop
  | nil (a : α) : Chain G a [] [] a
  | cons {a b c : α} {e : β} {vs : List α} {es : List β} :
      G.IsLink e a b → Chain G b vs es c → Chain G a (a :: vs) (e :: es) c

namespace Chain

lemma append {a b c : α} {vs vs' : List α} {es es' : List β}
    (h : Chain G a vs es b) (h' : Chain G b vs' es' c) :
    Chain G a (vs ++ vs') (es ++ es') c := by
  induction h with
  | nil => simpa using h'
  | cons hl _ ih => exact Chain.cons hl (ih h')

lemma single {a b : α} {e : β} (h : G.IsLink e a b) : Chain G a [a] [e] b :=
  Chain.cons h (Chain.nil b)

lemma length_eq {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    vs.length = es.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

lemma getD_zero {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    vs.getD 0 b = a := by
  cases h <;> rfl

lemma link_at {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    ∀ (k : ℕ) (hk : k < vs.length) (hk' : k < es.length),
      G.IsLink es[k] vs[k] (vs.getD (k + 1) b) := by
  induction h with
  | nil => intro k hk; simp at hk
  | @cons a b' c e vs es hl hc ih =>
    intro k hk hk'
    cases k with
    | zero =>
      have h0 : (a :: vs).getD (0 + 1) c = b' := hc.getD_zero
      show G.IsLink e a ((a :: vs).getD (0 + 1) c)
      rw [h0]; exact hl
    | succ k =>
      have hk1 : k < vs.length := by simpa using hk
      have hk2 : k < es.length := by simpa using hk'
      simpa using ih k hk1 hk2

/-- If all edges of a walk lie inside `X` and it starts in `X`, all its vertices lie in `X`. -/
lemma mem_of_ins {a b : α} {vs : List α} {es : List β} {X : Set α}
    (h : Chain G a vs es b) (hes : ∀ e ∈ es, e ∈ Ins G X) (ha : a ∈ X) :
    (∀ v ∈ vs, v ∈ X) ∧ b ∈ X := by
  induction h with
  | nil => exact ⟨by simp, ha⟩
  | @cons a b' c e vs es hl hc ih =>
    have hb' : b' ∈ X := (ins_of_link (hes e (by simp)) hl).2
    obtain ⟨h1, h2⟩ := ih (fun f hf => hes f (by simp [hf])) hb'
    refine ⟨?_, h2⟩
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ha
    · exact h1 v hv

end Chain

/-- `P` is the edge set of a path from `p` to `q` (a trivial path when `p = q` and `P = ∅`). -/
def IsPathSet (G : Graph α β) (p q : α) (P : Set β) : Prop :=
  ∃ (vs : List α) (es : List β), Chain G p vs es q ∧ (vs ++ [q]).Nodup ∧ es.Nodup ∧
    {e | e ∈ es} = P

/-- **Splice lemma.**  A closed walk with duplicate-free vertex and edge lists is a cycle. -/
theorem isCycle_of_chain {s : α} {vs : List α} {es : List β} (h : Chain G s vs es s)
    (hv : vs.Nodup) (he : es.Nodup) (hne : es ≠ []) : IsCycle G {e | e ∈ es} := by
  have hlen := h.length_eq
  have hn : 0 < es.length := List.length_pos_iff.2 hne
  have : NeZero es.length := ⟨hn.ne'⟩
  obtain ⟨e0, _⟩ := List.exists_mem_of_ne_nil es hne
  refine ⟨es.length, hn, fun i => vs.getD i.val s, fun i => es.getD i.val e0, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hi : i.val < vs.length := by rw [hlen]; exact ZMod.val_lt i
    have hj : j.val < vs.length := by rw [hlen]; exact ZMod.val_lt j
    exact ZMod.val_injective _ ((List.getD_inj hi hj hv).1 hij)
  · intro i j hij
    exact ZMod.val_injective _ ((List.getD_inj (ZMod.val_lt i) (ZMod.val_lt j) he).1 hij)
  · intro i
    have hi : i.val < vs.length := by rw [hlen]; exact ZMod.val_lt i
    have h1 := h.link_at i.val hi (ZMod.val_lt i)
    have hval : (i + 1).val = (i.val + 1) % es.length := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have hg : vs.getD ((i.val + 1) % es.length) s = vs.getD (i.val + 1) s := by
      by_cases hlt : i.val + 1 < es.length
      · rw [Nat.mod_eq_of_lt hlt]
      · have heq : i.val + 1 = es.length := by have := ZMod.val_lt i; omega
        rw [heq, Nat.mod_self, h.getD_zero, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]
        rfl
    simp only [hval, hg]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    rw [List.getElem?_eq_getElem (ZMod.val_lt i)]
    simpa using h1
  · ext e
    constructor
    · rintro ⟨i, rfl⟩
      show es.getD i.val e0 ∈ es
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (ZMod.val_lt i)]
      exact List.getElem_mem _
    · intro hm
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
      refine ⟨(k : ZMod es.length), ?_⟩
      have : ((k : ZMod es.length)).val = k := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
      simp only [this]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl

end Lax630294Proofs.Quotient2Cycle
