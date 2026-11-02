import Lax630294Proofs.PortsGraph

/-!
# Maximal directed paths in the arc digraph (final step of `lem:characterization-compatible-actual-cycle`)

Pure combinatorics on a graph `H` with an acyclic edge set `E0`:

* `RPath`, `exists_max_rpath`: a directed path (a nodup list of vertices of a finite set, each
  consecutive pair an arc) of maximal length exists;
* `rpath_reach`: the vertices of a directed path reach its last vertex through edges carrying
  the arcs;
* `sink_pair`: an arc relation with positive outdegree and the rerouting property has an edge
  with both orientations and different indices.  The proof is the paper's: take a maximal
  directed path, look at its last arc `U -> V`; every outgoing neighbour of `V` lies on the path,
  and a neighbour other than `U` would close a cycle in the acyclic edge set.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree

variable {γ β : Type*} {H : Graph γ β}

lemma Acyc.not_loop {E0 : Set β} (hac : Acyc H E0) {h : β} (hh : h ∈ E0) {a : γ}
    (hl : H.IsLink h a a) : False :=
  hac h hh a a hl reach_refl

lemma reach_in_set {E0 : Set β} {S0 : Set γ} (hE0 : E0 ⊆ Ins H S0) {a x : γ} (ha : a ∈ S0)
    (h : Reach H E0 a x) : x ∈ S0 := by
  induction h with
  | refl => exact ha
  | tail _ hs ih =>
    obtain ⟨c, hc, hl⟩ := hs
    exact (ins_of_link (hE0 hc) hl).2

/-- A directed path, stored reversed: the head of the list is its last vertex. -/
def RPath (arc : γ → γ → Prop) (S0 : Set γ) (l : List γ) : Prop :=
  l.Nodup ∧ (∀ x ∈ l, x ∈ S0) ∧ List.IsChain (fun a b => arc b a) l

/-- A directed path of maximal length exists (finiteness). -/
lemma exists_max_rpath {arc : γ → γ → Prop} {S0 : Set γ} (hS0 : S0.Finite) {U0 : γ}
    (hU0 : U0 ∈ S0) :
    ∃ l, RPath arc S0 l ∧ l ≠ [] ∧ ∀ l', RPath arc S0 l' → l'.length ≤ l.length := by
  classical
  let s : Set ℕ := {n | ∃ l, RPath arc S0 l ∧ l.length = n}
  have h1 : (1 : ℕ) ∈ s :=
    ⟨[U0], ⟨List.nodup_singleton _, by simpa using hU0, List.IsChain.singleton _⟩, rfl⟩
  have hb : BddAbove s := ⟨hS0.toFinset.card, by
    rintro n ⟨l, ⟨hnd, hS, -⟩, rfl⟩
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card (fun x hx => by simpa using hS x (List.mem_toFinset.1 hx))⟩
  obtain ⟨l, hl, hlen⟩ := Nat.sSup_mem ⟨1, h1⟩ hb
  refine ⟨l, hl, ?_, fun l' hl' => ?_⟩
  · rintro rfl
    have := le_csSup hb h1
    rw [← hlen] at this
    simp at this
  · rw [hlen]
    exact le_csSup hb ⟨l', hl', rfl⟩

/-- Along a directed path (stored reversed) every vertex reaches the last one through the edges
carrying the arcs. -/
lemma rpath_reach {F : Set β} {arc : γ → γ → Prop} :
    ∀ (m : List γ) (U : γ), List.IsChain (fun a b => arc b a) (U :: m) →
      (∀ a b, arc a b → a ∈ U :: m → b ∈ U :: m → ∃ c ∈ F, H.IsLink c a b) →
      ∀ x ∈ U :: m, Reach H F x U := by
  intro m
  induction m with
  | nil =>
    intro U _ _ x hx
    simp at hx
    subst hx
    exact reach_refl
  | cons b m ih =>
    intro U hch hF x hx
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hbU, hch'⟩ := hch
    obtain ⟨c, hc, hl⟩ := hF b U hbU (by simp) (by simp)
    have h1 : Reach H F b U := reach_of_isLink hc hl
    rcases List.mem_cons.1 hx with rfl | hx
    · exact reach_refl
    · exact (ih b hch' (fun a a' haa ha ha' => hF a a' haa (List.mem_cons_of_mem _ ha)
        (List.mem_cons_of_mem _ ha')) x hx).trans' h1

/-- In an acyclic edge set, an arc relation with positive outdegree and the rerouting property
contains an edge with both orientations and different indices (maximal directed path argument). -/
-- Same argument as the paper's (maximal directed path).  The path is
-- stored as a reversed list, and the acyclicity of `Y[S]` is used through the bridge property
-- `Acyc`.  (The case of a one-vertex maximal path, a loop, is excluded explicitly.)
theorem sink_pair {E0 : Set β} (hac : Acyc H E0) {S0 : Set γ} (hS0 : S0.Finite)
    (hE0 : E0 ⊆ Ins H S0) {arc : γ → γ → Prop} {idx : γ → Bool}
    (harc : ∀ a b, arc a b → a ∈ S0 ∧ ∃ c ∈ E0, H.IsLink c a b)
    (hout : ∀ U ∈ S0, ∃ V, arc U V)
    (hrer : ∀ a b, arc a b → idx a = idx b → ∃ w, w ≠ a ∧ arc b w)
    (hne : S0.Nonempty) :
    ∃ U V, arc U V ∧ arc V U ∧ idx U ≠ idx V := by
  have hbS : ∀ a b, arc a b → b ∈ S0 := fun a b hab => by
    obtain ⟨-, c, hc, hl⟩ := harc a b hab
    exact (ins_of_link (hE0 hc) hl).2
  obtain ⟨U0, hU0⟩ := hne
  obtain ⟨l, ⟨hnd, hlS, hch⟩, hlne, hmax⟩ := exists_max_rpath (arc := arc) hS0 hU0
  obtain ⟨V, l1, rfl⟩ := List.exists_cons_of_ne_nil hlne
  have hVS : V ∈ S0 := hlS V (by simp)
  -- every outgoing neighbour of `V` lies on the path
  have hon : ∀ W, arc V W → W ∈ V :: l1 := by
    intro W hW
    by_contra hWl
    have := hmax (W :: V :: l1) ⟨List.nodup_cons.2 ⟨hWl, hnd⟩, ?_,
      List.isChain_cons_cons.2 ⟨hW, hch⟩⟩
    · simp at this
    · intro x hx
      rcases List.mem_cons.1 hx with h | hx
      · rw [h]; exact hbS V W hW
      · exact hlS x hx
  cases l1 with
  | nil =>
    obtain ⟨W, hW⟩ := hout V hVS
    have := hon W hW
    simp at this
    subst this
    obtain ⟨-, c, hc, hl⟩ := harc _ _ hW
    exact (hac.not_loop hc hl).elim
  | cons U rest =>
    have hUV : arc U V := (List.isChain_cons_cons.1 hch).1
    have hVn : V ∉ U :: rest := (List.nodup_cons.1 hnd).1
    have key : ∀ W, arc V W → W = U := by
      intro W hW
      by_contra hWU
      have hWl := hon W hW
      obtain ⟨-, c, hc, hcl⟩ := harc V W hW
      have hWV : W ≠ V := by
        rintro rfl
        exact hac.not_loop hc hcl
      have hWrest : W ∈ U :: rest := by
        rcases List.mem_cons.1 hWl with h | h
        · exact absurd h hWV
        · exact h
      have hR : Reach H (E0 \ {c}) W U := by
        refine rpath_reach rest U (List.isChain_cons_cons.1 hch).2 ?_ W hWrest
        intro a b hab ha hb
        obtain ⟨-, c', hc', hl'⟩ := harc a b hab
        refine ⟨c', ⟨hc', ?_⟩, hl'⟩
        intro h
        rw [Set.mem_singleton_iff] at h
        subst h
        rcases hl'.eq_and_eq_or_eq_and_eq hcl with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hVn ha
        · exact hVn hb
      obtain ⟨-, c2, hc2, hl2⟩ := harc U V hUV
      have hc2c : c2 ≠ c := by
        rintro rfl
        rcases hl2.eq_and_eq_or_eq_and_eq hcl with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hVn (by rw [← h1]; simp)
        · exact hWU h1.symm
      have hWV' : Reach H (E0 \ {c}) W V :=
        hR.trans' (reach_of_isLink (F := E0 \ {c}) ⟨hc2, hc2c⟩ hl2)
      exact hac c hc V W hcl hWV'.symm'
    have hVU : arc V U := by
      obtain ⟨W, hW⟩ := hout V hVS
      rw [key W hW] at hW
      exact hW
    refine ⟨U, V, hUV, hVU, fun heq => ?_⟩
    obtain ⟨w, hwU, hVw⟩ := hrer U V hUV heq
    exact hwU (key w hVw)

end Lax630294Proofs.Ports
