import Lax630294Proofs.NecessityPrelim
import Mathlib.Data.Set.Card

namespace Lax630294Proofs.SmallCases

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore

variable {γ β : Type*}

/-- A connected graph with two vertices has an edge.
DEVIATION: the hypothesis `hE : E(H).Finite` is added (an infinite edge set has `ncard = 0`). -/
theorem two_vertices_edge {H : Graph γ β} (_hV : V(H).Finite) (hE : E(H).Finite)
    (h2 : V(H).ncard = 2)
    (hconn : ∀ x ∈ V(H), ∀ y ∈ V(H), Reach H E(H) x y) : 1 ≤ E(H).ncard := by
  obtain ⟨a, b, hab, hVab⟩ := Set.ncard_eq_two.mp h2
  have ha : a ∈ V(H) := by rw [hVab]; simp
  have hb : b ∈ V(H) := by rw [hVab]; simp
  have hr := hconn a ha b hb
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨e, he, _⟩, _⟩
  · exact absurd h hab
  · exact Nat.one_le_iff_ne_zero.mpr
      (fun h0 => by
        have := (Set.ncard_eq_zero hE).mp h0
        rw [this] at he; exact he)

lemma two_step {H : Graph γ β} {ℓ : β → ℕ} {u v w : γ} (hv : v ∈ V(H))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hsub : ∀ z ∈ V(H), z = u ∨ z = v ∨ z = w)
    (hnadj : ∀ e, ¬ H.IsLink e u v) (hp : HasTemporalPath H ℓ u v) :
    ∃ e1 e2, H.IsLink e1 u w ∧ H.IsLink e2 w v ∧ ℓ e1 < ℓ e2 := by
  obtain ⟨k, x, e, h0, hk, hinj, hl, hmono⟩ := hp
  have hmem : ∀ j, x j ∈ V(H) := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hk]; exact hv
    | cast i => exact (hl i).left_mem
  obtain _ | _ | _ | k := k
  · exact absurd (h0.symm.trans hk) huv
  · have := hl 0
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
    have h1 : x 1 = v := hk
    rw [h0, h1] at this
    exact absurd this (hnadj _)
  · have h1 : x 1 = w := by
      have hm := hsub _ (hmem 1)
      have n0 : x 1 ≠ x 0 := fun h => by
        have := hinj h; exact absurd this (by decide)
      have n2 : x 1 ≠ x (Fin.last 2) := fun h => by
        have := hinj h; exact absurd this (by decide)
      rw [h0] at n0; rw [hk] at n2
      tauto
    have l0 := hl 0
    have l1 := hl 1
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at l0
    have c1 : (Fin.castSucc (1 : Fin 2)) = (1 : Fin 3) := rfl
    have c2 : (Fin.succ (1 : Fin 2)) = Fin.last 2 := rfl
    rw [c1, c2] at l1
    rw [h0, h1] at l0
    rw [h1, hk] at l1
    exact ⟨e 0, e 1, l0, l1, hmono (by decide)⟩
  · exfalso
    have hd : ∀ i j : Fin (k + 4), i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
    have m0 := hsub _ (hmem ⟨0, by omega⟩)
    have m1 := hsub _ (hmem ⟨1, by omega⟩)
    have m2 := hsub _ (hmem ⟨2, by omega⟩)
    have m3 := hsub _ (hmem ⟨3, by omega⟩)
    have d01 := hd ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    have d02 := hd ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    have d03 := hd ⟨0, by omega⟩ ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    have d12 := hd ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    have d13 := hd ⟨1, by omega⟩ ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    have d23 := hd ⟨2, by omega⟩ ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    generalize x ⟨0, _⟩ = a0 at *
    generalize x ⟨1, _⟩ = a1 at *
    generalize x ⟨2, _⟩ = a2 at *
    generalize x ⟨3, _⟩ = a3 at *
    rcases m0 with rfl | rfl | rfl <;> rcases m1 with rfl | rfl | rfl <;>
      rcases m2 with rfl | rfl | rfl <;> rcases m3 with rfl | rfl | rfl <;> simp_all

/-- A complete simple graph on three vertices has three edges. -/
theorem three_vertices_edges {H : Graph γ β} (hS : H.Simple) (_hV : V(H).Finite)
    (hE : E(H).Finite) (h3 : V(H).ncard = 3) {ℓ : β → ℕ} (_hinj : Set.InjOn ℓ E(H))
    (hc : IsTemporallyConnected H ℓ) : 3 ≤ E(H).ncard := by
  obtain ⟨a, b, c, hab, hac, hbc, hVabc⟩ := Set.ncard_eq_three.mp h3
  have ha : a ∈ V(H) := by rw [hVabc]; simp
  have hb : b ∈ V(H) := by rw [hVabc]; simp
  have hc' : c ∈ V(H) := by rw [hVabc]; simp
  -- adjacency of any two distinct vertices, given a third one
  have key : ∀ u v w : γ, u ∈ V(H) → v ∈ V(H) → w ∈ V(H) → u ≠ v → u ≠ w → v ≠ w →
      (∀ z ∈ V(H), z = u ∨ z = v ∨ z = w) → ∃ e, H.IsLink e u v := by
    intro u v w hu hv hw huv huw hvw hsub
    by_contra hno
    push Not at hno
    obtain ⟨e1, e2, l1, l2, lt1⟩ := two_step hv huv huw hvw hsub hno (hc u hu v hv)
    obtain ⟨f1, f2, m1, m2, lt2⟩ := two_step (ℓ := ℓ) hu huv.symm hvw huw
      (fun z hz => by rcases hsub z hz with h | h | h <;> tauto)
      (fun e h => hno e h.symm) (hc v hv u hu)
    have e1f2 : e1 = f2 := hS.eq_of_isLink l1 m2.symm
    have e2f1 : e2 = f1 := hS.eq_of_isLink l2 m1.symm
    subst e1f2 e2f1
    omega
  have hab' := key a b c ha hb hc' hab hac hbc (by rw [hVabc] at *; intro z hz; simpa using hz)
  have hbc' := key b c a hb hc' ha hbc hab.symm hac.symm
    (by intro z hz; rw [hVabc] at hz; simp at hz; tauto)
  have hac' := key a c b ha hc' hb hac hab hbc.symm
    (by intro z hz; rw [hVabc] at hz; simp at hz; tauto)
  obtain ⟨e1, l1⟩ := hab'
  obtain ⟨e2, l2⟩ := hbc'
  obtain ⟨e3, l3⟩ := hac'
  have n12 : e1 ≠ e2 := by
    rintro rfl
    rcases l1.left_eq_or_eq l2 with h | h
    · exact hab h
    · exact hac h
  have n13 : e1 ≠ e3 := by
    rintro rfl
    rcases l1.right_eq_or_eq l3 with h | h
    · exact hab h.symm
    · exact hbc h
  have n23 : e2 ≠ e3 := by
    rintro rfl
    rcases l2.left_eq_or_eq l3 with h | h
    · exact hab h.symm
    · exact hbc h
  have : ({e1, e2, e3} : Set β).ncard = 3 := Set.ncard_eq_three.mpr ⟨e1, e2, e3, n12, n13, n23, rfl⟩
  rw [← this]
  apply Set.ncard_le_ncard _ hE
  intro e he
  rcases he with rfl | rfl | rfl
  · exact l1.edge_mem
  · exact l2.edge_mem
  · exact l3.edge_mem

end Lax630294Proofs.SmallCases
