import Lax630294Proofs.ProtectedExtMin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Protected extension: from a protected tree with forest complement to an `M`-witness

Given `S` in the class `Cls` whose complement `K = E(H) \ S` is a forest, the sets
`L₁ = K \ {g}` and `L₂ = S \ {e, f₀, f₁}` together with the four-cycle `{e, g, f₀, f₁}` form an
`M`-witness (paper l. 4803-4812), and each component of `L₁`, `L₂` contains exactly one of the four
vertices `x₀, x₁, u₀, u₁`.
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β} {x0 x1 u0 u1 : α} {e f0 f1 g : β}

/-- Every component of `L` contains exactly one of the four vertices `x0 x1 u0 u1`. -/
def OneEach (H : Graph α β) (L : Set β) (x0 x1 u0 u1 : α) : Prop :=
  ∀ v ∈ V(H), ∃! c, c ∈ ({x0, x1, u0, u1} : Set α) ∧ Reach H L v c

lemma isCycle_four (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    (hv : x0 ≠ x1 ∧ x0 ≠ u0 ∧ x0 ≠ u1 ∧ x1 ≠ u0 ∧ x1 ≠ u1 ∧ u0 ≠ u1)
    (he : e ≠ g ∧ e ≠ f0 ∧ e ≠ f1 ∧ g ≠ f0 ∧ g ≠ f1 ∧ f0 ≠ f1) :
    IsCycle H ({e, g, f0, f1} : Set β) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := hv
  obtain ⟨k01, k02, k03, k12, k13, k23⟩ := he
  refine ⟨4, by decide, ![x0, u0, u1, x1], ![f0, g, f1, e], ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | simp_all [eq_comm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | simp_all [eq_comm]
  · intro i
    fin_cases i
    · exact geo.lf0
    · exact geo.lg
    · exact geo.lf1.symm
    · exact geo.le.symm
  · ext k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨3, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩

lemma encard_four (he : e ≠ g ∧ e ≠ f0 ∧ e ≠ f1 ∧ g ≠ f0 ∧ g ≠ f1 ∧ f0 ≠ f1) :
    ({e, g, f0, f1} : Set β).encard = 4 := by
  obtain ⟨k01, k02, k03, k12, k13, k23⟩ := he
  rw [Set.encard_insert_of_notMem, Set.encard_insert_of_notMem, Set.encard_pair k23]
  · rfl
  · simp [k12, k13]
  · simp [k01, k02, k03]

/-- Pigeonhole: if `n` vertices lie in `n` different components of `F` and `F` has exactly `n`
components, every vertex is connected to one of them. -/
lemma cover_of_pairwise {n : ℕ} (hV : V(H).Finite) {F : Set β} (hc : comps H F = n)
    (z : Fin n → α) (hz : ∀ i, z i ∈ V(H)) (hd : ∀ i j, i ≠ j → ¬ Reach H F (z i) (z j)) :
    ∀ v ∈ V(H), ∃ i, Reach H F v (z i) := by
  have : Finite V(H) := hV.to_subtype
  have : Finite (CC H F) := Quotient.finite _
  let f : Fin n → CC H F := fun i => Quotient.mk _ ⟨z i, hz i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hd i j hne (Quotient.exact hij)
  have hcard : Nat.card (CC H F) ≤ Nat.card (Fin n) := by
    rw [Nat.card_fin]; unfold comps at hc; omega
  have hbij := hinj.bijective_of_nat_card_le hcard
  intro v hv
  obtain ⟨i, hi⟩ := hbij.2 (Quotient.mk _ ⟨v, hv⟩)
  exact ⟨i, Quotient.exact hi.symm⟩

/-- Pairwise disconnected vertices in a forest relative to `S`: a cycle through `k`. -/
lemma not_reach_of_forest {S F' : Set β} (hSf : IsForest H S) {k : β} {a b : α}
    (hl : H.IsLink k a b) (hk : k ∉ F') (hsub : insert k F' ⊆ S) (hr : Reach H F' a b) :
    False :=
  not_isForest_insert_of_reach hl hk hr (hSf.mono hsub)

lemma pair4 {F : Set β} (h01 : ¬ Reach H F x0 x1) (h02 : ¬ Reach H F x0 u0)
    (h03 : ¬ Reach H F x0 u1) (h12 : ¬ Reach H F x1 u0) (h13 : ¬ Reach H F x1 u1)
    (h23 : ¬ Reach H F u0 u1) :
    ∀ c ∈ ({x0, x1, u0, u1} : Set α), ∀ c' ∈ ({x0, x1, u0, u1} : Set α),
      Reach H F c c' → c = c' := by
  intro c hc c' hc' h
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd h h01 | exact absurd h h02 | exact absurd h h03
    | exact absurd h h12 | exact absurd h h13 | exact absurd h h23
    | exact absurd h.symm' h01 | exact absurd h.symm' h02 | exact absurd h.symm' h03
    | exact absurd h.symm' h12 | exact absurd h.symm' h13 | exact absurd h.symm' h23

lemma cover4 (hV : V(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g) {F : Set β}
    (hc : comps H F = 4) (h01 : ¬ Reach H F x0 x1) (h02 : ¬ Reach H F x0 u0)
    (h03 : ¬ Reach H F x0 u1) (h12 : ¬ Reach H F x1 u0) (h13 : ¬ Reach H F x1 u1)
    (h23 : ¬ Reach H F u0 u1) :
    ∀ v ∈ V(H), ∃ c, c ∈ ({x0, x1, u0, u1} : Set α) ∧ Reach H F v c := by
  intro v hv
  have := cover_of_pairwise hV hc ![x0, x1, u0, u1] (by
    intro i; fin_cases i
    · exact geo.le.left_mem
    · exact geo.le.right_mem
    · exact geo.lg.left_mem
    · exact geo.lg.right_mem) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
      | exact fun h => h01 h.symm' | exact fun h => h02 h.symm' | exact fun h => h03 h.symm'
      | exact fun h => h12 h.symm' | exact fun h => h13 h.symm' | exact fun h => h23 h.symm') v hv
  obtain ⟨i, hi⟩ := this
  refine ⟨_, ?_, hi⟩
  fin_cases i <;> simp

lemma oneEach_of (hV : V(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g) {F : Set β}
    (hc : comps H F = 4) (h01 : ¬ Reach H F x0 x1) (h02 : ¬ Reach H F x0 u0)
    (h03 : ¬ Reach H F x0 u1) (h12 : ¬ Reach H F x1 u0) (h13 : ¬ Reach H F x1 u1)
    (h23 : ¬ Reach H F u0 u1) : OneEach H F x0 x1 u0 u1 := by
  intro v hv
  obtain ⟨c, hcT, hcr⟩ := cover4 hV geo hc h01 h02 h03 h12 h13 h23 v hv
  refine ⟨c, ⟨hcT, hcr⟩, fun c' ⟨hc'T, hc'r⟩ => ?_⟩
  exact pair4 h01 h02 h03 h12 h13 h23 c' hc'T c hcT (hc'r.symm'.trans' hcr)

lemma meeting_of (hV : V(H).Finite) (hE : E(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    {F : Set β} (hFE : F ⊆ E(H)) (hFc : comps H F = 4) (hFn : F.ncard + 4 = V(H).ncard)
    (hone : OneEach H F x0 x1 u0 u1) :
    Lax630294.MGraph.IsFourComponentForestMeeting H {e, g, f0, f1} F := by
  refine ⟨(isSpanningForest_iff hV hE).2 ⟨hFE, hFc, hFn⟩, ?_⟩
  intro x
  obtain ⟨c, ⟨hcT, hcr⟩, -⟩ := hone x.1 x.2
  have hcV : c ∈ V(H) ∧ c ∈ incidentVertices H {e, g, f0, f1} := by
    rcases hcT with rfl | rfl | rfl | hc
    · exact ⟨geo.le.left_mem, e, by simp, geo.le.inc_left⟩
    · exact ⟨geo.le.right_mem, e, by simp, geo.le.inc_right⟩
    · exact ⟨geo.lg.left_mem, g, by simp, geo.lg.inc_left⟩
    · obtain rfl := Set.mem_singleton_iff.1 hc
      exact ⟨geo.lg.right_mem, g, by simp, geo.lg.inc_right⟩
  exact ⟨⟨c, hcV.1⟩, hcV.2, (underlying_reachable_iff x ⟨c, hcV.1⟩).2 hcr⟩

/-- **From a protected tree with forest complement to an `M`-witness.** -/
theorem mwitness_of_cls (hV : V(H).Finite) (hE : E(H).Finite)
    (geo : Geo H x0 x1 u0 u1 e f0 f1 g) (hcard : E(H).ncard + 4 = 2 * V(H).ncard)
    (hv : x0 ≠ x1 ∧ x0 ≠ u0 ∧ x0 ≠ u1 ∧ x1 ≠ u0 ∧ x1 ≠ u1 ∧ u0 ≠ u1)
    (he : e ≠ g ∧ e ≠ f0 ∧ e ≠ f1 ∧ g ≠ f0 ∧ g ≠ f1 ∧ f0 ≠ f1)
    {S : Set β} (hS : Cls H x0 x1 u0 e f0 f1 g S) (hF : IsForest H (E(H) \ S)) :
    Lax630294.MGraph.IsMWitness H {e, g, f0, f1} ((E(H) \ S) \ {g}) (S \ {e, f0, f1}) ∧
      OneEach H ((E(H) \ S) \ {g}) x0 x1 u0 u1 ∧ OneEach H (S \ {e, f0, f1}) x0 x1 u0 u1 := by
  classical
  obtain ⟨k01, k02, k03, k12, k13, k23⟩ := he
  have hSt := hS.tree
  obtain ⟨hSE, hne, hconn, hcardS⟩ := (isSpanningTree_iff hV hE).1 hSt
  have hSc : comps H S = 1 := (comps_eq_one_iff hV).2 ⟨hne, hconn⟩
  have hSf : IsForest H S := isForest_of_card hV hE hSE (by omega)
  have hKE : E(H) \ S ⊆ E(H) := Set.sdiff_subset
  have hgK : g ∈ E(H) \ S := ⟨hS.hgE, hS.hgS⟩
  have hSfin : S.Finite := hE.subset hSE
  have hKcard : (E(H) \ S).ncard + 3 = V(H).ncard := by
    rw [Set.ncard_sdiff hSE hSfin]
    have := Set.ncard_le_ncard hSE hE
    omega
  have hKc : comps H (E(H) \ S) = 3 := by
    have := forest_card hV hE hKE hF
    omega
  -- the forest `L1`
  have hL1K : insert g ((E(H) \ S) \ {g}) = E(H) \ S := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hgK]
  have hL1E : (E(H) \ S) \ {g} ⊆ E(H) := Set.sdiff_subset.trans hKE
  have hL1bridge : ¬ Reach H ((E(H) \ S) \ {g}) u0 u1 := forest_bridge hF hgK geo.lg
  have hL1c : comps H ((E(H) \ S) \ {g}) = 4 := by
    have := comps_insert_of_not_reach hV geo.lg hL1bridge
    rw [hL1K] at this
    omega
  have hL1card : ((E(H) \ S) \ {g}).ncard + 4 = V(H).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hgK]
    have : 0 < (E(H) \ S).ncard := (Set.ncard_pos (hE.subset hKE)).2 ⟨g, hgK⟩
    omega
  have hL1mono : ∀ {a b : α}, Reach H ((E(H) \ S) \ {g}) a b → Reach H (E(H) \ S) a b :=
    fun h => reach_mono Set.sdiff_subset h
  have hug : Reach H (E(H) \ S) u1 u0 := reach_of_isLink hgK geo.lg.symm
  have l01 : ¬ Reach H ((E(H) \ S) \ {g}) x0 x1 := fun h => hS.d01 (hL1mono h)
  have l02 : ¬ Reach H ((E(H) \ S) \ {g}) x0 u0 := fun h => hS.d0u (hL1mono h)
  have l12 : ¬ Reach H ((E(H) \ S) \ {g}) x1 u0 := fun h => hS.d1u (hL1mono h)
  have l03 : ¬ Reach H ((E(H) \ S) \ {g}) x0 u1 := fun h =>
    hS.d0u ((hL1mono h).trans' hug)
  have l13 : ¬ Reach H ((E(H) \ S) \ {g}) x1 u1 := fun h =>
    hS.d1u ((hL1mono h).trans' hug)
  have hone1 := oneEach_of hV geo hL1c l01 l02 l03 l12 l13 hL1bridge
  -- the forest `L2`
  have hP3 : ({e, f0, f1} : Set β) ⊆ S := by
    intro k hk
    rcases hk with rfl | rfl | rfl
    · exact hS.he
    · exact hS.hf0
    · exact hS.hf1
  have hP3card : ({e, f0, f1} : Set β).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨e, f0, f1, k02, k03, k23, rfl⟩
  have hL2S : S \ {e, f0, f1} ⊆ S := Set.sdiff_subset
  have hL2E : S \ {e, f0, f1} ⊆ E(H) := hL2S.trans hSE
  have hL2f : IsForest H (S \ {e, f0, f1}) := hSf.mono hL2S
  have hL2card : (S \ {e, f0, f1}).ncard + 3 = S.ncard := by
    rw [Set.ncard_sdiff hP3 (hSfin.subset hP3), hP3card]
    have := Set.ncard_le_ncard hP3 hSfin
    omega
  have hL2c : comps H (S \ {e, f0, f1}) = 4 := by
    have := forest_card hV hE hL2E hL2f
    omega
  have hL2n : (S \ {e, f0, f1}).ncard + 4 = V(H).ncard := by omega
  have eL2 : e ∉ S \ {e, f0, f1} := fun h => h.2 (by simp)
  have f0L2 : f0 ∉ S \ {e, f0, f1} := fun h => h.2 (by simp)
  have f1L2 : f1 ∉ S \ {e, f0, f1} := fun h => h.2 (by simp)
  have sub_e : insert e (S \ {e, f0, f1}) ⊆ S :=
    Set.insert_subset hS.he hL2S
  have sub_f0 : insert f0 (S \ {e, f0, f1}) ⊆ S :=
    Set.insert_subset hS.hf0 hL2S
  have sub_ef1 : insert f1 (insert e (S \ {e, f0, f1})) ⊆ S :=
    Set.insert_subset hS.hf1 sub_e
  have sub_ef0 : insert f0 (insert e (S \ {e, f0, f1})) ⊆ S :=
    Set.insert_subset hS.hf0 sub_e
  have sub_eff : insert f1 (insert f0 (insert e (S \ {e, f0, f1}))) ⊆ S :=
    Set.insert_subset hS.hf1 sub_ef0
  have hmono1 : ∀ {a b : α}, Reach H (S \ {e, f0, f1}) a b →
      Reach H (insert e (S \ {e, f0, f1})) a b := fun h => reach_mono (Set.subset_insert _ _) h
  have hmono2 : ∀ {a b : α}, Reach H (insert e (S \ {e, f0, f1})) a b →
      Reach H (insert f0 (insert e (S \ {e, f0, f1}))) a b :=
    fun h => reach_mono (Set.subset_insert _ _) h
  have he01 : Reach H (insert e (S \ {e, f0, f1})) x0 x1 :=
    reach_of_isLink (Set.mem_insert _ _) geo.le
  have he10 : Reach H (insert e (S \ {e, f0, f1})) x1 x0 :=
    reach_of_isLink (Set.mem_insert _ _) geo.le.symm
  have hf0m : Reach H (insert f0 (insert e (S \ {e, f0, f1}))) x0 u0 :=
    reach_of_isLink (Set.mem_insert _ _) geo.lf0
  have hnf1 : f1 ∉ insert e (S \ {e, f0, f1}) := by
    rintro (h | h)
    · exact k03 h.symm
    · exact f1L2 h
  have hnf0 : f0 ∉ insert e (S \ {e, f0, f1}) := by
    rintro (h | h)
    · exact k02 h.symm
    · exact f0L2 h
  have hnf1' : f1 ∉ insert f0 (insert e (S \ {e, f0, f1})) := by
    rintro (h | h)
    · exact k23 h.symm
    · exact hnf1 h
  have m01 : ¬ Reach H (S \ {e, f0, f1}) x0 x1 := fun h =>
    not_reach_of_forest hSf geo.le eL2 sub_e h
  have m02 : ¬ Reach H (S \ {e, f0, f1}) x0 u0 := fun h =>
    not_reach_of_forest hSf geo.lf0 f0L2 sub_f0 h
  have m13 : ¬ Reach H (S \ {e, f0, f1}) x1 u1 := fun h =>
    not_reach_of_forest hSf geo.lf1 f1L2 (Set.insert_subset hS.hf1 hL2S) h
  have m03 : ¬ Reach H (S \ {e, f0, f1}) x0 u1 := fun h =>
    not_reach_of_forest hSf geo.lf1 hnf1 sub_ef1 (he10.trans' (hmono1 h))
  have m12 : ¬ Reach H (S \ {e, f0, f1}) x1 u0 := fun h =>
    not_reach_of_forest hSf geo.lf0 hnf0 sub_ef0 (he01.trans' (hmono1 h))
  have m23 : ¬ Reach H (S \ {e, f0, f1}) u0 u1 := fun h =>
    not_reach_of_forest hSf geo.lf1 hnf1' sub_eff
      ((hmono2 he10).trans' (hf0m.trans' ((hmono2 (hmono1 h)))))
  have hone2 := oneEach_of hV geo hL2c m01 m02 m03 m12 m13 m23
  refine ⟨⟨isCycle_four geo hv ⟨k01, k02, k03, k12, k13, k23⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hone1, hone2⟩
  · rw [encard_four ⟨k01, k02, k03, k12, k13, k23⟩]
  · exact meeting_of hV hE geo hL1E hL1c hL1card hone1
  · exact meeting_of hV hE geo hL2E hL2c hL2n hone2
  · refine Set.disjoint_left.2 fun k hk hk' => ?_
    rcases hk with rfl | rfl | rfl | rfl
    · exact hk'.1.2 hS.he
    · exact hk'.2 rfl
    · exact hk'.1.2 hS.hf0
    · exact hk'.1.2 hS.hf1
  · refine Set.disjoint_left.2 fun k hk hk' => ?_
    rcases hk with rfl | rfl | rfl | rfl
    · exact hk'.2 (by simp)
    · exact hS.hgS hk'.1
    · exact hk'.2 (by simp)
    · exact hk'.2 (by simp)
  · exact Set.disjoint_left.2 fun k hk hk' => hk.1.2 hk'.1

end Lax630294Proofs.ProtectedExt
