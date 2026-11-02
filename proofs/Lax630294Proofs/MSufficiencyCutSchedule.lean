import Lax630294Proofs.MSufficiencyGeometry

/-!
# The schedule of an `M`-witness along a cycle with four cut edges
-/

namespace Lax630294Proofs.MSufficiencyCutSchedule

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal Lax630294Proofs.ThreePhase
  Lax630294Proofs.MSufficiencySchedule Lax630294Proofs.MSufficiencyGeometry

variable {α β : Type*} {G : Graph α β}

/-- DEVIATION (formulation): the paper describes the schedule on the four intervals
`X₁,…,X₄` with essential edges `b₁,…,b₄`; here the intervals are `[0,c1], [c1+1,c2],
[c2+1,c3], [c3+1,n-1]` of a linearly indexed cycle, `b₁ = f c1, b₂ = f c2, b₃ = f c3,
b₄ = f (n-1)`.  Gather along `F₁` towards the endpoints of `b₁,b₃`, call `b₁,b₃`, walk along the
interval paths from the endpoints of `b₁,b₃` to the endpoints of `b₂,b₄`, call `b₂,b₄`, and
distribute along `F₂` from the endpoints of `b₂,b₄`.  The 16 walks between roots are obtained by
composing the four building blocks `path`, `b₁/b₃-hop`, `b₂/b₄-hop`. -/
theorem schedule_from_cuts (hV : V(G).Finite) {F1 F2 : Set β}
    {n : ℕ} {u : ℕ → α} {f : ℕ → β}
    (hlink : ∀ k, k + 1 < n → G.IsLink (f k) (u k) (u (k + 1)))
    (hwrap : G.IsLink (f (n - 1)) (u (n - 1)) (u 0))
    (finj : ∀ k k', k < n → k' < n → f k = f k' → k = k')
    {c1 c2 c3 : ℕ} (h12 : c1 < c2) (h23 : c2 < c3) (h3n : c3 < n - 1)
    (hr1 : ∀ k, k + 1 < n → k ≠ c1 → k ≠ c2 → k ≠ c3 →
      Relation.ReflTransGen (step G F1) (u k) (u (k + 1)))
    (hr2 : ∀ k, k + 1 < n → k ≠ c1 → k ≠ c2 → k ≠ c3 →
      Relation.ReflTransGen (step G F2) (u k) (u (k + 1)))
    (hm1 : ∀ x ∈ V(G), ∃ m, m < n ∧ Relation.ReflTransGen (step G F1) x (u m))
    (hm2 : ∀ x ∈ V(G), ∃ m, m < n ∧ Relation.ReflTransGen (step G F2) x (u m))
    (hd12 : Disjoint F1 F2) (hd1 : ∀ k, k < n → f k ∉ F1) (hd2 : ∀ k, k < n → f k ∉ F2) :
    IsLabelConnected G := by
  classical
  let lmI : ℕ → ℕ := fun k => if k = c1 ∨ k = c3 then 1 else if k = c2 ∨ k = n - 1 then n + 3
      else if (c1 < k ∧ k < c2) ∨ (c3 < k ∧ k < n - 1) then 2 + k else 2 + (n - k)
  let lm : β → ℕ := fun e => if h : ∃ k, k < n ∧ f k = e then lmI h.choose else 0
  have hlm : ∀ k, k < n → lm (f k) = lmI k := by
    intro k hk
    have h : ∃ k', k' < n ∧ f k' = f k := ⟨k, hk, rfl⟩
    simp only [lm, dif_pos h]
    congr 1
    exact finj _ _ h.choose_spec.1 hk h.choose_spec.2
  have hI1 : lmI c1 = 1 := by simp [lmI]
  have hI3 : lmI c3 = 1 := by simp [lmI]
  have hI2 : lmI c2 = n + 3 := by
    have e1 : c2 ≠ c1 := by omega
    have e2 : c2 ≠ c3 := by omega
    simp [lmI, e1, e2]
  have hI4 : lmI (n - 1) = n + 3 := by
    have e1 : n - 1 ≠ c1 := by omega
    have e2 : n - 1 ≠ c3 := by omega
    simp [lmI, e1, e2]
  have hIf1 : ∀ k, c1 < k → k < c2 → lmI k = 2 + k := by
    intro k h1 h2; simp only [lmI]; split_ifs <;> omega
  have hIf3 : ∀ k, c3 < k → k < n - 1 → lmI k = 2 + k := by
    intro k h1 h2; simp only [lmI]; split_ifs <;> omega
  have hIb0 : ∀ k, k < c1 → lmI k = 2 + (n - k) := by
    intro k h1; simp only [lmI]; split_ifs <;> omega
  have hIb2 : ∀ k, c2 < k → k < c3 → lmI k = 2 + (n - k) := by
    intro k h1 h2; simp only [lmI]; split_ifs <;> omega
  let p : Fin 4 → α := ![u c1, u (c1 + 1), u c3, u (c3 + 1)]
  let q : Fin 4 → α := ![u 0, u c2, u (c2 + 1), u (n - 1)]
  let σ : Fin 4 → Fin 4 := ![1, 0, 3, 2]
  let τ : Fin 4 → Fin 4 := ![3, 2, 1, 0]
  let Mid : Set β := {g | ∃ k, k < n ∧ f k = g}
  -- paths inside the intervals
  have key : ∀ g (k : ℕ), k < n → k ≠ c1 → k ≠ c2 → k ≠ c3 → k ≠ n - 1 → g = f k →
      g ∈ Mid ∧ 2 ≤ lm g ∧ lm g ≤ n + 2 := by
    intro g k hk h1 h2 h3 h4 hg
    subst hg
    refine ⟨⟨k, hk, rfl⟩, ?_⟩
    rw [hlm k hk]
    simp only [lmI]
    split_ifs <;> omega
  have hP : ∀ a : Fin 4, ∃ vs es, TW G lm (p a) (q a) vs es ∧
      ∀ g ∈ es, g ∈ Mid ∧ 2 ≤ lm g ∧ lm g ≤ n + 2 := by
    intro a
    fin_cases a
    · obtain ⟨vs, es, hw, hg⟩ := walk_bwd (L := lmI) hlink hlm c1 0 (by omega) (by
        intro k k' hk hkk' hk'
        rw [hIb0 k (by omega), hIb0 k' (by omega)]; omega)
      refine ⟨vs, es, ?_, fun g hg' => ?_⟩
      · simpa [p, q] using hw
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hg'
        exact key _ k (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    · obtain ⟨vs, es, hw, hg⟩ := walk_fwd (L := lmI) hlink hlm (c2 - (c1 + 1)) (c1 + 1)
        (by omega) (by
        intro k k' hk hkk' hk'
        rw [hIf1 k (by omega) (by omega), hIf1 k' (by omega) (by omega)]; omega)
      have e : c1 + 1 + (c2 - (c1 + 1)) = c2 := by omega
      rw [e] at hw
      refine ⟨vs, es, ?_, fun g hg' => ?_⟩
      · simpa [p, q] using hw
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hg'
        exact key _ k (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    · obtain ⟨vs, es, hw, hg⟩ := walk_bwd (L := lmI) hlink hlm (c3 - (c2 + 1)) (c2 + 1)
        (by omega) (by
        intro k k' hk hkk' hk'
        rw [hIb2 k (by omega) (by omega), hIb2 k' (by omega) (by omega)]; omega)
      have e : c2 + 1 + (c3 - (c2 + 1)) = c3 := by omega
      rw [e] at hw
      refine ⟨vs, es, ?_, fun g hg' => ?_⟩
      · simpa [p, q] using hw
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hg'
        exact key _ k (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    · obtain ⟨vs, es, hw, hg⟩ := walk_fwd (L := lmI) hlink hlm (n - 1 - (c3 + 1)) (c3 + 1)
        (by omega) (by
        intro k k' hk hkk' hk'
        rw [hIf3 k (by omega) (by omega), hIf3 k' (by omega) (by omega)]; omega)
      have e : c3 + 1 + (n - 1 - (c3 + 1)) = n - 1 := by omega
      rw [e] at hw
      refine ⟨vs, es, ?_, fun g hg' => ?_⟩
      · simpa [p, q] using hw
      · obtain ⟨k, hk1, hk2, rfl⟩ := hg g hg'
        exact key _ k (by omega) (by omega) (by omega) (by omega) (by omega) rfl
  -- hops over the cut edges
  have hH1 : ∀ a : Fin 4, ∃ vs es, TW G lm (p a) (p (σ a)) vs es ∧
      ∀ g ∈ es, g ∈ Mid ∧ lm g = 1 := by
    intro a
    fin_cases a
    · refine ⟨_, _, (TW.single (hlink c1 (by omega)) : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c1, by omega, rfl⟩, by rw [hlm c1 (by omega), hI1]⟩
    · refine ⟨_, _, (TW.single (hlink c1 (by omega)).symm : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c1, by omega, rfl⟩, by rw [hlm c1 (by omega), hI1]⟩
    · refine ⟨_, _, (TW.single (hlink c3 (by omega)) : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c3, by omega, rfl⟩, by rw [hlm c3 (by omega), hI3]⟩
    · refine ⟨_, _, (TW.single (hlink c3 (by omega)).symm : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c3, by omega, rfl⟩, by rw [hlm c3 (by omega), hI3]⟩
  have hH2 : ∀ a : Fin 4, ∃ vs es, TW G lm (q a) (q (τ a)) vs es ∧
      ∀ g ∈ es, g ∈ Mid ∧ lm g = n + 3 := by
    intro a
    fin_cases a
    · refine ⟨_, _, (TW.single hwrap.symm : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨n - 1, by omega, rfl⟩, by rw [hlm (n - 1) (by omega), hI4]⟩
    · refine ⟨_, _, (TW.single (hlink c2 (by omega)) : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c2, by omega, rfl⟩, by rw [hlm c2 (by omega), hI2]⟩
    · refine ⟨_, _, (TW.single (hlink c2 (by omega)).symm : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨c2, by omega, rfl⟩, by rw [hlm c2 (by omega), hI2]⟩
    · refine ⟨_, _, (TW.single hwrap : TW G lm _ _ _ _), ?_⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨⟨n - 1, by omega, rfl⟩, by rw [hlm (n - 1) (by omega), hI4]⟩
  -- the middle walks between all pairs of roots
  have hcomb : ∀ a j : Fin 4, ∃ vs es, TW G lm (p a) (q j) vs es ∧
      ∀ g ∈ es, g ∈ Mid ∧ 1 ≤ lm g ∧ lm g ≤ n + 3 := by
    have hcases : ∀ a j : Fin 4, j = a ∨ j = τ a ∨ j = σ a ∨ j = τ (σ a) := by decide
    intro a j
    rcases hcases a j with h | h | h | h <;> rw [h]
    · obtain ⟨vs, es, hw, hg⟩ := hP a
      exact ⟨vs, es, hw, fun g hg' => ⟨(hg g hg').1, by have := (hg g hg').2.1; omega,
        by have := (hg g hg').2.2; omega⟩⟩
    · obtain ⟨vs1, es1, hw1, hg1⟩ := hP a
      obtain ⟨vs2, es2, hw2, hg2⟩ := hH2 a
      refine ⟨_, _, hw1.append hw2 (fun f hf g hg => ?_), fun g hg => ?_⟩
      · have := (hg1 f hf).2.2
        have := (hg2 g hg).2
        omega
      · rcases List.mem_append.1 hg with hg | hg
        · exact ⟨(hg1 g hg).1, by have := (hg1 g hg).2.1; omega,
            by have := (hg1 g hg).2.2; omega⟩
        · exact ⟨(hg2 g hg).1, by have := (hg2 g hg).2; omega, by have := (hg2 g hg).2; omega⟩
    · obtain ⟨vs1, es1, hw1, hg1⟩ := hH1 a
      obtain ⟨vs2, es2, hw2, hg2⟩ := hP (σ a)
      refine ⟨_, _, hw1.append hw2 (fun f hf g hg => ?_), fun g hg => ?_⟩
      · have := (hg1 f hf).2
        have := (hg2 g hg).2.1
        omega
      · rcases List.mem_append.1 hg with hg | hg
        · exact ⟨(hg1 g hg).1, by have := (hg1 g hg).2; omega, by have := (hg1 g hg).2; omega⟩
        · exact ⟨(hg2 g hg).1, by have := (hg2 g hg).2.1; omega,
            by have := (hg2 g hg).2.2; omega⟩
    · obtain ⟨vs1, es1, hw1, hg1⟩ := hH1 a
      obtain ⟨vs2, es2, hw2, hg2⟩ := hP (σ a)
      obtain ⟨vs3, es3, hw3, hg3⟩ := hH2 (σ a)
      have hw12 := hw1.append hw2 (fun f hf g hg => by
        have := (hg1 f hf).2
        have := (hg2 g hg).2.1
        omega)
      refine ⟨_, _, hw12.append hw3 (fun f hf g hg => ?_), fun g hg => ?_⟩
      · rcases List.mem_append.1 hf with hf | hf
        · have := (hg1 f hf).2
          have := (hg3 g hg).2
          omega
        · have := (hg2 f hf).2.2
          have := (hg3 g hg).2
          omega
      · rcases List.mem_append.1 hg with hg | hg
        · rcases List.mem_append.1 hg with hg | hg
          · exact ⟨(hg1 g hg).1, by have := (hg1 g hg).2; omega,
              by have := (hg1 g hg).2; omega⟩
          · exact ⟨(hg2 g hg).1, by have := (hg2 g hg).2.1; omega,
              by have := (hg2 g hg).2.2; omega⟩
        · exact ⟨(hg3 g hg).1, by have := (hg3 g hg).2; omega, by have := (hg3 g hg).2; omega⟩
  -- gathering and distributing
  have chain1 : ∀ a b, a ≤ b → b < n → (∀ k, a ≤ k → k < b → k ≠ c1 ∧ k ≠ c2 ∧ k ≠ c3) →
      Relation.ReflTransGen (step G F1) (u a) (u b) := by
    intro a b hab hb hk
    exact rtg_between u hab (fun k hk1 hk2 =>
      hr1 k (by omega) (hk k hk1 hk2).1 (hk k hk1 hk2).2.1 (hk k hk1 hk2).2.2)
  have chain2 : ∀ a b, a ≤ b → b < n → (∀ k, a ≤ k → k < b → k ≠ c1 ∧ k ≠ c2 ∧ k ≠ c3) →
      Relation.ReflTransGen (step G F2) (u a) (u b) := by
    intro a b hab hb hk
    exact rtg_between u hab (fun k hk1 hk2 =>
      hr2 k (by omega) (hk k hk1 hk2).1 (hk k hk1 hk2).2.1 (hk k hk1 hk2).2.2)
  have hsymm : ∀ (F : Set β) (x y : α), Relation.ReflTransGen (step G F) x y →
      Relation.ReflTransGen (step G F) y x := fun F x y h =>
    rtg_symm (fun _ _ h => step_symm h) h
  refine three_phase_gen hV F1 F2 Mid (Set.range p) (Set.range q) lm (n + 3) hd12 ?_ ?_ ?_ ?_ ?_
  · refine Set.disjoint_left.2 (fun g hg hgM => ?_)
    obtain ⟨k, hk, rfl⟩ := hgM
    exact hd1 k hk hg
  · refine Set.disjoint_left.2 (fun g hg hgM => ?_)
    obtain ⟨k, hk, rfl⟩ := hgM
    exact hd2 k hk hg
  · intro x hx
    obtain ⟨m, hm, hxm⟩ := hm1 x hx
    by_cases h1 : m ≤ c1
    · exact ⟨p 0, ⟨0, rfl⟩, hxm.trans (chain1 m c1 h1 (by omega) (by intro k a b; omega))⟩
    by_cases h2 : m ≤ c2
    · exact ⟨p 1, ⟨1, rfl⟩, hxm.trans (hsymm F1 _ _
        (chain1 (c1 + 1) m (by omega) hm (by intro k a b; omega)))⟩
    by_cases h3 : m ≤ c3
    · exact ⟨p 2, ⟨2, rfl⟩, hxm.trans (chain1 m c3 h3 (by omega) (by intro k a b; omega))⟩
    · exact ⟨p 3, ⟨3, rfl⟩, hxm.trans (hsymm F1 _ _
        (chain1 (c3 + 1) m (by omega) hm (by intro k a b; omega)))⟩
  · intro y hy
    obtain ⟨m, hm, hxm⟩ := hm2 y hy
    have hxm' := hsymm F2 _ _ hxm
    by_cases h1 : m ≤ c1
    · exact ⟨q 0, ⟨0, rfl⟩, (chain2 0 m (by omega) hm (by intro k a b; omega)).trans hxm'⟩
    by_cases h2 : m ≤ c2
    · exact ⟨q 1, ⟨1, rfl⟩, (hsymm F2 _ _
        (chain2 m c2 h2 (by omega) (by intro k a b; omega))).trans hxm'⟩
    by_cases h3 : m ≤ c3
    · exact ⟨q 2, ⟨2, rfl⟩, (chain2 (c2 + 1) m (by omega) hm (by intro k a b; omega)).trans hxm'⟩
    · exact ⟨q 3, ⟨3, rfl⟩, (hsymm F2 _ _
        (chain2 m (n - 1) (by omega) (by omega) (by intro k a b; omega))).trans hxm'⟩
  · rintro r ⟨a, rfl⟩ r' ⟨j, rfl⟩
    obtain ⟨vs, es, hw, hg⟩ := hcomb a j
    exact ⟨vs, es, hw, hg⟩

end Lax630294Proofs.MSufficiencyCutSchedule
