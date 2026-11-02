import Lax630294Proofs.ThreePhase

/-!
# Generalised three-phase schedule

Like `ThreePhase.three_phase`, but the middle phase between the gathering roots and the
distribution roots is an arbitrary family of temporal walks (with labels in `[1, K]`) on a
set `Mid` of edges, instead of a single hub edge.

DEVIATION (organisation only): the paper's proof of `lem:construct-labeling` describes the whole
schedule at once; here the gather/distribute phases (as in `ThreePhase`) are separated from the
cycle-specific middle phase, which is treated in `MSufficiencyGeometry`.
-/

namespace Lax630294Proofs.MSufficiencySchedule

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal Lax630294Proofs.ThreePhase

variable {α β : Type*} {G : Graph α β}

/-- Shifting all labels of a walk by a constant keeps it temporal. -/
lemma tw_shift {ℓ ℓ' : β → ℕ} {M : ℕ} {u v : α} {vs : List α} {es : List β}
    (h : TW G ℓ u v vs es) (hl : ∀ f ∈ es, ℓ' f = M + ℓ f) : TW G ℓ' u v vs es := by
  induction h with
  | nil => exact .nil _
  | cons hlk hw hlab ih =>
    rename_i u z w' e vs es
    refine .cons hlk (ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))) ?_
    intro f hf
    have h1 := hl e (List.mem_cons_self ..)
    have h2 := hl f (List.mem_cons_of_mem _ hf)
    have := hlab f hf
    omega

open Classical in
/-- Labeling for the generalised three-phase scheme. -/
noncomputable def genLabel (G : Graph α β) (A B Mid : Set β) (RA RB : Set α) (lm : β → ℕ)
    (M K : ℕ) (e : β) : ℕ :=
  if e ∈ A then M - edgeMax G (dep G A RA) e
  else if e ∈ B then M + K + 1 + edgeMax G (dep G B RB) e
  else if e ∈ Mid then M + lm e else 0

-- DEVIATION: instead of rooting each component of F_1 (resp. F_2) at one chosen vertex as in
-- the paper, the forests are gathered/distributed towards/from the *set* of four roots (nearest
-- root, as in ThreePhase); no information on how the components of the forest and the roots
-- correspond is needed. The labeling of the middle phase is arbitrary and only its walks matter.
theorem three_phase_gen (hV : V(G).Finite) (A B Mid : Set β) (RA RB : Set α) (lm : β → ℕ)
    (K : ℕ)
    (hAB : Disjoint A B) (hAM : Disjoint A Mid) (hBM : Disjoint B Mid)
    (hA : ∀ x ∈ V(G), ∃ r ∈ RA, Relation.ReflTransGen (step G A) x r)
    (hB : ∀ y ∈ V(G), ∃ r ∈ RB, Relation.ReflTransGen (step G B) r y)
    (hM : ∀ r ∈ RA, ∀ r' ∈ RB, ∃ vs es, TW G lm r r' vs es ∧
      ∀ f ∈ es, f ∈ Mid ∧ 1 ≤ lm f ∧ lm f ≤ K) :
    IsLabelConnected G := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, ∀ x ∈ V(G), dep G A RA x ≤ N ∧ dep G B RB x ≤ N := by
    obtain ⟨N, hN⟩ := Set.Finite.bddAbove (hV.image fun x => max (dep G A RA x) (dep G B RB x))
    refine ⟨N, fun x hx => ?_⟩
    have := hN ⟨x, hx, rfl⟩
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  set M := N + 1 with hM'
  set ℓ := genLabel G A B Mid RA RB lm M K with hℓ
  have hlA : ∀ {e x y}, e ∈ A → G.IsLink e x y →
      ℓ e = M - max (dep G A RA x) (dep G A RA y) := by
    intro e x y he hl
    simp only [hℓ, genLabel, if_pos he, edgeMax_eq hl]
  have hlB : ∀ {e x y}, e ∈ B → G.IsLink e x y →
      ℓ e = M + K + 1 + max (dep G B RB x) (dep G B RB y) := by
    intro e x y he hl
    have : e ∉ A := fun h => Set.disjoint_left.1 hAB h he
    simp only [hℓ, genLabel, if_neg this, if_pos he, edgeMax_eq hl]
  have hlC : ∀ {e}, e ∈ Mid → ℓ e = M + lm e := by
    intro e he
    have h1 : e ∉ A := fun h => Set.disjoint_left.1 hAM h he
    have h2 : e ∉ B := fun h => Set.disjoint_left.1 hBM h he
    simp only [hℓ, genLabel, if_neg h1, if_neg h2, if_pos he]
  -- gathering
  have gather : ∀ n, ∀ x ∈ V(G), dep G A RA x = n → ∃ r ∈ RA, ∃ vs es, TW G ℓ x r vs es ∧
      ∀ f ∈ es, M - n ≤ ℓ f ∧ ℓ f < M := by
    intro n
    induction n with
    | zero =>
      intro x hx h0
      exact ⟨x, dep_zero (exists_within (hA x hx)) h0, [], [], .nil x, by simp⟩
    | succ n ih =>
      intro x hx hn
      obtain ⟨e, he, y, hl, hy⟩ := dep_succ (exists_within (hA x hx)) hn
      have hyV : y ∈ V(G) := hl.right_mem
      obtain ⟨r, hr, vs, es, hw, hf⟩ := ih y hyV hy
      have hnN : n ≤ N := hy ▸ (hN y hyV).1
      have hle : ℓ e = M - (n + 1) := by
        rw [hlA he hl, hn, hy]; congr 1; omega
      refine ⟨r, hr, x :: vs, e :: es, .cons hl hw ?_, ?_⟩
      · intro f hfm
        have := (hf f hfm).1
        omega
      · intro f hfm
        rcases List.mem_cons.1 hfm with rfl | hfm
        · omega
        · have := hf f hfm
          omega
  -- distributing
  have distribute : ∀ n, ∀ y ∈ V(G), dep G B RB y = n → ∃ r ∈ RB, ∃ vs es, TW G ℓ r y vs es ∧
      ∀ f ∈ es, M + K + 1 < ℓ f ∧ ℓ f ≤ M + K + 1 + n := by
    intro n
    induction n with
    | zero =>
      intro y hy h0
      have hB' : ∃ n, Within G B RB n y := by
        obtain ⟨r, hr, hry⟩ := hB y hy
        exact exists_within ⟨r, hr, rtg_symm (fun a b h => step_symm h) hry⟩
      exact ⟨y, dep_zero hB' h0, [], [], .nil y, by simp⟩
    | succ n ih =>
      intro y hy hn
      have hB' : ∃ n, Within G B RB n y := by
        obtain ⟨r, hr, hry⟩ := hB y hy
        exact exists_within ⟨r, hr, rtg_symm (fun a b h => step_symm h) hry⟩
      obtain ⟨e, he, z, hl, hz⟩ := dep_succ hB' hn
      have hzV : z ∈ V(G) := hl.right_mem
      obtain ⟨r, hr, vs, es, hw, hf⟩ := ih z hzV hz
      have hle : ℓ e = M + K + 1 + (n + 1) := by
        rw [hlB he hl, hn, hz]; congr 1; omega
      refine ⟨r, hr, vs ++ [z], es ++ [e], hw.append (TW.single hl.symm) ?_, ?_⟩
      · intro f hfm g hg
        simp only [List.mem_singleton] at hg
        subst hg
        have := (hf f hfm).2
        omega
      · intro f hfm
        rcases List.mem_append.1 hfm with hfm | hfm
        · have := hf f hfm
          omega
        · simp only [List.mem_singleton] at hfm
          subst hfm
          omega
  refine ⟨ℓ, fun x hx y hy => ?_⟩
  obtain ⟨r1, hr1, vs1, es1, hw1, hf1⟩ := gather _ x hx rfl
  obtain ⟨r2, hr2, vs2, es2, hw2, hf2⟩ := distribute _ y hy rfl
  obtain ⟨vs3, es3, hw3, hf3⟩ := hM r1 hr1 r2 hr2
  have hw3' : TW G ℓ r1 r2 vs3 es3 := tw_shift hw3 (M := M) (fun f hf => hlC (hf3 f hf).1)
  have h13 := hw1.append hw3' (fun f hf g hg => by
    have := (hf1 f hf).2
    have := hlC (hf3 g hg).1
    have := (hf3 g hg).2.1
    omega)
  exact (h13.append hw2 (fun f hf g hg => by
    have := (hf2 g hg).1
    rcases List.mem_append.1 hf with hf | hf
    · have := (hf1 f hf).2; omega
    · have := hlC (hf3 f hf).1
      have := (hf3 f hf).2.2
      omega)).hasTemporalPath

end Lax630294Proofs.MSufficiencySchedule
