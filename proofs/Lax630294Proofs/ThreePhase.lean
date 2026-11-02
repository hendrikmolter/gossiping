import Lax630294Proofs.Temporal
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lattice

namespace Lax630294Proofs.ThreePhase

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal

variable {α β : Type*} {G : Graph α β}

/-- Two vertices joined by an edge of `F`. -/
def step (G : Graph α β) (F : Set β) (x y : α) : Prop := ∃ e ∈ F, G.IsLink e x y

lemma step_symm {F : Set β} {x y : α} (h : step G F x y) : step G F y x := by
  obtain ⟨e, he, hl⟩ := h
  exact ⟨e, he, hl.symm⟩

/-- `x` reaches `R` along `n` edges of `F`. -/
def Within (G : Graph α β) (F : Set β) (R : Set α) : ℕ → α → Prop
  | 0, x => x ∈ R
  | n + 1, x => ∃ e ∈ F, ∃ y, G.IsLink e x y ∧ Within G F R n y

lemma rtg_symm {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hs _ _ hbc) ih

lemma exists_within {F : Set β} {R : Set α} {x : α}
    (h : ∃ r ∈ R, Relation.ReflTransGen (step G F) x r) : ∃ n, Within G F R n x := by
  obtain ⟨r, hr, hxr⟩ := h
  induction hxr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, hr⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨e, he, hl⟩ := hab
    exact ⟨n + 1, e, he, _, hl, hn⟩

open Classical in
/-- Distance of `x` to `R` along edges of `F` (and `0` if `R` is not reachable). -/
noncomputable def dep (G : Graph α β) (F : Set β) (R : Set α) (x : α) : ℕ :=
  if h : ∃ n, Within G F R n x then Nat.find h else 0

lemma within_dep {F : Set β} {R : Set α} {x : α} (h : ∃ n, Within G F R n x) :
    Within G F R (dep G F R x) x := by
  classical
  simp only [dep, dif_pos h]
  exact Nat.find_spec h

lemma dep_le {F : Set β} {R : Set α} {x : α} {n : ℕ} (h : Within G F R n x) :
    dep G F R x ≤ n := by
  classical
  have h' : ∃ n, Within G F R n x := ⟨n, h⟩
  simp only [dep, dif_pos h']
  exact Nat.find_min' h' h

lemma dep_zero {F : Set β} {R : Set α} {x : α} (hx : ∃ n, Within G F R n x)
    (h0 : dep G F R x = 0) : x ∈ R := by
  have := within_dep hx
  rw [h0] at this
  exact this

lemma dep_succ {F : Set β} {R : Set α} {x : α} {n : ℕ} (hx : ∃ n, Within G F R n x)
    (hn : dep G F R x = n + 1) :
    ∃ e ∈ F, ∃ y, G.IsLink e x y ∧ dep G F R y = n := by
  have h := within_dep hx
  rw [hn] at h
  obtain ⟨e, he, y, hl, hy⟩ := h
  refine ⟨e, he, y, hl, le_antisymm (dep_le hy) ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hy' := within_dep (⟨n, hy⟩ : ∃ n, Within G F R n y)
  have : Within G F R (dep G F R y + 1) x := ⟨e, he, y, hl, hy'⟩
  have := dep_le this
  omega

open Classical in
/-- The larger value of `f` at the ends of the edge `e`. -/
noncomputable def edgeMax (G : Graph α β) (f : α → ℕ) (e : β) : ℕ :=
  if h : ∃ x y, G.IsLink e x y then max (f h.choose) (f h.choose_spec.choose) else 0

lemma edgeMax_eq {f : α → ℕ} {e : β} {x y : α} (h : G.IsLink e x y) :
    edgeMax G f e = max (f x) (f y) := by
  have hex : ∃ x y, G.IsLink e x y := ⟨x, y, h⟩
  simp only [edgeMax, dif_pos hex]
  have h2 := hex.choose_spec.choose_spec
  rcases (h.isLink_iff.1 h2) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact max_comm _ _

open Classical in
/-- The labeling used in the three-phase construction: gathering edges `A` get small labels,
the hub edges `C` get label `M`, and distributing edges `B` get large labels. -/
noncomputable def phaseLabel (G : Graph α β) (A B C : Set β) (R : Set α) (M : ℕ) (e : β) : ℕ :=
  if e ∈ A then M - edgeMax G (dep G A R) e
  else if e ∈ B then M + 1 + edgeMax G (dep G B R) e
  else if e ∈ C then M else 0

/-- Three-phase scheme: information is gathered at roots along `A`, exchanged between roots
along hub edges `C`, and distributed along `B`. -/
theorem three_phase (hV : V(G).Finite) (A B C : Set β) (R : Set α)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hA : ∀ x ∈ V(G), ∃ r ∈ R, Relation.ReflTransGen (step G A) x r)
    (hB : ∀ y ∈ V(G), ∃ r ∈ R, Relation.ReflTransGen (step G B) r y)
    (hC : ∀ r ∈ R, ∀ r' ∈ R, r = r' ∨ ∃ c ∈ C, G.IsLink c r r') :
    IsLabelConnected G := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, ∀ x ∈ V(G), dep G A R x ≤ N ∧ dep G B R x ≤ N := by
    obtain ⟨N, hN⟩ := Set.Finite.bddAbove (hV.image fun x => max (dep G A R x) (dep G B R x))
    refine ⟨N, fun x hx => ?_⟩
    have := hN ⟨x, hx, rfl⟩
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  set M := N + 1 with hM
  set ℓ := phaseLabel G A B C R M with hℓ
  have hlA : ∀ {e x y}, e ∈ A → G.IsLink e x y →
      ℓ e = M - max (dep G A R x) (dep G A R y) := by
    intro e x y he hl
    simp only [hℓ, phaseLabel, if_pos he, edgeMax_eq hl]
  have hlB : ∀ {e x y}, e ∈ B → G.IsLink e x y →
      ℓ e = M + 1 + max (dep G B R x) (dep G B R y) := by
    intro e x y he hl
    have : e ∉ A := fun h => Set.disjoint_left.1 hAB h he
    simp only [hℓ, phaseLabel, if_neg this, if_pos he, edgeMax_eq hl]
  have hlC : ∀ {e}, e ∈ C → ℓ e = M := by
    intro e he
    have h1 : e ∉ A := fun h => Set.disjoint_left.1 hAC h he
    have h2 : e ∉ B := fun h => Set.disjoint_left.1 hBC h he
    simp only [hℓ, phaseLabel, if_neg h1, if_neg h2, if_pos he]
  -- gathering
  have gather : ∀ n, ∀ x ∈ V(G), dep G A R x = n → ∃ r ∈ R, ∃ vs es, TW G ℓ x r vs es ∧
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
  have distribute : ∀ n, ∀ y ∈ V(G), dep G B R y = n → ∃ r ∈ R, ∃ vs es, TW G ℓ r y vs es ∧
      ∀ f ∈ es, M + 1 < ℓ f ∧ ℓ f ≤ M + 1 + n := by
    intro n
    induction n with
    | zero =>
      intro y hy h0
      have hB' : ∃ n, Within G B R n y := by
        obtain ⟨r, hr, hry⟩ := hB y hy
        exact exists_within ⟨r, hr, by
          have : Relation.ReflTransGen (step G B) y r :=
            rtg_symm (fun a b h => step_symm h) hry
          exact this⟩
      exact ⟨y, dep_zero hB' h0, [], [], .nil y, by simp⟩
    | succ n ih =>
      intro y hy hn
      have hB' : ∃ n, Within G B R n y := by
        obtain ⟨r, hr, hry⟩ := hB y hy
        exact exists_within ⟨r, hr,
          rtg_symm (fun a b h => step_symm h) hry⟩
      obtain ⟨e, he, z, hl, hz⟩ := dep_succ hB' hn
      have hzV : z ∈ V(G) := hl.right_mem
      obtain ⟨r, hr, vs, es, hw, hf⟩ := ih z hzV hz
      have hle : ℓ e = M + 1 + (n + 1) := by
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
  rcases hC r1 hr1 r2 hr2 with rfl | ⟨c, hc, hl⟩
  · exact (hw1.append hw2 (fun f hf g hg => by
      have := (hf1 f hf).2; have := (hf2 g hg).1; omega)).hasTemporalPath
  · have hlc := hlC hc
    have h12 := hw1.append (TW.single hl) (fun f hf g hg => by
      simp only [List.mem_singleton] at hg; subst hg
      have := (hf1 f hf).2; omega)
    exact (h12.append hw2 (fun f hf g hg => by
      have := (hf2 g hg).1
      rcases List.mem_append.1 hf with hf | hf
      · have := (hf1 f hf).2; omega
      · simp only [List.mem_singleton] at hf; subst hf; omega)).hasTemporalPath

end Lax630294Proofs.ThreePhase
