import Lax630294.Gossiping
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

namespace Lax630294Proofs.Temporal

open Graph Lax630294.Gossiping

variable {α β : Type*}

/-- A temporal walk from `u` to `v` with respect to the labeling `ℓ`: `vs` lists the vertices
visited, except the final one, and `es` the traversed edges; labels strictly increase. -/
inductive TW (G : Graph α β) (ℓ : β → ℕ) : α → α → List α → List β → Prop
  | nil (u : α) : TW G ℓ u u [] []
  | cons {u w v : α} {e : β} {vs : List α} {es : List β} :
      G.IsLink e u w → TW G ℓ w v vs es → (∀ f ∈ es, ℓ e < ℓ f) →
      TW G ℓ u v (u :: vs) (e :: es)

variable {G : Graph α β} {ℓ : β → ℕ}

lemma TW.single {u v : α} {e : β} (h : G.IsLink e u v) : TW G ℓ u v [u] [e] :=
  .cons h (.nil v) (by simp)

lemma TW.length_eq {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es) :
    vs.length = es.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- Concatenation of temporal walks whose labels fit. -/
lemma TW.append {u w v : α} {vs vs' : List α} {es es' : List β}
    (h : TW G ℓ u w vs es) (h' : TW G ℓ w v vs' es')
    (hl : ∀ f ∈ es, ∀ g ∈ es', ℓ f < ℓ g) : TW G ℓ u v (vs ++ vs') (es ++ es') := by
  induction h with
  | nil => simpa using h'
  | cons hl1 hw hlab ih =>
    rename_i u z w' e vs es
    refine .cons hl1 (ih h' (fun f hf g hg => hl f (by simp [hf]) g hg)) ?_
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact hlab f hf
    · exact hl e (by simp) f hf

lemma TW.getElem_zero {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es)
    (h0 : 0 < (vs ++ [v]).length) : (vs ++ [v])[0] = u := by
  cases h <;> simp

lemma TW.labels_pairwise {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es) :
    es.Pairwise (fun a b => ℓ a < ℓ b) := by
  induction h with
  | nil => simp
  | cons _ _ hlab ih => exact List.pairwise_cons.2 ⟨hlab, ih⟩

/-- A vertex visited by a walk starts a suffix walk with a sublist of the edges. -/
lemma TW.suffix {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es)
    {x : α} (hx : x ∈ vs ++ [v]) :
    ∃ vs₂ es₂, TW G ℓ x v vs₂ es₂ ∧ es₂.Sublist es ∧ (vs₂ ++ [v]).IsSuffix (vs ++ [v]) := by
  induction h with
  | nil =>
    simp at hx; subst hx
    exact ⟨[], [], .nil _, List.Sublist.refl _, List.suffix_refl _⟩
  | cons hl hw hlab ih =>
    rename_i u z w' e vs es
    by_cases hxu : x = u
    · subst hxu
      exact ⟨_, _, .cons hl hw hlab, List.Sublist.refl _, List.suffix_refl _⟩
    · have hx' : x ∈ vs ++ [w'] := by
        simpa [hxu] using hx
      obtain ⟨vs₂, es₂, h2, hs, hsuf⟩ := ih hx'
      exact ⟨vs₂, es₂, h2, hs.cons _, hsuf.trans (by simp)⟩

/-- Every temporal walk contains a temporal walk without repeated vertices. -/
lemma TW.erase {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es) :
    ∃ vs' es', TW G ℓ u v vs' es' ∧ (vs' ++ [v]).Nodup ∧ es'.Sublist es := by
  induction h with
  | nil => exact ⟨[], [], .nil _, by simp, List.Sublist.refl _⟩
  | cons hl hw hlab ih =>
    rename_i u z w' e vs es
    obtain ⟨vs', es', h', hnd, hsub⟩ := ih
    by_cases hu : u ∈ vs' ++ [w']
    · obtain ⟨vs₂, es₂, h2, hs, hsuf⟩ := h'.suffix hu
      exact ⟨vs₂, es₂, h2, hnd.sublist hsuf.sublist, (hs.trans hsub).trans (by simp)⟩
    · refine ⟨u :: vs', e :: es', .cons hl h' (fun f hf => hlab f (hsub.subset hf)), ?_,
        hsub.cons_cons e⟩
      rw [List.cons_append, List.nodup_cons]; exact ⟨hu, hnd⟩

/-- A temporal walk with pairwise distinct vertices is a temporal path. -/
lemma TW.toPath {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es)
    (hnd : (vs ++ [v]).Nodup) : HasTemporalPath G ℓ u v := by
  have hlen : (vs ++ [v]).length = es.length + 1 := by simp [h.length_eq]
  have hlinks : ∀ i (hi : i < es.length),
      G.IsLink es[i] ((vs ++ [v])[i]'(by omega)) ((vs ++ [v])[i + 1]'(by omega)) := by
    induction h with
    | nil => intro i hi; simp at hi
    | cons hl hw hlab ih =>
      rename_i u z w' e vs es
      intro i hi
      cases i with
      | zero =>
        have := hw.getElem_zero (by simp)
        simpa [this] using hl
      | succ i =>
        have hnd' : (vs ++ [w']).Nodup := by
          simp only [List.cons_append, List.nodup_cons] at hnd; exact hnd.2
        simpa using ih hnd' (by simp [hw.length_eq]) i (by simpa using hi)
  refine ⟨es.length, fun i => (vs ++ [v]).get ⟨i, by omega⟩, fun i => es.get i, ?_, ?_, ?_, ?_, ?_⟩
  · cases h with
    | nil => rfl
    | cons => rfl
  · simp [List.getElem_append_right, h.length_eq]
  · intro a b hab
    have := (List.nodup_iff_injective_get.1 hnd) hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro i
    simpa using hlinks i i.2
  · intro i j hij
    exact List.pairwise_iff_get.1 h.labels_pairwise i j hij

lemma TW.hasTemporalPath {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es) :
    HasTemporalPath G ℓ u v := by
  obtain ⟨vs', es', h', hnd, -⟩ := h.erase
  exact h'.toPath hnd

end Lax630294Proofs.Temporal
