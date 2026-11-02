import Lax630294Proofs.Temporal
import Mathlib.Data.List.FinRange

/-!
# Causal order of a labeled graph

For a labeling `ℓ` of `G`, the causal order `causal G ℓ` is the transitive closure of
"`a`, `b` share an endpoint and `ℓ a < ℓ b`".  Every linear extension of it keeps `G`
temporally connected.  `PW G R` is a walk whose edge list is `R`-increasing (every edge is
`R`-below all later ones); `TW G ℓ` is the special case `R = (ℓ · < ℓ ·)`.
-/

namespace Lax630294Proofs.Causal

open Graph Lax630294.Gossiping Lax630294Proofs.Temporal

variable {α β : Type*}

/-- Generating relation of the causal order: two calls sharing an endpoint, in label order. -/
def CStep (G : Graph α β) (ℓ : β → ℕ) (a b : β) : Prop :=
  (∃ x, G.Inc a x ∧ G.Inc b x) ∧ ℓ a < ℓ b

/-- The causal order `P_G` of the labeled graph `(G, ℓ)`. -/
def causal (G : Graph α β) (ℓ : β → ℕ) : β → β → Prop := Relation.TransGen (CStep G ℓ)

section causal

variable {G : Graph α β} {ℓ : β → ℕ}

lemma causal_lt {a b : β} (h : causal G ℓ a b) : ℓ a < ℓ b := by
  induction h with
  | single h => exact h.2
  | tail _ h ih => exact ih.trans h.2

lemma causal_irrefl (e : β) : ¬ causal G ℓ e e := fun h => lt_irrefl _ (causal_lt h)

lemma causal_trans {a b c : β} (h : causal G ℓ a b) (h' : causal G ℓ b c) : causal G ℓ a c :=
  Relation.TransGen.trans h h'

end causal

/-- A walk from `u` to `v` whose edges (listed in order) are `R`-increasing: each edge is
`R`-below all later edges of the list. -/
inductive PW (G : Graph α β) (R : β → β → Prop) : α → α → List α → List β → Prop
  | nil (u : α) : PW G R u u [] []
  | cons {u w v : α} {e : β} {vs : List α} {es : List β} :
      G.IsLink e u w → PW G R w v vs es → (∀ f ∈ es, R e f) → PW G R u v (u :: vs) (e :: es)

namespace PW

variable {G : Graph α β} {R R' : β → β → Prop}

lemma edge_mem {u v : α} {vs : List α} {es : List β} (h : PW G R u v vs es) :
    ∀ f ∈ es, f ∈ E(G) := by
  induction h with
  | nil => simp
  | cons hl _ _ ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hl.edge_mem
    · exact ih f hf

/-- An `R`-increasing walk is a temporal walk for every labeling respecting `R`. -/
lemma toTW {ℓ' : β → ℕ} (hR : ∀ a b, R a b → ℓ' a < ℓ' b) {u v : α} {vs : List α}
    {es : List β} (h : PW G R u v vs es) : TW G ℓ' u v vs es := by
  induction h with
  | nil => exact .nil _
  | cons hl _ hf ih => exact .cons hl ih (fun f hf' => hR _ _ (hf f hf'))

/-- Converse helper: an `R`-increasing walk yields a strict temporal path for every labeling
respecting `R`. -/
lemma hasTemporalPath {ℓ' : β → ℕ} (hR : ∀ a b, R a b → ℓ' a < ℓ' b) {u v : α}
    {vs : List α} {es : List β} (h : PW G R u v vs es) : HasTemporalPath G ℓ' u v :=
  (h.toTW hR).hasTemporalPath

end PW

variable {G : Graph α β} {ℓ : β → ℕ}

private lemma _root_.Lax630294Proofs.Temporal.TW.causal_head {w v : α} {vs : List α} {es : List β} (h : TW G ℓ w v vs es)
    {e : β} (he : G.Inc e w) (hl : ∀ f ∈ es, ℓ e < ℓ f) : ∀ f ∈ es, causal G ℓ e f := by
  induction h generalizing e with
  | nil => simp
  | @cons u w' v e0 vs es hl0 hw hlab ih =>
    intro f hf
    have h0 : causal G ℓ e e0 :=
      Relation.TransGen.single ⟨⟨u, he, hl0.inc_left⟩, hl e0 (by simp)⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · exact h0
    · exact causal_trans h0 (ih hl0.inc_right hlab f hf)

/-- A strict temporal walk is `causal`-increasing: its chain of calls is a causal chain. -/
lemma _root_.Lax630294Proofs.Temporal.TW.toPW {u v : α} {vs : List α} {es : List β} (h : TW G ℓ u v vs es) :
    PW G (causal G ℓ) u v vs es := by
  induction h with
  | nil => exact .nil _
  | cons hl hw hlab ih => exact .cons hl ih (TW.causal_head hw hl.inc_right hlab)

/-- Walks from the data of a path: used to turn `HasTemporalPath` into `TW`. -/
private lemma tw_ofFn : ∀ (k : ℕ) (x : Fin (k + 1) → α) (e : Fin k → β),
    (∀ i : Fin k, G.IsLink (e i) (x i.castSucc) (x i.succ)) → StrictMono (fun i => ℓ (e i)) →
    TW G ℓ (x 0) (x (Fin.last k)) (List.ofFn (fun i : Fin k => x i.castSucc)) (List.ofFn e) := by
  intro k
  induction k with
  | zero =>
    intro x e _ _
    simp only [List.ofFn_zero]
    exact TW.nil (x 0)
  | succ k ih =>
    intro x e hl hm
    rw [List.ofFn_succ, List.ofFn_succ]
    have h1 := ih (fun i => x i.succ) (fun i => e i.succ)
      (fun i => by have h := hl i.succ; rw [← Fin.succ_castSucc] at h; exact h)
      (fun i j hij => hm (Fin.succ_lt_succ_iff.2 hij))
    refine TW.cons (w := x (Fin.succ 0)) ?_ ?_ ?_
    · simpa using hl 0
    · simpa [Fin.succ_last] using h1
    · intro f hf
      obtain ⟨i, hi⟩ := List.mem_ofFn.1 hf
      subst hi
      exact hm (Fin.succ_pos i)

/-- A strict temporal path is a temporal walk without repeated vertices. -/
lemma exists_TW_of_hasTemporalPath {u v : α} (h : HasTemporalPath G ℓ u v) :
    ∃ vs es, TW G ℓ u v vs es ∧ (vs ++ [v]).Nodup := by
  obtain ⟨k, x, e, h0, hk, hinj, hl, hm⟩ := h
  refine ⟨_, _, h0 ▸ hk ▸ tw_ofFn k x e hl hm, ?_⟩
  have : List.ofFn (fun i : Fin k => x i.castSucc) ++ [x (Fin.last k)] = List.ofFn x := by
    exact List.ofFn_succ_last.symm
  rw [← hk, this, List.ofFn_eq_map]
  exact (List.nodup_finRange _).map hinj

/-- A route between two original vertices that is `causal`-increasing (every call is causally
below every later call), temporal for `ℓ`, and without repeated vertices. -/
theorem exists_route (hℓ : IsTemporallyConnected G ℓ) {u v : α} (hu : u ∈ V(G))
    (hv : v ∈ V(G)) :
    ∃ vs es, TW G ℓ u v vs es ∧ (vs ++ [v]).Nodup ∧ es.Nodup ∧ PW G (causal G ℓ) u v vs es := by
  obtain ⟨vs, es, h, hnd⟩ := exists_TW_of_hasTemporalPath (hℓ u hu v hv)
  refine ⟨vs, es, h, hnd, ?_, h.toPW⟩
  exact List.Pairwise.imp (fun {a b} hab (heq : a = b) => by subst heq; exact lt_irrefl _ hab)
    h.labels_pairwise

/-- A *linear extension* of the causal order: injective on `E(G)`, respects `causal G ℓ`. -/
def IsLinExt (G : Graph α β) (ℓ ℓ' : β → ℕ) : Prop :=
  Set.InjOn ℓ' E(G) ∧ ∀ a b, causal G ℓ a b → ℓ' a < ℓ' b

end Lax630294Proofs.Causal
