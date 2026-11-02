import Lax630294Proofs.CallOrderMain
import Lax630294Proofs.Quotient2MLift

/-!
# Port selection (appendix, "Selecting Compatible Ports Using Original Routes"): graph toolkit

Generic multigraph facts used by the port selection:

* `Acyc H R`: every edge of `R` is a bridge of `(V(H), R)`.
* increasing trails `IncTrail`: splitting, pairwise comparability, closed trails in acyclic sets,
  staying inside a connected vertex set, exit through the unique crossing edge;
* paths `IsPathSet`: reversal, extraction from connectivity;
* breadth-first distances in an edge set.
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.SpanningStructures Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder

variable {α β γ : Type*}

/-! ### Acyclic edge sets -/

/-- Every edge of `R` is a bridge of the spanning subgraph `R`. -/
def Acyc (H : Graph γ β) (R : Set β) : Prop :=
  ∀ h ∈ R, ∀ a b, H.IsLink h a b → ¬ Reach H (R \ {h}) a b

section Acyc

variable {H : Graph γ β} {R R' : Set β}

lemma Acyc.mono (h : Acyc H R) (hs : R' ⊆ R) : Acyc H R' :=
  fun c hc a b hl hr => h c (hs hc) a b hl (reach_mono (Set.sdiff_subset_sdiff_left hs) hr)

lemma acyc_of_isForest (hF : IsForest H R) : Acyc H R :=
  fun _ hh _ _ hl => forest_bridge hF hh hl

/-- A connected edge set with `|A| - 1` edges on the vertex set `A` is acyclic. -/
lemma acyc_of_tree (hV : V(H).Finite) (hE : E(H).Finite) {A : Set γ} (hA : A ⊆ V(H))
    (hne : A.Nonempty) (hR : R ⊆ Ins H A) (hconn : ∀ x ∈ A, ∀ y ∈ A, Reach H R x y)
    (hcard : R.ncard + 1 = A.ncard) : Acyc H R := by
  intro h hh a b hl hr
  have hREfin : R.Finite := hE.subset (hR.trans ins_subset_edgeSet)
  have hconn' : ∀ x ∈ A, ∀ y ∈ A, Reach H (R \ {h}) x y := fun x hx y hy =>
    reach_remove_edge hl hr (hconn x hx y hy)
  have hsub : R \ {h} ⊆ Ins H A := Set.sdiff_subset.trans hR
  obtain ⟨hVf, hEf⟩ := finite_induce hV hE hA
  have h1 : comps (H.induce A) (R \ {h}) = 1 := by
    rw [comps_eq_one_iff hVf]
    refine ⟨hne, fun x hx y hy => ?_⟩
    exact (reach_induce_iff hsub).2 (hconn' x hx y hy)
  have h2 := (rank_ineq hVf (hREfin.subset Set.sdiff_subset) (F := R \ {h}) hsub).1
  rw [h1] at h2
  have h3 : (R \ {h}).ncard = R.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hh
  have h4 : 0 < R.ncard := Set.ncard_pos hREfin |>.2 ⟨h, hh⟩
  have h5 : V(H.induce A) = A := rfl
  rw [h5] at h2
  omega

end Acyc

/-! ### Increasing trails -/

section Trail

variable {H : Graph γ β} {P : β → β → Prop} {R : Set β} {u v w m : γ} {es es1 es2 : List β}

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.reach (h : IncTrail H P u v es) (hs : ∀ c ∈ es, c ∈ R) : Reach H R u v := by
  induction h with
  | nil => exact reach_refl
  | cons hl _ _ ih =>
    exact (reach_of_isLink (hs _ (by simp)) hl).trans' (ih fun c hc => hs c (by simp [hc]))

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.edge_mem (h : IncTrail H P u v es) :
    ∀ c ∈ es, c ∈ E(H) := by
  induction h with
  | nil => intro c hc; simp at hc
  | cons hl _ _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hl.edge_mem
    · exact ih c hc

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.split (h : IncTrail H P u v (es1 ++ es2)) :
    ∃ m, IncTrail H P u m es1 ∧ IncTrail H P m v es2 := by
  induction es1 generalizing u with
  | nil => exact ⟨u, IncTrail.nil u, by simpa using h⟩
  | cons e es1 ih =>
    rw [List.cons_append] at h
    cases h with
    | cons hl h2 hp =>
      obtain ⟨m, hm1, hm2⟩ := ih h2
      refine ⟨m, IncTrail.cons hl hm1 ?_, hm2⟩
      intro f hf
      apply hp
      cases es1 with
      | nil => simp at hf
      | cons g es1' => simpa using hf

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.pairwise (hP : ∀ a b c, P a b → P b c → P a c) (h : IncTrail H P u v es) :
    es.Pairwise P := by
  induction h with
  | nil => simp
  | @cons u w v e es hl h2 hp ih =>
    rw [List.pairwise_cons]
    refine ⟨fun g hg => ?_, ih⟩
    cases es with
    | nil => simp at hg
    | cons f es' =>
      rw [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hp _ rfl
      · exact hP _ _ _ (hp _ rfl) ((List.pairwise_cons.1 ih).1 g hg)

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.nodup (hP : ∀ a b c, P a b → P b c → P a c) (hirr : ∀ c, ¬ P c c)
    (h : IncTrail H P u v es) : es.Nodup :=
  (h.pairwise hP).imp (fun {a b} hab (heq : a = b) => by subst heq; exact hirr _ hab)

lemma _root_.Lax630294Proofs.CallOrder.IncTrail.mem_cons_inv {e : β} (h : IncTrail H P u v (e :: es)) :
    ∃ w, H.IsLink e u w ∧ IncTrail H P w v es ∧ (∀ f, es.head? = some f → P e f) := by
  cases h with
  | cons hl h2 hp => exact ⟨_, hl, h2, hp⟩

/-- A closed trail in an acyclic edge set is empty. -/
lemma closed_trail_nil (hR : Acyc H R) (htr : IncTrail H P u u es) (hs : ∀ c ∈ es, c ∈ R)
    (hnd : es.Nodup) : es = [] := by
  cases es with
  | nil => rfl
  | cons c es' =>
    obtain ⟨w, hl, h2, -⟩ := htr.mem_cons_inv
    exfalso
    have hc : c ∈ R := hs c (by simp)
    have hnc : c ∉ es' := (List.nodup_cons.1 hnd).1
    have : Reach H (R \ {c}) w u := h2.reach fun c' hc' =>
      ⟨hs c' (by simp [hc']), fun h => hnc (by rw [Set.mem_singleton_iff] at h; subst h; exact hc')⟩
    exact hR c hc u w hl this.symm'

/-- A trail with ends in a connected vertex set `S` of an acyclic edge set stays inside `S`. -/
lemma trail_stay (hR : Acyc H R) {S : Set γ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, Reach H (R ∩ Ins H S) x y)
    (htr : IncTrail H P u v es) (hs : ∀ c ∈ es, c ∈ R) (hnd : es.Nodup) (hu : u ∈ S)
    (hv : v ∈ S) : ∀ c ∈ es, c ∈ Ins H S := by
  revert hs hnd hu hv
  induction htr with
  | nil => intro _ _ _ _ c hc; simp at hc
  | @cons u w v e es hl h2 hp ih =>
    intro hs hnd hu hv
    have hw : w ∈ S := by
      by_contra hw
      have heI : e ∉ Ins H S := by
        rintro ⟨x, y, hxy, hx, hy⟩
        rcases hl.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hw hy
        · exact hw hx
      have heR : e ∈ R := hs e (by simp)
      have hne : e ∉ es := (List.nodup_cons.1 hnd).1
      have h3 : Reach H (R \ {e}) w v := h2.reach fun c' hc' =>
        ⟨hs c' (by simp [hc']), fun h => hne (by rw [Set.mem_singleton_iff] at h; subst h; exact hc')⟩
      have h4 : Reach H (R \ {e}) u v := reach_mono (fun c hc => ⟨hc.1, fun h => heI (by
        rw [Set.mem_singleton_iff] at h; subst h; exact hc.2)⟩) (hS u hu v hv)
      exact hR e heR u w hl (h4.trans' h3.symm')
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨u, w, hl, hu, hw⟩
    · exact ih (fun c' hc' => hs c' (by simp [hc'])) (List.nodup_cons.1 hnd).2 hw hv c hc

/-- Exit from a component of `E0 \ {k}` through the edge `k`. -/
lemma trail_exit {E0 : Set β} (hE0 : Acyc H E0) {k : β} {W' U : γ} (hk : H.IsLink k W' U)
    (hkE : k ∈ E0) {S' : Set γ} (hS' : ∀ x, x ∈ S' ↔ Reach H (E0 \ {k}) W' x)
    (htr : IncTrail H P u v es) (hs : ∀ c ∈ es, c ∈ E0) (hu : u ∈ S') (hv : v ∉ S') :
    ∃ es1 es2, es = es1 ++ k :: es2 ∧ IncTrail H P u W' es1 ∧ IncTrail H P U v es2 := by
  revert hs hu hv
  induction htr with
  | nil => intro _ _ hv; exact absurd ‹_› hv
  | @cons u w v e es hl h2 hp ih =>
    intro hs hu hv
    by_cases hw : w ∈ S'
    · obtain ⟨es1, es2, hes, h1, h1'⟩ := ih (fun c' hc' => hs c' (by simp [hc'])) hw hv
      refine ⟨e :: es1, es2, by simp [hes], IncTrail.cons hl h1 ?_, h1'⟩
      intro f hf
      apply hp
      rw [hes]
      cases es1 with
      | nil => simp at hf
      | cons g es1' => simpa using hf
    · have heE : e ∈ E0 := hs e (by simp)
      have hek : e = k := by
        by_contra hne
        apply hw
        rw [hS'] at hu ⊢
        exact hu.trans' (reach_of_isLink ⟨heE, hne⟩ hl)
      subst hek
      have hUn : U ∉ S' := by
        rw [hS']
        exact hE0 e heE W' U hk
      rcases hl.eq_and_eq_or_eq_and_eq hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨[], es, rfl, IncTrail.nil _, h2⟩
      · exact absurd hu hUn

end Trail

/-! ### Reach decomposition -/

section ReachLemmas

variable {H : Graph γ β} {R : Set β} {x y a b : γ} {c : β}

end ReachLemmas

/-! ### Paths -/

section Paths

variable {G : Graph α β}

lemma _root_.Lax630294Proofs.Quotient2Cycle.Chain.start_mem {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    a ∈ vs ++ [b] := by
  cases h <;> simp

lemma _root_.Lax630294Proofs.Quotient2Cycle.Chain.edge_ends {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    ∀ e ∈ es, ∀ x y, G.IsLink e x y → x ∈ vs ++ [b] ∧ y ∈ vs ++ [b] := by
  induction h with
  | nil => intro e he; simp at he
  | @cons a b0 c e0 vs es hl hc ih =>
    intro e he x y hxy
    rcases List.mem_cons.1 he with rfl | he
    · have hb0 : b0 ∈ vs ++ [c] := hc.start_mem
      rcases hl.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by simp, by simp at hb0 ⊢; tauto⟩
      · exact ⟨by simp at hb0 ⊢; tauto, by simp⟩
    · obtain ⟨h1, h2⟩ := ih e he x y hxy
      simp only [List.mem_append, List.mem_cons] at h1 h2 ⊢
      tauto

lemma _root_.Lax630294Proofs.Quotient2Cycle.Chain.suffix {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    ∀ (L1 L2 : List α) (x : α), vs = L1 ++ x :: L2 →
      ∃ es2, Chain G x (x :: L2) es2 b ∧ es2.Sublist es := by
  induction h with
  | nil => intro L1 L2 x hv; simp at hv
  | @cons a b0 c e vs es hl hc ih =>
    intro L1 L2 x hv
    cases L1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨e :: es, Chain.cons hl hc, List.Sublist.refl _⟩
    | cons y L1' =>
      simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨-, hv⟩ := hv
      obtain ⟨es2, h2, hs⟩ := ih L1' L2 x hv
      exact ⟨es2, h2, hs.cons e⟩

lemma _root_.Lax630294Proofs.Quotient2Cycle.Chain.reverse {a b : α} {vs : List α} {es : List β} (h : Chain G a vs es b) :
    ∃ vs' es', Chain G b vs' es' a ∧ vs' ++ [a] = (vs ++ [b]).reverse ∧ es' = es.reverse := by
  induction h with
  | nil a => exact ⟨[], [], Chain.nil a, by simp, rfl⟩
  | @cons a b0 c e vs es hl hc ih =>
    obtain ⟨vs', es', h', hv', he'⟩ := ih
    refine ⟨vs' ++ [b0], es' ++ [e], h'.append (Chain.single hl.symm), ?_, ?_⟩
    · simp [← hv']
    · simp [he']

lemma _root_.Lax630294Proofs.Quotient2Cycle.IsPathSet.symm {p q : α} {P : Set β} (h : IsPathSet G p q P) : IsPathSet G q p P := by
  obtain ⟨vs, es, hc, hvn, hen, hP⟩ := h
  obtain ⟨vs', es', hc', hv', he'⟩ := hc.reverse
  refine ⟨vs', es', hc', ?_, ?_, ?_⟩
  · rw [hv']
    exact List.nodup_reverse.2 hvn
  · rw [he']
    exact List.nodup_reverse.2 hen
  · rw [← hP, he']
    ext e
    simp

lemma isPathSet_refl (p : α) : IsPathSet G p p (∅ : Set β) :=
  ⟨[], [], Chain.nil p, by simp, by simp, by simp⟩

/-- Connectivity yields a path inside the edge set. -/
lemma exists_isPathSet_of_reach {R : Set β} {p q : α} (h : Reach G R p q) :
    ∃ P ⊆ R, IsPathSet G p q P := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨∅, Set.empty_subset _, isPathSet_refl q⟩
  | @head p p1 hs hr ih =>
    obtain ⟨c, hc, hl⟩ := hs
    obtain ⟨P, hPR, vs, es, hch, hvn, hen, hP⟩ := ih
    by_cases hp : p ∈ vs ++ [q]
    · rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨L1, L2, hL⟩ := List.append_of_mem hp
        obtain ⟨es2, hch2, hsub⟩ := hch.suffix L1 L2 p hL
        refine ⟨{e | e ∈ es2}, ?_, ?_⟩
        · intro e he
          exact hPR (hP ▸ show e ∈ es from hsub.subset he)
        · refine ⟨p :: L2, es2, hch2, ?_, hen.sublist hsub, rfl⟩
          have : List.Sublist ((p :: L2) ++ [q]) (vs ++ [q]) := by
            rw [hL]
            simp only [List.cons_append, List.append_assoc]
            exact (List.sublist_append_right L1 _)
          exact hvn.sublist this
      · simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨∅, Set.empty_subset _, isPathSet_refl p⟩
    · refine ⟨insert c P, Set.insert_subset hc hPR, p :: vs, c :: es, Chain.cons hl hch, ?_, ?_, ?_⟩
      · exact List.nodup_cons.2 ⟨by simpa using hp, hvn⟩
      · refine List.nodup_cons.2 ⟨fun hce => ?_, hen⟩
        have := hch.edge_ends c hce p p1 hl
        exact hp this.1
      · ext e
        simp [← hP]

end Paths

/-! ### Breadth-first distances -/

section BFS

open Classical in
/-- `WN G D v n x`: `x` is reached from `v` by a walk with exactly `n` steps in `D`. -/
def WN (G : Graph α β) (D : Set β) (v : α) : ℕ → α → Prop
  | 0, x => x = v
  | n + 1, x => ∃ y c, WN G D v n y ∧ c ∈ D ∧ G.IsLink c y x

variable {G : Graph α β} {D : Set β} {v : α}

lemma reach_iff_wn {x : α} : Reach G D v x ↔ ∃ n, WN G D v n x := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hs ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨c, hc, hl⟩ := hs
      exact ⟨n + 1, _, c, hn, hc, hl⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero => have hx : x = v := hn; subst hx; exact reach_refl
    | succ n ih =>
      obtain ⟨y, c, hy, hc, hl⟩ := hn
      exact (ih hy).tail ⟨c, hc, hl⟩

open Classical in
/-- Distance from `v` (zero for unreachable vertices). -/
noncomputable def dist (G : Graph α β) (D : Set β) (v : α) (x : α) : ℕ :=
  if h : ∃ n, WN G D v n x then Nat.find h else 0

lemma dist_spec {x : α} (h : Reach G D v x) : WN G D v (dist G D v x) x := by
  classical
  have h' := reach_iff_wn.1 h
  unfold dist
  rw [dif_pos h']
  exact Nat.find_spec h'

lemma dist_le {x : α} {n : ℕ} (h : WN G D v n x) : dist G D v x ≤ n := by
  classical
  unfold dist
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

lemma dist_eq_zero {x : α} (h : Reach G D v x) (h0 : dist G D v x = 0) : x = v := by
  have := dist_spec h
  rw [h0] at this
  exact this

lemma dist_succ_le {x y : α} {c : β} (h : Reach G D v y) (hc : c ∈ D) (hl : G.IsLink c y x) :
    dist G D v x ≤ dist G D v y + 1 :=
  dist_le ⟨y, c, dist_spec h, hc, hl⟩

/-- Every reachable vertex other than `v` has a parent one step closer. -/
lemma exists_parent {x : α} (h : Reach G D v x) (hx : x ≠ v) :
    ∃ y c, Reach G D v y ∧ c ∈ D ∧ G.IsLink c y x ∧ dist G D v y + 1 = dist G D v x := by
  have hd : dist G D v x ≠ 0 := fun h0 => hx (dist_eq_zero h h0)
  obtain ⟨n, hn⟩ : ∃ n, dist G D v x = n + 1 := ⟨dist G D v x - 1, by omega⟩
  have hs := dist_spec h
  rw [hn] at hs
  obtain ⟨y, c, hy, hc, hl⟩ := hs
  have hry : Reach G D v y := reach_iff_wn.2 ⟨n, hy⟩
  have h1 : dist G D v y ≤ n := dist_le hy
  have h2 := dist_succ_le hry hc hl
  exact ⟨y, c, hry, hc, hl, by omega⟩

end BFS

end Lax630294Proofs.Ports
