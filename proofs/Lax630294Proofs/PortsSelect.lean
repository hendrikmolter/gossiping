import Lax630294Proofs.PortsGraph

/-!
# Static selection and antichain selection
(`lem:characterization-static-selection`, `lem:characterization-antichain-selection`)

DEVIATION: the paper proves the static selection lemma by pruning a minimal Steiner tree of
`D` (deepest nonleaf vertex, pendant paths).  Here the pruning is replaced by a breadth-first
distance argument: among the edges of `D` joining two different components of `A` (reachable from
`v`), take one maximising the distance of its nearer end; then every terminal outside the component
of its far end stays connected to `v` in `D` minus that edge (`static_step`).  The induction on the
number of specified vertices is the paper's (add the edge to `A`, drop one specified vertex).
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.SpanningStructures Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder

variable {α β : Type*} {G : Graph α β}

/-- One pruning step of the static selection lemma. -/
lemma static_step {B : Set α} (hB : B.Finite) {A D : Set β} (hDB : D ⊆ Ins G B) {v : α}
    (hvB : v ∈ B) {Tm : Set α} (hTm : ∀ t ∈ Tm, Reach G D v t)
    (hpair : ∀ t ∈ Tm, ∀ t' ∈ Tm, Reach G A t t' → t = t')
    (h2 : ∃ t ∈ Tm, ∃ t' ∈ Tm, t ≠ t') :
    ∃ h ∈ D, ∃ a b, G.IsLink h a b ∧ ¬ Reach G A a b ∧
      ∀ t ∈ Tm, ¬ Reach G A t b → Reach G (D \ {h}) v t := by
  classical
  let Ent : Set (α × α) := {p | p.1 ∈ B ∧ p.2 ∈ B ∧ Reach G D v p.1 ∧ ¬ Reach G A p.1 p.2 ∧
    ∃ h ∈ D, G.IsLink h p.1 p.2}
  have hEntfin : Ent.Finite := (hB.prod hB).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  have hne : Ent.Nonempty := by
    by_contra hne
    have key : ∀ x, Reach G D v x → Reach G A v x := by
      intro x hx
      induction hx with
      | refl => exact reach_refl
      | @tail y z hr hs ih =>
        obtain ⟨c, hc, hl⟩ := hs
        have hyB : y ∈ B := (ins_of_link (hDB hc) hl).1
        have hzB : z ∈ B := (ins_of_link (hDB hc) hl).2
        by_cases hyz : Reach G A y z
        · exact ih.trans' hyz
        · exact absurd ⟨(y, z), hyB, hzB, hr, hyz, c, hc, hl⟩ hne
    obtain ⟨t, ht, t', ht', htt'⟩ := h2
    exact htt' (hpair t ht t' ht' ((key t (hTm t ht)).symm'.trans' (key t' (hTm t' ht'))))
  obtain ⟨p, hp, hm⟩ := Set.exists_max_image Ent (fun p => min (dist G D v p.1) (dist G D v p.2)) hEntfin hne
  obtain ⟨a, b, hent, hle, hmax⟩ : ∃ a b, (a, b) ∈ Ent ∧ dist G D v a ≤ dist G D v b ∧
      ∀ q ∈ Ent, min (dist G D v q.1) (dist G D v q.2) ≤ dist G D v a := by
    obtain ⟨a, b⟩ := p
    rcases le_total (dist G D v a) (dist G D v b) with h | h
    · refine ⟨a, b, hp, h, fun q hq => (hm q hq).trans ?_⟩
      simp [min_eq_left h]
    · obtain ⟨haB, hbB, hra, hnab, c, hc, hl⟩ := hp
      have hrb : Reach G D v b := hra.trans' (reach_of_isLink hc hl)
      refine ⟨b, a, ⟨hbB, haB, hrb, fun hh => hnab hh.symm', c, hc, hl.symm⟩, h, fun q hq => ?_⟩
      refine (hm q hq).trans ?_
      simp [min_eq_right h]
  obtain ⟨haB, hbB, hra, hnab, h, hhD, hl⟩ := hent
  simp only at haB hbB hra hnab hl
  have hC : ∀ n : ℕ, ∀ x, Reach G D v x → dist G D v x = n →
      (Reach G (D \ {h}) v x ∨ (Reach G A x b ∧ dist G D v b ≤ dist G D v x ∧ dist G D v a + 1 = dist G D v b)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      by_cases hxv : x = v
      · subst hxv; exact Or.inl reach_refl
      obtain ⟨y, c, hry, hc, hcl, hyd⟩ := exists_parent hx hxv
      have hyB : y ∈ B := (ins_of_link (hDB hc) hcl).1
      have hxB : x ∈ B := (ins_of_link (hDB hc) hcl).2
      rcases ih (dist G D v y) (by omega) y hry rfl with hleft | ⟨hyb, hby, hab⟩
      · by_cases hch : c = h
        · subst hch
          rcases hl.eq_and_eq_or_eq_and_eq hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨reach_refl, le_rfl, by omega⟩
          · omega
        · exact Or.inl (hleft.tail ⟨c, ⟨hc, hch⟩, hcl⟩)
      · by_cases hyx : Reach G A y x
        · exact Or.inr ⟨hyx.symm'.trans' hyb, by omega, hab⟩
        · exfalso
          have := hmax (y, x) ⟨hyB, hxB, hry, hyx, c, hc, hcl⟩
          simp only at this
          omega
  refine ⟨h, hhD, a, b, hl, hnab, fun t ht htb => ?_⟩
  rcases hC _ t (hTm t ht) rfl with h1 | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 htb

/-- **Static selection** (`lem:characterization-static-selection`).  `Jset` is the edge set of the
graph `J` on the finite vertex set `B`; `A, D ⊆ Jset` are disjoint; every vertex of `B` is
`A`-connected to a vertex of `Tm`, and `D` connects `v` to every vertex of `Tm`.  Then some
`v`-`t` path `P` of `D` (`t ∈ Tm`) can be deleted from `J` leaving it connected. -/
theorem static_selection {B : Set α} (hB : B.Finite) {Jset : Set β} (hJB : Jset ⊆ Ins G B)
    {v : α} (hvB : v ∈ B) :
    ∀ (n : ℕ) (A D : Set β) (Tm : Set α), Tm.ncard = n → A ⊆ Jset → D ⊆ Jset → Disjoint A D →
      Tm ⊆ B → (∀ x ∈ B, ∃ t ∈ Tm, Reach G A x t) → (∀ t ∈ Tm, Reach G D v t) →
      ∃ t ∈ Tm, ∃ P ⊆ D, IsPathSet G v t P ∧ ∀ x ∈ B, ∀ y ∈ B, Reach G (Jset \ P) x y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A D Tm hn hAJ hDJ hAD hTmB hcov hTm
    have hTmfin : Tm.Finite := hB.subset hTmB
    by_cases hdup : ∃ t ∈ Tm, ∃ t' ∈ Tm, t ≠ t' ∧ Reach G A t t'
    · obtain ⟨t, ht, t', ht', htt', hr⟩ := hdup
      have hlt : (Tm \ {t'}).ncard < n := by
        rw [← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem ht' hTmfin
      obtain ⟨s, hs, P, hP, hpath, hcon⟩ := ih _ hlt A D (Tm \ {t'}) rfl hAJ hDJ hAD
        (Set.sdiff_subset.trans hTmB)
        (fun x hx => by
          obtain ⟨s0, hs0, hr0⟩ := hcov x hx
          by_cases h0 : s0 = t'
          · subst h0
            exact ⟨t, ⟨ht, htt'⟩, hr0.trans' hr.symm'⟩
          · exact ⟨s0, ⟨hs0, h0⟩, hr0⟩)
        (fun s hs => hTm s hs.1)
      exact ⟨s, hs.1, P, hP, hpath, hcon⟩
    · have hpair : ∀ t ∈ Tm, ∀ t' ∈ Tm, Reach G A t t' → t = t' := by
        intro t ht t' ht' hr
        by_contra hne
        exact hdup ⟨t, ht, t', ht', hne, hr⟩
      by_cases h2 : ∃ t ∈ Tm, ∃ t' ∈ Tm, t ≠ t'
      · have hDB : D ⊆ Ins G B := hDJ.trans hJB
        obtain ⟨h, hhD, a, b, hl, hnab, hconn⟩ := static_step hB hDB hvB hTm hpair h2
        have haB : a ∈ B := (ins_of_link (hDB hhD) hl).1
        have hbB : b ∈ B := (ins_of_link (hDB hhD) hl).2
        obtain ⟨tb, htb, hrb⟩ := hcov b hbB
        obtain ⟨ta, hta, hra⟩ := hcov a haB
        have hlt : (Tm \ {tb}).ncard < n := by
          rw [← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem htb hTmfin
        have hAA : A ⊆ insert h A := Set.subset_insert _ _
        obtain ⟨s, hs, P, hP, hpath, hcon⟩ := ih _ hlt (insert h A) (D \ {h}) (Tm \ {tb}) rfl
          (Set.insert_subset (hDJ hhD) hAJ) (Set.sdiff_subset.trans hDJ)
          (Set.disjoint_insert_left.2 ⟨fun hh => hh.2 rfl, hAD.mono_right Set.sdiff_subset⟩)
          (Set.sdiff_subset.trans hTmB)
          (fun x hx => by
            obtain ⟨s0, hs0, hr0⟩ := hcov x hx
            by_cases h0 : s0 = tb
            · subst h0
              have hne : ta ≠ s0 := by
                rintro rfl
                exact hnab (hra.trans' hrb.symm')
              refine ⟨ta, ⟨hta, hne⟩, ?_⟩
              have hhA : Reach G (insert h A) b a := reach_of_isLink (Set.mem_insert _ _) hl.symm
              exact (reach_mono hAA (hr0.trans' hrb.symm')).trans'
                (hhA.trans' (reach_mono hAA hra))
            · exact ⟨s0, ⟨hs0, h0⟩, reach_mono hAA hr0⟩)
          (fun s hs => by
            refine hconn s hs.1 fun hsb => hs.2 ?_
            have : s = tb := hpair s hs.1 tb htb (hsb.trans' hrb)
            exact this)
        exact ⟨s, hs.1, P, hP.trans Set.sdiff_subset, hpath, hcon⟩
      · push Not at h2
        obtain ⟨t, ht, hrt⟩ := hcov v hvB
        obtain ⟨P, hPD, hpath⟩ := exists_isPathSet_of_reach (hTm t ht)
        refine ⟨t, ht, P, hPD, hpath, fun x hx y hy => ?_⟩
        have hAP : A ⊆ Jset \ P := fun c hc =>
          ⟨hAJ hc, fun hcP => Set.disjoint_left.1 hAD hc (hPD hcP)⟩
        have hall : ∀ w ∈ B, Reach G (Jset \ P) w t := by
          intro w hw
          obtain ⟨s, hs, hrs⟩ := hcov w hw
          have : s = t := h2 s hs t ht
          rw [this] at hrs
          exact reach_mono hAP hrs
        exact (hall x hx).trans' (hall y hy).symm'

/-- **Antichain selection** (`lem:characterization-antichain-selection`), with the order `R` an
abstract strict partial order on calls.  The calls `t i` have ports `z i`; `Jset` is the edge set
of the internal graph `J` on `B`.  Conditions (1)-(3) of the paper are phrased with the
connectivity relation `Reach` (paths are undirected, so reversed paths are free). -/
theorem antichain_selection {B : Set α} (hB : B.Finite) {Jset : Set β} (hJB : Jset ⊆ Ins G B)
    {v : α} (hvB : v ∈ B) {R : β → β → Prop} (hRirr : ∀ c, ¬ R c c)
    (hRtr : ∀ a b c, R a b → R b c → R a c) {ι : Type*} [Finite ι] (t : ι → β) (z : ι → α)
    (hzB : ∀ i, z i ∈ B)
    (h1 : ∀ x ∈ B, ∃ i, Reach G (Jset ∩ {c | R c (t i)}) x (z i))
    (h2 : ∀ i, Reach G (Jset ∩ {c | R (t i) c}) (z i) v)
    (h3 : ∀ i j, R (t i) (t j) →
      Reach G (Jset ∩ {c | R (t i) c ∧ R c (t j)}) (z i) (z j)) :
    ∃ i, ∃ P ⊆ Jset, IsPathSet G v (z i) P ∧ ∀ x ∈ B, ∀ y ∈ B, Reach G (Jset \ P) x y := by
  classical
  -- maximal calls
  let r : ι → ι → Prop := fun x a => R (t a) (t x)
  have hrt : IsTrans ι r := ⟨fun a b c hab hbc => hRtr _ _ _ hbc hab⟩
  have hri : Std.Irrefl r := ⟨fun a => hRirr _⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  let Max : Set ι := {j | ∀ i, ¬ R (t j) (t i)}
  have hmax : ∀ i, ∃ j ∈ Max, i = j ∨ R (t i) (t j) := by
    intro i
    obtain ⟨j, hj, hjmin⟩ := hwf.has_min {j | i = j ∨ R (t i) (t j)} ⟨i, Or.inl rfl⟩
    refine ⟨j, fun k hk => ?_, hj⟩
    have : k ∈ {j | i = j ∨ R (t i) (t j)} := by
      rcases hj with rfl | hj
      · exact Or.inr hk
      · exact Or.inr (hRtr _ _ _ hj hk)
    exact hjmin k this hk
  let A : Set β := Jset ∩ {c | ∃ j ∈ Max, R c (t j)}
  let D : Set β := Jset ∩ {c | ∃ i ∈ Max, R (t i) c}
  have hAD : Disjoint A D := by
    refine Set.disjoint_left.2 fun c hcA hcD => ?_
    obtain ⟨j, hj, hcj⟩ := hcA.2
    obtain ⟨i, hi, hic⟩ := hcD.2
    exact hi j (hRtr _ _ _ hic hcj)
  obtain ⟨s, hs, P, hP, hpath, hcon⟩ := static_selection hB hJB hvB (z '' Max).ncard A D (z '' Max)
    rfl Set.inter_subset_left Set.inter_subset_left hAD
    (by rintro _ ⟨j, -, rfl⟩; exact hzB j)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := h1 x hx
      obtain ⟨j, hj, hij⟩ := hmax i
      refine ⟨z j, ⟨j, hj, rfl⟩, ?_⟩
      have hA1 : ∀ c, c ∈ Jset → R c (t i) → i = j ∨ R (t i) (t j) → c ∈ A := by
        intro c hc hci hij'
        refine ⟨hc, j, hj, ?_⟩
        rcases hij' with rfl | h
        · exact hci
        · exact hRtr _ _ _ hci h
      rcases hij with rfl | hij
      · exact reach_mono (fun c hc => hA1 c hc.1 hc.2 (Or.inl rfl)) hi
      · refine (reach_mono (fun c hc => hA1 c hc.1 hc.2 (Or.inr hij)) hi).trans'
          (reach_mono (fun c hc => ⟨hc.1, j, hj, hc.2.2⟩) (h3 i j hij)))
    (by
      rintro _ ⟨i, hi, rfl⟩
      exact (reach_mono (F' := D) (fun c hc => ⟨hc.1, i, hi, hc.2⟩) (h2 i)).symm')
  obtain ⟨j, hj, rfl⟩ := hs
  exact ⟨j, P, hP.trans Set.inter_subset_left, hpath, hcon⟩

end Lax630294Proofs.Ports
