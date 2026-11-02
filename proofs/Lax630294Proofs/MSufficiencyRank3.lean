import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff

/-!
# Rank-three lemma (abstract form)

The combinatorial core of `lem:rank-three` of the paper, stated for two families `P`, `Q` of
three-element subsets (the bases of the two rank-three matroids) in which every element is
avoided by some member (no coloops).
-/

namespace Lax630294Proofs.MSufficiencyRank3

open Finset

variable {ι : Type*} [DecidableEq ι]

lemma erase_structure {A B : Finset ι} {y : ι} (hA : A.card = 3) (hB : B.card = 3)
    (hy : y ∈ B) (hyA : y ∉ A) (h : 2 ≤ (A ∩ B).card) :
    ∃ x, x ∉ B ∧ A = insert x (B.erase y) := by
  have hsub : A ∩ B ⊆ B.erase y := by
    intro z hz
    rw [mem_inter] at hz
    exact mem_erase.2 ⟨fun h' => hyA (h' ▸ hz.1), hz.2⟩
  have hcard : (B.erase y).card = 2 := by rw [card_erase_of_mem hy, hB]
  have heq : A ∩ B = B.erase y := eq_of_subset_of_card_le hsub (by omega)
  have h1 : (A \ B).card = 1 := by
    have := card_sdiff_add_card_inter A B
    have h2 : (A ∩ B).card = 2 := by rw [heq]; exact hcard
    omega
  obtain ⟨x, hx⟩ := card_eq_one.1 h1
  have hxA : x ∈ A \ B := by rw [hx]; simp
  refine ⟨x, (mem_sdiff.1 hxA).2, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hzB : z ∈ B
    · apply mem_insert_of_mem
      rw [← heq]; exact mem_inter.2 ⟨hz, hzB⟩
    · have : z ∈ A \ B := mem_sdiff.2 ⟨hz, hzB⟩
      rw [hx] at this
      simp only [mem_singleton] at this
      simp [this]
  · intro hz
    rcases mem_insert.1 hz with rfl | hz
    · exact (mem_sdiff.1 hxA).1
    · have : z ∈ A ∩ B := by rw [heq]; exact hz
      exact (mem_inter.1 this).1

lemma card_insert_erase {B : Finset ι} {x y : ι} (hB : B.card = 3) (hy : y ∈ B) (hx : x ∉ B) :
    (insert x (B.erase y)).card = 3 := by
  rw [card_insert_of_notMem (fun h => hx (mem_of_mem_erase h)), card_erase_of_mem hy, hB]

lemma triple {B Ai Aj Bh : Finset ι} {yi yj yh xi xj : ι}
    (hBeq : B = {yi, yj, yh}) (hij : yi ≠ yj) (hih : yi ≠ yh) (hjh : yj ≠ yh)
    (hxi : xi ∉ B) (hxj : xj ∉ B)
    (hAi : Ai = insert xi (B.erase yi)) (hAj : Aj = insert xj (B.erase yj))
    (hBh : Bh.card = 3) (hyh : yh ∉ Bh)
    (hi : 2 ≤ (Ai ∩ Bh).card) (hj : 2 ≤ (Aj ∩ Bh).card) :
    xi = xj ∧ Bh = insert xi (B.erase yh) := by
  have hBc : B.card = 3 := by
    rw [hBeq]
    simp [card_insert_of_notMem, hij, hih, hjh]
  have hyiB : yi ∈ B := by simp [hBeq]
  have hyjB : yj ∈ B := by simp [hBeq]
  have hyhB : yh ∈ B := by simp [hBeq]
  have hAic := card_insert_erase hBc hyiB hxi
  have hAjc := card_insert_erase hBc hyjB hxj
  rw [← hAi] at hAic
  rw [← hAj] at hAjc
  have hyhAi : yh ∈ Ai := by
    rw [hAi]; exact mem_insert_of_mem (mem_erase.2 ⟨hih.symm, hyhB⟩)
  have hyhAj : yh ∈ Aj := by
    rw [hAj]; exact mem_insert_of_mem (mem_erase.2 ⟨hjh.symm, hyhB⟩)
  obtain ⟨x', hx', hBhi⟩ := erase_structure hBh hAic hyhAi hyh (by rwa [inter_comm])
  obtain ⟨x'', hx'', hBhj⟩ := erase_structure hBh hAjc hyhAj hyh (by rwa [inter_comm])
  have hxiBh : xi ∈ Bh := by
    rw [hBhi]
    apply mem_insert_of_mem
    rw [mem_erase, hAi]
    refine ⟨?_, mem_insert_self _ _⟩
    rintro rfl; exact hxi hyhB
  have hyjBh : yj ∈ Bh := by
    rw [hBhi]
    apply mem_insert_of_mem
    rw [mem_erase, hAi]
    refine ⟨hjh, mem_insert_of_mem (mem_erase.2 ⟨hij.symm, hyjB⟩)⟩
  have hxjBh : xj ∈ Bh := by
    rw [hBhj]
    apply mem_insert_of_mem
    rw [mem_erase, hAj]
    refine ⟨?_, mem_insert_self _ _⟩
    rintro rfl; exact hxj hyhB
  have hyiBh : yi ∈ Bh := by
    rw [hBhj]
    apply mem_insert_of_mem
    rw [mem_erase, hAj]
    refine ⟨hih, mem_insert_of_mem (mem_erase.2 ⟨hij, hyiB⟩)⟩
  have hxeq : xi = xj := by
    by_contra hne
    have hsub : ({xi, xj, yi, yj} : Finset ι) ⊆ Bh := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have hc := card_le_card hsub
    have hxiyi : xi ≠ yi := fun h => hxi (h ▸ hyiB)
    have hxiyj : xi ≠ yj := fun h => hxi (h ▸ hyjB)
    have hxjyi : xj ≠ yi := fun h => hxj (h ▸ hyiB)
    have hxjyj : xj ≠ yj := fun h => hxj (h ▸ hyjB)
    have : ({xi, xj, yi, yj} : Finset ι).card = 4 := by
      simp [card_insert_of_notMem, hne, hxiyi, hxiyj, hxjyi, hxjyj, hij]
    omega
  refine ⟨hxeq, ?_⟩
  subst hxeq
  have hsub : insert xi (B.erase yh) ⊆ Bh := by
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact hxiBh
    · have hzB := mem_of_mem_erase hz
      have hzh := ne_of_mem_erase hz
      rw [hBeq] at hzB
      simp only [mem_insert, mem_singleton] at hzB
      rcases hzB with rfl | rfl | rfl
      · exact hyiBh
      · exact hyjBh
      · exact absurd rfl hzh
  exact (eq_of_subset_of_card_le hsub (by rw [hBh, card_insert_erase hBc hyhB hxi])).symm

lemma erase_sub {A Bh B : Finset ι} {x yh : ι} (hx : x ∉ A) (hBh : Bh = insert x (B.erase yh))
    (hcard : (B.erase yh).card = 2) (h : 2 ≤ (A ∩ Bh).card) : B.erase yh ⊆ A := by
  have hsub : A ∩ Bh ⊆ B.erase yh := by
    intro z hz
    rw [mem_inter, hBh, mem_insert] at hz
    rcases hz.2 with rfl | h'
    · exact absurd hz.1 hx
    · exact h'
  have := eq_of_subset_of_card_le hsub (by omega)
  rw [← this]
  exact inter_subset_left

lemma exists_w {W A : Finset ι} (hW : W.card = 4) (hA : A.card = 3) (hnot : ¬ A ⊆ W) :
    ∃ w ∈ W, (A ∩ W.erase w).card ≤ 1 := by
  obtain ⟨e, heA, heW⟩ := not_subset.1 hnot
  have h2 : (A ∩ W).card ≤ 2 := by
    have : A ∩ W ⊆ A.erase e := by
      intro z hz
      rw [mem_inter] at hz
      exact mem_erase.2 ⟨fun h => heW (h ▸ hz.2), hz.1⟩
    have := card_le_card this
    rw [card_erase_of_mem heA, hA] at this
    omega
  by_cases hne : (A ∩ W).Nonempty
  · obtain ⟨w, hw⟩ := hne
    refine ⟨w, (mem_inter.1 hw).2, ?_⟩
    have : A ∩ W.erase w ⊆ (A ∩ W).erase w := by
      intro z hz
      rw [mem_inter, mem_erase] at hz
      rw [mem_erase, mem_inter]
      exact ⟨hz.2.1, hz.1, hz.2.2⟩
    have := card_le_card this
    rw [card_erase_of_mem hw] at this
    omega
  · have hW0 : W.Nonempty := by
      rw [← card_pos]; omega
    obtain ⟨w, hw⟩ := hW0
    refine ⟨w, hw, ?_⟩
    have : A ∩ W.erase w ⊆ A ∩ W := inter_subset_inter_left (erase_subset _ _)
    have h0 : A ∩ W = ∅ := not_nonempty_iff_eq_empty.1 hne
    rw [h0] at this
    have := card_le_card this
    rw [card_empty] at this
    omega

-- DEVIATION: the paper states lem:rank-three for two rank-three matroids without coloops
-- (given by independence oracles) and returns either two bases meeting in at most one element
-- or a four-element set W such that the bases of both matroids are exactly the three-element
-- subsets of W.  Here no matroid is used: P, Q are arbitrary families of three-element sets
-- (the bases) in which every element is avoided by some member (= no coloop).  The conclusion is
-- the same dichotomy, with the second alternative stated as W of size 4 containing every member
-- of P and of Q (this is exactly "every edge outside W is a loop", which is what is used
-- afterwards).  The proof follows the paper's case analysis (y_i, A_i, x_i, B_h, A_0, scan of
-- E \ W) but without any algorithmic content.
theorem rank_three [Nonempty ι] (P Q : Set (Finset ι))
    (hP : ∀ A ∈ P, A.card = 3) (hQ : ∀ B ∈ Q, B.card = 3)
    (hP' : ∀ i, ∃ A ∈ P, i ∉ A) (hQ' : ∀ i, ∃ B ∈ Q, i ∉ B) :
    (∃ A ∈ P, ∃ B ∈ Q, (A ∩ B).card ≤ 1) ∨
    ∃ W : Finset ι, W.card = 4 ∧ (∀ A ∈ P, A ⊆ W) ∧ (∀ B ∈ Q, B ⊆ W) := by
  by_contra hcon
  obtain ⟨hH, hW⟩ := not_or.1 hcon
  have H : ∀ A ∈ P, ∀ B ∈ Q, 2 ≤ (A ∩ B).card := by
    intro A hA B hB
    by_contra h
    exact hH ⟨A, hA, B, hB, by omega⟩
  apply hW
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨B, hBQ, -⟩ := hQ' i0
  obtain ⟨y1, y2, y3, h12, h13, h23, hBeq⟩ := card_eq_three.1 (hQ B hBQ)
  have hBc := hQ B hBQ
  have hy1 : y1 ∈ B := by simp [hBeq]
  have hy2 : y2 ∈ B := by simp [hBeq]
  have hy3 : y3 ∈ B := by simp [hBeq]
  have getA : ∀ y ∈ B, ∃ A ∈ P, ∃ x, x ∉ B ∧ A = insert x (B.erase y) := by
    intro y hy
    obtain ⟨A, hA, hyA⟩ := hP' y
    obtain ⟨x, hx, hAeq⟩ := erase_structure (hP A hA) hBc hy hyA (H A hA B hBQ)
    exact ⟨A, hA, x, hx, hAeq⟩
  obtain ⟨A1, hA1, x1, hx1, hA1e⟩ := getA y1 hy1
  obtain ⟨A2, hA2, x2, hx2, hA2e⟩ := getA y2 hy2
  obtain ⟨A3, hA3, x3, hx3, hA3e⟩ := getA y3 hy3
  obtain ⟨B1, hB1, hy1B1⟩ := hQ' y1
  obtain ⟨B2, hB2, hy2B2⟩ := hQ' y2
  obtain ⟨B3, hB3, hy3B3⟩ := hQ' y3
  have hBeq1 : B = {y1, y2, y3} := hBeq
  have t12 := triple (B := B) (Bh := B3) hBeq1 h12 h13 h23 hx1 hx2 hA1e hA2e (hQ B3 hB3) hy3B3
    (H A1 hA1 B3 hB3) (H A2 hA2 B3 hB3)
  have t13 := triple (B := B) (Bh := B2) (yi := y1) (yj := y3) (yh := y2)
    (by rw [hBeq1]; ext z; simp; tauto) h13 h12 h23.symm hx1 hx3 hA1e hA3e (hQ B2 hB2) hy2B2
    (H A1 hA1 B2 hB2) (H A3 hA3 B2 hB2)
  have t23 := triple (B := B) (Bh := B1) (yi := y2) (yj := y3) (yh := y1)
    (by rw [hBeq1]; ext z; simp; tauto) h23 h12.symm h13.symm hx2 hx3 hA2e hA3e (hQ B1 hB1) hy1B1
    (H A2 hA2 B1 hB1) (H A3 hA3 B1 hB1)
  obtain ⟨hx12, hB3e⟩ := t12
  obtain ⟨hx13, hB2e⟩ := t13
  obtain ⟨hx23, hB1e⟩ := t23
  subst hx12 hx13
  -- now x := x1
  obtain ⟨A0, hA0, hxA0⟩ := hP' x1
  have hcard2 : ∀ y ∈ B, (B.erase y).card = 2 := by
    intro y hy; rw [card_erase_of_mem hy, hBc]
  have s1 := erase_sub hxA0 hB1e (hcard2 y1 hy1) (H A0 hA0 B1 hB1)
  have s2 := erase_sub hxA0 hB2e (hcard2 y2 hy2) (H A0 hA0 B2 hB2)
  have s3 := erase_sub hxA0 hB3e (hcard2 y3 hy3) (H A0 hA0 B3 hB3)
  have hBA0 : B ⊆ A0 := by
    intro z hz
    rw [hBeq1] at hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact s2 (mem_erase.2 ⟨h12, hy1⟩)
    · exact s1 (mem_erase.2 ⟨h12.symm, hy2⟩)
    · exact s1 (mem_erase.2 ⟨h13.symm, hy3⟩)
  have hA0B : A0 = B := (eq_of_subset_of_card_le hBA0 (by rw [hP A0 hA0, hBc])).symm
  have hBP : B ∈ P := hA0B ▸ hA0
  have hWc : (insert x1 B).card = 4 := by
    rw [card_insert_of_notMem hx1, hBc]
  have fam : ∀ w ∈ insert x1 B, (insert x1 B).erase w ∈ P ∧ (insert x1 B).erase w ∈ Q := by
    intro w hw
    rcases mem_insert.1 hw with rfl | hwB
    · rw [erase_insert hx1]; exact ⟨hBP, hBQ⟩
    · have hne : w ≠ x1 := fun h => hx1 (h ▸ hwB)
      have : (insert x1 B).erase w = insert x1 (B.erase w) := erase_insert_of_ne hne.symm
      rw [this]
      rw [hBeq1] at hwB
      simp only [mem_insert, mem_singleton] at hwB
      rcases hwB with rfl | rfl | rfl
      · exact ⟨hA1e ▸ hA1, hB1e ▸ hB1⟩
      · exact ⟨hA2e ▸ hA2, hB2e ▸ hB2⟩
      · exact ⟨hA3e ▸ hA3, hB3e ▸ hB3⟩
  refine ⟨insert x1 B, hWc, fun A hA => ?_, fun B' hB' => ?_⟩
  · by_contra hnot
    obtain ⟨w, hw, hle⟩ := exists_w hWc (hP A hA) hnot
    have := H A hA _ (fam w hw).2
    omega
  · by_contra hnot
    obtain ⟨w, hw, hle⟩ := exists_w hWc (hQ B' hB') hnot
    have := H _ (fam w hw).1 B' hB'
    rw [inter_comm] at this
    omega

end Lax630294Proofs.MSufficiencyRank3
