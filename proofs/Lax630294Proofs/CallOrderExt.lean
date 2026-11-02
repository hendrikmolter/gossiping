import Lax630294Proofs.CallOrderDefs

/-!
# Linear extensions with prescribed layers

A finite strict partial order `Q` on a set `E` of edges, together with a layering `lam : β → ℕ`
with `Q a b → lam a ≤ lam b`, has a linear extension `ℓ : β → ℕ` (injective on `E`) which in
addition puts lower layers first.  (Used to build "linear extensions placing `I` first and `e`
last in `I`".)
-/

namespace Lax630294Proofs.CallOrder

variable {α β : Type*}

lemma exists_linear_ext {E : Set β} (hE : E.Finite) (Q : β → β → Prop)
    (hirr : ∀ e, ¬ Q e e) (htr : ∀ {a b c}, Q a b → Q b c → Q a c)
    (hQE : ∀ {a b}, Q a b → a ∈ E ∧ b ∈ E) (lam : β → ℕ)
    (hlam : ∀ {a b}, Q a b → lam a ≤ lam b) :
    ∃ ℓ : β → ℕ, Set.InjOn ℓ E ∧ (∀ a b, Q a b → ℓ a < ℓ b) ∧
      (∀ a ∈ E, ∀ b ∈ E, lam a < lam b → ℓ a < ℓ b) := by
  classical
  let R : β → β → Prop := fun a b =>
    a = b ∨ (a ∈ E ∧ b ∈ E ∧ (lam a < lam b ∨ (lam a = lam b ∧ Q a b)))
  have hR : IsPartialOrder β R := by
    refine { refl := fun a => Or.inl rfl, trans := ?_, antisymm := ?_ }
    · intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb, h1⟩
      · exact hbc
      rcases hbc with rfl | ⟨_, hc, h2⟩
      · exact Or.inr ⟨ha, hb, h1⟩
      refine Or.inr ⟨ha, hc, ?_⟩
      rcases h1 with h1 | ⟨h1, q1⟩ <;> rcases h2 with h2 | ⟨h2, q2⟩
      · exact Or.inl (lt_trans h1 h2)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, htr q1 q2⟩
    · intro a b hab hba
      rcases hab with rfl | ⟨ha, hb, h1⟩
      · rfl
      rcases hba with h | ⟨_, _, h2⟩
      · exact h.symm
      rcases h1 with h1 | ⟨h1, q1⟩ <;> rcases h2 with h2 | ⟨h2, q2⟩
      · omega
      · omega
      · omega
      · exact (hirr a (htr q1 q2)).elim
  obtain ⟨s, hs, hRs⟩ := extend_partialOrder R
  let ℓ : β → ℕ := fun a => {c | c ∈ E ∧ s c a ∧ c ≠ a}.ncard
  have hfin : ∀ a, {c | c ∈ E ∧ s c a ∧ c ≠ a}.Finite := fun a => hE.subset fun c hc => hc.1
  have hlt : ∀ a ∈ E, ∀ b ∈ E, s a b → a ≠ b → ℓ a < ℓ b := by
    intro a ha b hb hab hne
    apply Set.ncard_lt_ncard _ (hfin b)
    refine ⟨?_, fun h => ?_⟩
    · rintro c ⟨hc, hca, hcne⟩
      refine ⟨hc, _root_.trans hca hab, ?_⟩
      rintro rfl
      exact hcne (antisymm hca hab)
    · exact (h ⟨ha, hab, hne⟩).2.2 rfl
  have hRlt : ∀ a b, R a b → a ≠ b → ℓ a < ℓ b := by
    intro a b h hne
    rcases h with h | ⟨ha, hb, _⟩
    · exact (hne h).elim
    · exact hlt a ha b hb (hRs _ _ (Or.inr ⟨ha, hb, by assumption⟩)) hne
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    by_contra hne
    rcases hs.total a b with h | h
    · exact (hlt a ha b hb h hne).ne hab
    · exact (hlt b hb a ha h (Ne.symm hne)).ne hab.symm
  · intro a b hQ
    obtain ⟨ha, hb⟩ := hQE hQ
    have hne : a ≠ b := fun h => hirr a (h ▸ hQ)
    apply hlt a ha b hb _ hne
    apply hRs
    refine Or.inr ⟨ha, hb, ?_⟩
    rcases Nat.lt_or_ge (lam a) (lam b) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨le_antisymm (hlam hQ) h, hQ⟩
  · intro a ha b hb hab
    have hne : a ≠ b := fun h => by subst h; omega
    exact hlt a ha b hb (hRs _ _ (Or.inr ⟨ha, hb, Or.inl hab⟩)) hne

end Lax630294Proofs.CallOrder
