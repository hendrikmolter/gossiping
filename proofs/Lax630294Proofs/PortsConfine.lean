import Lax630294Proofs.PortsRoutes
import Lax630294Proofs.PortsQ

/-!
# Confinement to a quotient forest (`lem:characterization-forest-confinement`)
-/

namespace Lax630294Proofs.Ports

open Graph Lax630294.Gossiping Lax630294Proofs.QuotientCore Lax630294Proofs.QuotientTwoTree
  Lax630294Proofs.Quotient2Cycle Lax630294Proofs.CallOrder Lax630294Proofs.Causal
  Lax630294Proofs.CausalQuotient Lax630294Proofs.QuotientBlocks Lax630294Proofs.QuotientDef
  Lax630294Proofs.Quotient2Contract Lax630294Proofs.Quotient2Quotient Lax630294Proofs.Quotient2MLift

variable {α β : Type*} {G : Graph α β} {ℓ : β → ℕ}

lemma causalQ_trans {a b c : β} (h1 : causalQ G ℓ a b) (h2 : causalQ G ℓ b c) :
    causalQ G ℓ a c := ⟨h1.1, h2.2.1, causal_trans h1.2.2 h2.2.2⟩

lemma causalQ_irrefl (c : β) : ¬ causalQ G ℓ c c := fun h => causal_irrefl c h.2.2

/-- **`lem:characterization-forest-confinement`.**  Let `a <_{P_Q} b` be external calls sharing the
quotient vertex `U`, and let `R` be an acyclic set of external calls containing `a`, `b` and all
external calls between them.  Then there is an internal increasing route between a port of `a` and a
port of `b` in `U`, with all its calls strictly between `a` and `b`. -/
-- DEVIATION: acyclicity of the forest is used in the form "every edge is a bridge" (`Acyc`);
-- the paper's "deleting `a,b` separates ..." and "a closed trail in a forest is empty" are
-- `Acyc.not_reach` and `closed_trail_nil`.  The marker argument of the paper is `chain_walk`.
theorem confinement (hV : V(G).Finite) (hE : E(G).Finite) {a b : β} (hab : causalQ G ℓ a b)
    {U : Set α} (haU : (quotient G).Inc a U) (hbU : (quotient G).Inc b U) {R : Set β}
    (hR : Acyc (quotient G) R) (haR : a ∈ R) (hbR : b ∈ R)
    (hmid : ∀ c, causalQ G ℓ a c → causalQ G ℓ c b → c ∈ R) :
    ∃ pa pb, IsPort G U a pa ∧ IsPort G U b pb ∧ Seg G ℓ (some a) (some b) pa pb := by
  obtain ⟨s, t, vs, es, hs, ht, hpw, hes⟩ := chain_walk hab.2.2
  have hbnd : Bnd G ℓ (some a) (some b) := fun a' b' ha hb => by
    obtain rfl := Option.some.inj ha
    obtain rfl := Option.some.inj hb
    exact hab.2.2
  have hiv : ∀ c ∈ es, c ∈ Iv G ℓ (some a) (some b) := fun c hc =>
    ⟨fun a' ha' => by obtain rfl := Option.some.inj ha'; exact (hes c hc).1,
     fun b' hb' => by obtain rfl := Option.some.inj hb'; exact (hes c hc).2⟩
  obtain ⟨ts, hts, hsub⟩ := XR.of_pw hV hE hpw (some a) (some b) hbnd hiv
  have hT := XR.incTrail hV hE hts
  have hQa : a ∈ E(quotient G) := hab.1
  have hQb : b ∈ E(quotient G) := hab.2.1
  have htsR : ∀ c ∈ ts, c ∈ R := by
    intro c hc
    have hcE : c ∈ E(quotient G) := hT.edge_mem c hc
    exact hmid c ⟨hQa, hcE, (hes c (hsub c hc)).1⟩ ⟨hcE, hQb, (hes c (hsub c hc)).2⟩
  have hne_a : ∀ c ∈ ts, c ≠ a := fun c hc h => causal_irrefl a (h ▸ (hes c (hsub c hc)).1)
  have hne_b : ∀ c ∈ ts, c ≠ b := fun c hc h => causal_irrefl b (h ▸ (hes c (hsub c hc)).2)
  have hba : b ≠ a := fun h => causal_irrefl a (h ▸ hab.2.2)
  obtain ⟨a', hUa⟩ := haU
  obtain ⟨b', hUb⟩ := hbU
  have hsV : s ∈ V(G) := hs.vertex_mem
  have htV : t ∈ V(G) := ht.vertex_mem
  have hbs : (quotient G).Inc a (blk G s) := inc_quotient hQa hs
  have hbt : (quotient G).Inc b (blk G t) := inc_quotient hQb ht
  have hs' := hbs.eq_or_eq_of_isLink hUa
  have ht' := hbt.eq_or_eq_of_isLink hUb
  have hRa : ∀ c ∈ ts, c ∈ R \ {a} := fun c hc => ⟨htsR c hc, hne_a c hc⟩
  have hRb : ∀ c ∈ ts, c ∈ R \ {b} := fun c hc => ⟨htsR c hc, hne_b c hc⟩
  have hUblk : blk G s = U ∧ blk G t = U := by
    rcases hs' with h1 | h1 <;> rcases ht' with h2 | h2
    · exact ⟨h1, h2⟩
    · -- start in `U`, end in `b'`
      exfalso
      rw [h1, h2] at hT
      exact hR b hbR U b' hUb (hT.reach hRb)
    · -- start in `a'`, end in `U`
      exfalso
      rw [h1, h2] at hT
      exact hR a haR U a' hUa (hT.reach hRa).symm'
    · -- start in `a'`, end in `b'`
      exfalso
      rw [h1, h2] at hT
      have h3 : Reach (quotient G) (R \ {a}) b' U :=
        reach_of_isLink ⟨hbR, hba⟩ hUb.symm
      exact hR a haR U a' hUa (h3.symm'.trans' (hT.reach hRa).symm')
  obtain ⟨hsU, htU⟩ := hUblk
  rw [hsU, htU] at hT
  have hnd : ts.Nodup := IncTrail.nodup (P := causalQ G ℓ) (fun _ _ _ h1 h2 => causalQ_trans h1 h2)
    (fun c => causalQ_irrefl c) hT
  have hnil : ts = [] := closed_trail_nil hR hT htsR hnd
  subst hnil
  exact ⟨s, t, ⟨hsU ▸ mem_blk_self hV hE hsV, hs⟩, ⟨htU ▸ mem_blk_self hV hE htV, ht⟩, hts⟩

end Lax630294Proofs.Ports
