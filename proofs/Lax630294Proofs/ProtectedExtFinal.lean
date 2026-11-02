import Lax630294Proofs.ProtectedExtWitness

/-!
# Protected extension (`lem:characterization-protected-extension`), final statement

Combines
* `cls_init` : the tree `B = F + e` of the canonical form lies in the class `Cls`;
* `protected_exchange` : a minimising tree of the class has a forest as complement;
* `mwitness_of_cls` : the resulting forests give an `M`-witness.
-/

namespace Lax630294Proofs.ProtectedExt

open Graph Lax630294.SpanningStructures Lax630294Proofs.ThreePhase Lax630294Proofs.QuotientCore
  Lax630294Proofs.QuotientTwoTree Lax630294Proofs.QuotientExchange Lax630294Proofs

variable {α β : Type*} {H : Graph α β} {P : β → β → Prop} {x0 x1 u0 u1 : α} {e f0 f1 g : β}

/-- **Minimisation.**  If the class `Cls` is nonempty, it contains a tree whose complement is a
forest (paper l. 4778-4802: minimise the number of components of the complement). -/
theorem protected_exchange (hV : V(H).Finite) (hE : E(H).Finite)
    (hloop : ∀ e x, ¬ H.IsLink e x x)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X)
    (geo : Geo H x0 x1 u0 u1 e f0 f1 g) (hcard : E(H).ncard + 4 = 2 * V(H).ncard)
    {S0 : Set β} (h0 : Cls H x0 x1 u0 e f0 f1 g S0) :
    ∃ S, Cls H x0 x1 u0 e f0 f1 g S ∧ IsForest H (E(H) \ S) := by
  classical
  have hex : ∃ c, ∃ S, Cls H x0 x1 u0 e f0 f1 g S ∧ comps H (E(H) \ S) = c := ⟨_, S0, h0, rfl⟩
  obtain ⟨S, hS, hSc⟩ := Nat.find_spec hex
  have hmin : ∀ S', Cls H x0 x1 u0 e f0 f1 g S' → comps H (E(H) \ S) ≤ comps H (E(H) \ S') := by
    intro S' h
    rw [hSc]
    exact Nat.find_min' hex ⟨S', h, rfl⟩
  exact ⟨S, hS, forest_of_min' hV hE hloop hno geo hcard hS hmin⟩

/-- The starting tree `B = F + e` of the paper is in the class. -/
theorem cls_init (hV : V(H).Finite) (hE : E(H).Finite) (geo : Geo H x0 x1 u0 u1 e f0 f1 g)
    {I : Set β} {X Y : Set α} (hIE : I ⊆ E(H))
    (hcardF : (E(H) \ I).ncard + 2 = V(H).ncard)
    (hconnF : ∀ v ∈ V(H), Reach H (E(H) \ I) v x0 ∨ Reach H (E(H) \ I) v x1)
    (hX : CallOrder.IsTreeComp H I X) (hY : CallOrder.IsTreeComp H I Y) (hXY : X ≠ Y)
    (heX : e ∈ CallOrder.edgesIn H I X) (hgY : g ∈ CallOrder.edgesIn H I Y)
    (hf0 : f0 ∈ E(H) \ I) (hf1 : f1 ∈ E(H) \ I)
    (hunic : ∀ D, CallOrder.IsComp H I D → D ≠ X → D ≠ Y → CallOrder.IsUnicyclicComp H I D) :
    Cls H x0 x1 u0 e f0 f1 g (insert e (E(H) \ I)) := by
  have hdisj : Disjoint X Y := hX.1.disjoint_of_ne hY.1 hXY
  obtain ⟨hx0X, hx1X⟩ := heX.2.ends_mem geo.le
  obtain ⟨hu0Y, hu1Y⟩ := hgY.2.ends_mem geo.lg
  have heI : e ∈ I := heX.1
  have hgI : g ∈ I := hgY.1
  have hK0 : E(H) \ insert e (E(H) \ I) = I \ {e} := by
    ext k
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_and, not_not]
    constructor
    · rintro ⟨hkE, hke, hk⟩
      exact ⟨hk hkE, hke⟩
    · rintro ⟨hkI, hke⟩
      exact ⟨hIE hkI, hke, fun _ => hkI⟩
  have hge : g ≠ e := by
    rintro rfl
    rcases geo.lg.eq_and_eq_or_eq_and_eq geo.le with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Set.disjoint_left.1 hdisj hx0X hu0Y
    · exact Set.disjoint_left.1 hdisj hx1X hu0Y
  -- the tree
  have htree : IsSpanningTree H (insert e (E(H) \ I)) := by
    rw [isSpanningTree_iff hV hE]
    have heF : e ∉ E(H) \ I := fun h => h.2 heI
    refine ⟨Set.insert_subset (hIE heI) Set.sdiff_subset, ⟨x0, geo.le.left_mem⟩, ?_, ?_⟩
    · have hall : ∀ v ∈ V(H), Reach H (insert e (E(H) \ I)) v x0 := by
        intro v hv
        rcases hconnF v hv with h | h
        · exact reach_mono (Set.subset_insert _ _) h
        · exact (reach_mono (Set.subset_insert _ _) h).trans'
            (reach_of_isLink (Set.mem_insert _ _) geo.le.symm)
      intro x hx y hy
      exact (hall x hx).trans' (hall y hy).symm'
    · rw [Set.ncard_insert_of_notMem heF (hE.subset Set.sdiff_subset)]
      omega
  obtain ⟨A1, A2, hA1, hA2, hdis12, hunion, hx0A1, hx1A2⟩ :=
    CallOrder.tree_split hV hE hX heX geo.le
  refine ⟨htree, Set.mem_insert _ _, Or.inr hf0, Or.inr hf1, hIE hgI, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact hge h
    · exact h.2 hgI
  · rw [hK0]
    intro h
    exact Set.disjoint_left.1 hdis12 (hA1.1.mem_of_conn hx0A1 h) hx1A2
  · rw [hK0]
    intro h
    have := hX.1.mem_of_conn hx0X (reach_mono Set.sdiff_subset h)
    exact Set.disjoint_left.1 hdisj this hu0Y
  · rw [hK0]
    intro h
    have := hX.1.mem_of_conn hx1X (reach_mono Set.sdiff_subset h)
    exact Set.disjoint_left.1 hdisj this hu0Y
  · rw [hK0]
    intro A hA n0 n1 nu
    obtain ⟨v, hv⟩ := hA.1
    -- no vertex of `A` lies in `X`
    have hnX : ∀ w ∈ A, w ∉ X := by
      intro w hw hwX
      rw [← hunion] at hwX
      rcases hwX with hw1 | hw2
      · exact n0 (hA.mem_of_conn hw (CallOrder.Conn.symm (hA1.1.2.2.2 _ hx0A1 _ hw1)))
      · exact n1 (hA.mem_of_conn hw (CallOrder.Conn.symm (hA2.1.2.2.2 _ hx1A2 _ hw2)))
    have hAI : CallOrder.IsComp H I A := by
      refine ⟨hA.1, hA.2.1, ?_, fun x hx y hy => (hA.2.2.2 x hx y hy).mono Set.sdiff_subset⟩
      intro k hk p q hl hp
      by_cases hke : k = e
      · subst hke
        exfalso
        rcases geo.le.eq_and_eq_or_eq_and_eq hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hnX _ hp hx0X
        · exact hnX _ hp hx1X
      · exact hA.2.2.1 k ⟨hk, hke⟩ p q hl hp
    have hEE : CallOrder.edgesIn H (I \ {e}) A = CallOrder.edgesIn H I A := by
      ext k
      constructor
      · rintro ⟨hk, hint⟩
        exact ⟨hk.1, hint⟩
      · rintro ⟨hk, hint⟩
        refine ⟨⟨hk, ?_⟩, hint⟩
        rintro rfl
        exact hnX _ ((hint.ends_mem geo.le).1) hx0X
    have hAX : A ≠ X := fun h => hnX v hv (h ▸ hv)
    have hAY : A ≠ Y := fun h => nu (h ▸ hu0Y)
    have := (hunic A hAI hAX hAY).2
    rw [hEE]
    omega

/-- The vertices reached from the roots in the canonical forest `F = E(H) \ I`. -/
lemma canonical_reach [hH : H.Simple] {I : Set β} {X : Set α} {e : β} {x0 x1 : α}
    (hC : CallOrder.IsCanonical H P I X e x0 x1) :
    ∀ v ∈ V(H), Reach H (E(H) \ I) v x0 ∨ Reach H (E(H) \ I) v x1 := by
  obtain ⟨par, pe, hfor⟩ := hC.forest
  intro v hv
  obtain ⟨n, hn⟩ := hfor.reach v hv
  have hr := hfor.reachable_iterate hv n
  have hx0 : x0 ∈ V(H) := hC.e_link.left_mem
  have hx1 : x1 ∈ V(H) := hC.e_link.right_mem
  rcases hn with hn | hn
  · left
    have h' : (⟨par^[n] v, hfor.iterate_mem hv n⟩ : V(H)) = ⟨x0, hx0⟩ := Subtype.ext hn
    rw [h'] at hr
    exact (underlying_reachable_iff _ _).1 hr
  · right
    have h' : (⟨par^[n] v, hfor.iterate_mem hv n⟩ : V(H)) = ⟨x1, hx1⟩ := Subtype.ext hn
    rw [h'] at hr
    exact (underlying_reachable_iff _ _).1 hr

/-- **`lem:characterization-protected-extension`.**

Let `H` be a finite simple graph with `r ≥ 4` vertices and `2r - 4` edges which is admissible for
the causal order `P`, with no two-tree set of size at least two (in the paper: the quotient `Q`),
and let `I, X, e = x0 x1` be the canonical data (`CallOrder.IsCanonical`) with second tree component `Y` of
`H[I]` (all other components unicyclic).  Let `g = u0 u1` be an edge of `Y` and
`f0 = x0 u0`, `f1 = x1 u1` edges of `F = E(H) \ I`.  Then the four-cycle `x0 u0 u1 x1` with edges
`f0, g, f1, e` extends to an `M`-witness of `H` whose two forests have exactly one of
`x0, x1, u0, u1` in each of their (four) components. -/
theorem protected_extension (hA : CallOrder.Admissible H P) (hr : 4 ≤ V(H).ncard)
    (hEc : E(H).ncard = 2 * V(H).ncard - 4)
    (hno : ∀ X ⊆ V(H), 2 ≤ X.ncard → ¬ IsTwoTreeSet H X)
    {I : Set β} {X : Set α} {x0 x1 : α} {e : β} (hC : CallOrder.IsCanonical H P I X e x0 x1)
    {Y : Set α} (hY : CallOrder.IsTreeComp H I Y) (hYX : Y ≠ X)
    (hunic : ∀ D, CallOrder.IsComp H I D → D ≠ X → D ≠ Y → CallOrder.IsUnicyclicComp H I D)
    {g f0 f1 : β} {u0 u1 : α} (hg : g ∈ CallOrder.edgesIn H I Y) (hgl : H.IsLink g u0 u1)
    (hf0 : f0 ∈ E(H) \ I) (hf0l : H.IsLink f0 x0 u0)
    (hf1 : f1 ∈ E(H) \ I) (hf1l : H.IsLink f1 x1 u1) :
    ∃ L1 L2 : Set β, Lax630294.MGraph.IsMWitness H {e, g, f0, f1} L1 L2 ∧
      OneEach H L1 x0 x1 u0 u1 ∧ OneEach H L2 x0 x1 u0 u1 ∧
      (x0 ≠ x1 ∧ x0 ≠ u0 ∧ x0 ≠ u1 ∧ x1 ≠ u0 ∧ x1 ≠ u1 ∧ u0 ≠ u1) ∧
      (e ≠ g ∧ e ≠ f0 ∧ e ≠ f1 ∧ g ≠ f0 ∧ g ≠ f1 ∧ f0 ≠ f1) := by
  have : H.Simple := hA.simple
  have hV := hA.finV
  have hE := hA.finE
  have hloop : ∀ e x, ¬ H.IsLink e x x := fun e x h => Graph.Loopless.not_isLoopAt e x h
  have hcard : E(H).ncard + 4 = 2 * V(H).ncard := by omega
  have geo : Geo H x0 x1 u0 u1 e f0 f1 g := ⟨hC.e_link, hf0l, hf1l, hgl⟩
  have hdisj : Disjoint X Y := hC.tree.1.disjoint_of_ne hY.1 (Ne.symm hYX)
  obtain ⟨hx0X, hx1X⟩ := hC.e_mem.2.ends_mem hC.e_link
  obtain ⟨hu0Y, hu1Y⟩ := hg.2.ends_mem hgl
  have heI : e ∈ I := hC.e_mem.1
  have hgI : g ∈ I := hg.1
  have hv : x0 ≠ x1 ∧ x0 ≠ u0 ∧ x0 ≠ u1 ∧ x1 ≠ u0 ∧ x1 ≠ u1 ∧ u0 ≠ u1 :=
    ⟨hC.e_link.ne, fun h => Set.disjoint_left.1 hdisj hx0X (h ▸ hu0Y),
      fun h => Set.disjoint_left.1 hdisj hx0X (h ▸ hu1Y),
      fun h => Set.disjoint_left.1 hdisj hx1X (h ▸ hu0Y),
      fun h => Set.disjoint_left.1 hdisj hx1X (h ▸ hu1Y), hgl.ne⟩
  have hge : e ≠ g := by
    intro h
    subst h
    rcases geo.le.eq_and_eq_or_eq_and_eq geo.lg with ⟨h, -⟩ | ⟨h, -⟩
    · exact hv.2.1 h
    · exact hv.2.2.1 h
  have hef0 : e ≠ f0 := fun h => hf0.2 (h ▸ heI)
  have hef1 : e ≠ f1 := fun h => hf1.2 (h ▸ heI)
  have hgf0 : g ≠ f0 := fun h => hf0.2 (h ▸ hgI)
  have hgf1 : g ≠ f1 := fun h => hf1.2 (h ▸ hgI)
  have hf01 : f0 ≠ f1 := by
    intro h
    subst h
    rcases geo.lf0.eq_and_eq_or_eq_and_eq geo.lf1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact hv.1 h
    · exact hv.2.2.1 h
  have he : e ≠ g ∧ e ≠ f0 ∧ e ≠ f1 ∧ g ≠ f0 ∧ g ≠ f1 ∧ f0 ≠ f1 :=
    ⟨hge, hef0, hef1, hgf0, hgf1, hf01⟩
  have hcls := cls_init hV hE geo hC.ideal.1 hC.card_F (canonical_reach hC) hC.tree hY
    (Ne.symm hYX) hC.e_mem hg hf0 hf1 hunic
  obtain ⟨S, hS, hF⟩ := protected_exchange hV hE hloop hno geo hcard hcls
  obtain ⟨hw, h1, h2⟩ := mwitness_of_cls hV hE geo hcard hv he hS hF
  exact ⟨_, _, hw, h1, h2, hv, he⟩

end Lax630294Proofs.ProtectedExt
