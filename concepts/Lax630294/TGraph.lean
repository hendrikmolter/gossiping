import Lax630294.SpanningStructures

/-!
---
title: T-Graph
type: definition
---

A *`T`-witness* of a multigraph `G` is a pair of spanning trees of `G` that share
at most one edge. A multigraph is a *`T`-graph* if it has a `T`-witness.

# Formalization notes

The two trees are given by their edge sets `T₁` and `T₂`; they may coincide only
when they have at most one edge in common, that is, when `G` has at most two
vertices.
-/

namespace Lax630294.TGraph

open Graph Lax630294.SpanningStructures

variable {α β : Type*}

/-- `T₁, T₂` are spanning trees of `G` sharing at most one edge. -/
def IsTWitness (G : Graph α β) (T₁ T₂ : Set β) : Prop :=
  IsSpanningTree G T₁ ∧ IsSpanningTree G T₂ ∧ (T₁ ∩ T₂).encard ≤ 1

/-- `G` is a `T`-graph: it has a `T`-witness. -/
def IsTGraph (G : Graph α β) : Prop :=
  ∃ T₁ T₂ : Set β, IsTWitness G T₁ T₂

end Lax630294.TGraph
