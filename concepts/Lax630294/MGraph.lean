import Lax630294.TGraph

/-!
---
title: M-Witness and M-Graph
type: definition
---

An *`M`-witness* of a multigraph `G` consists of pairwise edge-disjoint subgraphs
`C`, `F₁`, `F₂` of `G`, where `C` is a cycle of length at least four and each `Fᵢ`
is a spanning forest of `G` with exactly four components, each of which contains
a vertex of `C`. A multigraph *admits an `M`-witness* if it has one, and it is an
*`M`-graph* if it admits an `M`-witness and is not a `T`-graph.

# Formalization notes

Subgraphs are given by their edge sets, as in the concept of spanning forests.
The requirement that each component of `Fᵢ` contains a vertex of `C` is stated as:
every vertex of `G` is connected in `Fᵢ` to a vertex incident to an edge of `C`.
-/

namespace Lax630294.MGraph

open Graph Lax630294.SpanningStructures Lax630294.TGraph

variable {α β : Type*}

/-- `F` is a spanning forest of `G` with four components, each containing a vertex
of the cycle `C`. -/
def IsFourComponentForestMeeting (G : Graph α β) (C F : Set β) : Prop :=
  IsSpanningForest G F 4 ∧
    ∀ x : V(G), ∃ c : V(G), (c : α) ∈ incidentVertices G C ∧ (underlying G F).Reachable x c

/-- `C, F₁, F₂` is an `M`-witness of `G`. -/
def IsMWitness (G : Graph α β) (C F₁ F₂ : Set β) : Prop :=
  IsCycle G C ∧ 4 ≤ C.encard ∧
  IsFourComponentForestMeeting G C F₁ ∧ IsFourComponentForestMeeting G C F₂ ∧
  Disjoint C F₁ ∧ Disjoint C F₂ ∧ Disjoint F₁ F₂

/-- `G` admits an `M`-witness. -/
def AdmitsMWitness (G : Graph α β) : Prop :=
  ∃ C F₁ F₂ : Set β, IsMWitness G C F₁ F₂

/-- `G` is an `M`-graph: it admits an `M`-witness and is not a `T`-graph. -/
def IsMGraph (G : Graph α β) : Prop :=
  AdmitsMWitness G ∧ ¬ IsTGraph G

end Lax630294.MGraph
