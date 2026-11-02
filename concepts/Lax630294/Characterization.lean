import Lax630294.Gossiping
import Lax630294.TGraph
import Lax630294.MGraph

/-!
---
title: Characterization of Label-Connected Multigraphs
type: theorem
---

Let `G` be a finite multigraph. Then `G` is a yes-instance of Gossiping
(label-connected) if and only if at least one of the following holds:

1. `G` has at most one vertex;
2. `G` is a `T`-graph;
3. `G` is an `M`-graph.

# Formalization notes

Multigraphs are Mathlib's `Graph α β`; finiteness of the vertex set and of the
edge set is assumed. The definitions of label-connectedness, `T`-graphs and
`M`-graphs are those of the concepts `Gossiping`, `TGraph` and `MGraph`. Loops are
allowed in `G`; they play no role on either side of the equivalence.
-/

namespace Lax630294.Characterization

open Graph Lax630294.Gossiping Lax630294.TGraph Lax630294.MGraph

universe u v

/-- A finite multigraph is label-connected if and only if it has at most one vertex,
is a `T`-graph, or is an `M`-graph. -/
axiom isLabelConnected_iff {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    IsLabelConnected G ↔ V(G).Subsingleton ∨ IsTGraph G ∨ IsMGraph G

end Lax630294.Characterization
