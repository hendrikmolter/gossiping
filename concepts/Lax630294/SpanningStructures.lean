import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Basic

/-!
---
title: Cycles, Spanning Trees and Spanning Forests of a Multigraph
type: definition
---

Let `G` be a multigraph and let `F` be a set of edges of `G`; we identify `F`
with the spanning subgraph of `G` that keeps all vertices of `G` and only the
edges in `F`. The *components* of `F` are the connected components of this
subgraph; every vertex of `G` lies in a component, even if it is incident to no
edge of `F`.

A set `F` of edges is *simple* if it contains no loop and no two parallel edges.
A simple set `F` is *acyclic* if the subgraph it forms has no cycle, and it is a
*tree* if it is acyclic and connected. A *spanning tree* of `G` is a simple set of
edges of `G` forming a tree on all vertices of `G`. A *spanning forest with `k`
components* of `G` is a simple acyclic set of edges of `G` with exactly `k`
components.

A *cycle of length `n ≥ 1`* consists of `n` pairwise distinct vertices
`v₀, …, vₙ₋₁` and `n` pairwise distinct edges `e₀, …, eₙ₋₁` such that `eᵢ` joins
`vᵢ` and `vᵢ₊₁`, with indices taken modulo `n`. Its edge set is `{e₀, …, eₙ₋₁}`.

# Formalization notes

The multigraph is Mathlib's `Graph α β`. Connectivity, components, trees and
acyclicity are taken from Mathlib's theory of simple graphs, applied to
`Graph.toSimpleGraph` of the spanning subgraph `G.restrict F`; this forgets loops
and parallel edges. Requiring `(G.restrict F).Simple` restores them, so that a loop
or a pair of parallel edges in `F` is never accepted as part of a tree or a forest
(these are the cycles of length one and two). Cycles are given by an explicit cyclic
sequence indexed by `ZMod n`; a cycle of length one is a loop and a cycle of length
two is a pair of parallel edges. The number of components is an extended natural number (`ENat.card`), so
that infinitely many components are not mistaken for a finite number.
-/

namespace Lax630294.SpanningStructures

open Graph

variable {α β : Type*}

/-- The simple graph underlying the spanning subgraph of `G` with edge set `F`. -/
abbrev underlying (G : Graph α β) (F : Set β) : SimpleGraph V(G) :=
  (G.restrict F).toSimpleGraph

/-- The vertices of `G` incident to an edge of `F`. -/
def incidentVertices (G : Graph α β) (F : Set β) : Set α :=
  {x | ∃ e ∈ F, G.Inc e x}

/-- `C` is the edge set of a cycle of `G` of some length `n ≥ 1`: there are
pairwise distinct vertices `v 0, …, v (n - 1)` and pairwise distinct edges
`e 0, …, e (n - 1)` such that `e i` links `v i` and `v (i + 1)`, with indices
taken modulo `n`, and `C` consists of these edges. Its length is `C.encard`. -/
def IsCycle (G : Graph α β) (C : Set β) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ (v : ZMod n → α) (e : ZMod n → β),
    Function.Injective v ∧ Function.Injective e ∧
    (∀ i, G.IsLink (e i) (v i) (v (i + 1))) ∧ Set.range e = C

/-- `T` is a spanning tree of `G`. -/
def IsSpanningTree (G : Graph α β) (T : Set β) : Prop :=
  T ⊆ E(G) ∧ (G.restrict T).Simple ∧ (underlying G T).IsTree

/-- `F` is a spanning forest of `G` with exactly `k` components. -/
def IsSpanningForest (G : Graph α β) (F : Set β) (k : ℕ) : Prop :=
  F ⊆ E(G) ∧ (G.restrict F).Simple ∧ (underlying G F).IsAcyclic ∧
    ENat.card (underlying G F).ConnectedComponent = k

end Lax630294.SpanningStructures
