import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic

/-!
---
title: The Gossiping Problem
type: definition
---

Let `G` be a multigraph. A *labeling* assigns a natural number to every edge.
A *strict temporal path* from `u` to `v` is a path from `u` to `v` in `G` whose
edge labels strictly increase in traversal order; the path of length zero is
allowed. The labeled graph is *temporally connected* if, for every ordered pair
of vertices `u, v`, there is a strict temporal path from `u` to `v`. The instance
`G` of Gossiping is a *yes-instance* if some labeling makes `G` temporally
connected.

Interpreting each edge as a call between its endpoints and each label as the
time of the call, a labeling is an ordering of the calls, and it is temporally
connected exactly when every participant learns every secret.

# Formalization notes

Multigraphs are Mathlib's `Graph α β`, with vertex type `α` and edge type `β`;
parallel edges and loops are allowed, and `G.IsLink e x y` states that the edge
`e` has the ends `x` and `y`. Finiteness is not part of the definition and is
assumed where it matters. Loops never lie on a path, so they do not influence
the answer. Labels are taken in `ℕ`; only their relative order matters. A path
of length `k` is given by its `k + 1` pairwise distinct vertices `x 0, …, x k`
and its `k` edges `e 0, …, e (k - 1)`, where `e i` links `x i` and `x (i + 1)`.
A graph with at most one vertex is a yes-instance, since only paths of length
zero are required.
-/

namespace Lax630294.Gossiping

open Graph

variable {α β : Type*}

/-- A strict temporal path from `u` to `v` with respect to the labeling `ℓ`: a path
of some length `k` whose edge labels strictly increase along the path. -/
def HasTemporalPath (G : Graph α β) (ℓ : β → ℕ) (u v : α) : Prop :=
  ∃ (k : ℕ) (x : Fin (k + 1) → α) (e : Fin k → β),
    x 0 = u ∧ x (Fin.last k) = v ∧ Function.Injective x ∧
    (∀ i : Fin k, G.IsLink (e i) (x i.castSucc) (x i.succ)) ∧
    StrictMono (fun i => ℓ (e i))

/-- The labeling `ℓ` makes `G` temporally connected: every vertex reaches every
vertex by a strict temporal path. -/
def IsTemporallyConnected (G : Graph α β) (ℓ : β → ℕ) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), HasTemporalPath G ℓ u v

/-- `G` is label-connected, i.e. a yes-instance of Gossiping: some labeling makes it temporally connected. -/
def IsLabelConnected (G : Graph α β) : Prop :=
  ∃ ℓ : β → ℕ, IsTemporallyConnected G ℓ

end Lax630294.Gossiping
