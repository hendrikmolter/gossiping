import Lax630294Proofs.TSufficiency
import Lax630294Proofs.MSufficiency
import Lax630294.Characterization

namespace Lax630294Proofs.Sufficiency

open Graph Lax630294.Gossiping Lax630294.TGraph Lax630294.MGraph

/-- Sufficiency half of the characterization: a finite multigraph with at most one vertex, or a
`T`-graph, or an `M`-graph is label-connected. -/
theorem sufficiency {α β : Type*} {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (h : V(G).Subsingleton ∨ IsTGraph G ∨ IsMGraph G) : IsLabelConnected G := by
  rcases h with h | h | h
  · exact TSufficiency.subsingleton_sufficiency h
  · exact TSufficiency.tGraph_sufficiency hV h
  · exact MSufficiency.mGraph_sufficiency hV hE h

end Lax630294Proofs.Sufficiency
