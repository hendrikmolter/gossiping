import Lax630294.Characterization
import Lax630294Proofs.Sufficiency
import Lax630294Proofs.Necessity

namespace Lax630294Proofs

open Graph Lax630294.Gossiping Lax630294.TGraph Lax630294.MGraph

universe u v

/--
---
conclusion: Lax630294.Characterization.isLabelConnected_iff
---
# Strategy

Sufficiency: a `T`-witness or an `M`-witness is turned into a labeling by gathering secrets along
the first tree or forest, exchanging them (through a hub edge, or around the cycle), and distributing
them along the second one. Necessity: contract the maximal sets supporting two edge-disjoint spanning
trees, bound the number of calls in the quotient from below by `2r - 4`, split into the cases
`2r - 3` edges (a `T`-witness) and `2r - 4` edges (canonical form of the call order, a protected
extension of a four-cycle to an `M`-witness of the quotient, and a lift to the original graph through
a compatible choice of ports).
-/
theorem isLabelConnected_iff {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    IsLabelConnected G ↔ V(G).Subsingleton ∨ IsTGraph G ∨ IsMGraph G :=
  ⟨Necessity.necessity hV hE, Sufficiency.sufficiency hV hE⟩

end Lax630294Proofs
