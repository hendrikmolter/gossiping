In the Gossiping problem, the edges of a multigraph $G$ are calls between
participants, and one asks for an ordering of the calls, given by a labeling of
the edges with natural numbers, such that every participant learns the secret of
every other participant. Equivalently, the edge-labeled graph must be temporally
connected: for every ordered pair of vertices there is a path whose edge labels
strictly increase. We say that $G$ is *label-connected* if such a labeling exists.

This submission defines the problem and the two structural witnesses of the
classical characterization of label-connected multigraphs. A *$T$-graph* has two
spanning trees sharing at most one edge. An *$M$-graph* is not a $T$-graph but
contains a cycle of length at least four together with two edge-disjoint
spanning forests, each with exactly four components, all of which meet the cycle.
The main statement is that a finite multigraph is label-connected if and only if
it has at most one vertex, is a $T$-graph, or is an $M$-graph.
