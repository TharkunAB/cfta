# Complete payloads from occurrence compilation

`EqualityLeafProjectionCompileAvailability` proves that occurrence compilation
preserves coherence, stored child availability, and node-to-edge links.
The proof uses actual intermediate cache states for every child, edge, and
node request. Earlier sibling records remain available after later siblings.

`edge_children` uses the exact complete child-payload theorem from
`InternedShallowValues.makeEdge_children`. Thus an original compiled edge
contains the actual ordered child records produced by its original occurrence
forest. Equality of child reference keys alone is not used as a substitute
for complete record equality.

The generic compiler theorem has a local leaf-constructor contract.
`nullary_available` proves that contract for physical nullary declaration
construction. `admitted_leaves` instantiates it for the admitted canonical
source leaf builder. `admitted_forest` therefore derives complete available
output records without a supplied leaf correctness premise.

The facts concern physical cache payloads. They do not by themselves prove
that recursive edits equal edited occurrence compilation or that the fixed
equality schedule terminates on these physical records. They supply the
complete child correspondence premises for that recursive composition.
