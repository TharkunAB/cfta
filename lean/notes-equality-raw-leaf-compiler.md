# Finite raw leaf compilation and projection union

`EqualityRawLeafInventory` generates exact initial raw guards and all later
canonical conjunctions. Source admission filters this finite list. The
inventory length is at most the initial guard count plus two raised to the
original outer atom count. `intersect_exact` proves closure under both
source branches. `leaf_progress` derives the local projected-edit measure.
Initial syntax remains unchanged until the source normalizes a product.

`EqualityRawLeafCompiler` builds any selected predicate over this inventory.
`build_keys` proves exact complete outgoing keys. `meet_read` gives the
actual physical source intersection's finite-carrier readback. `meet_record`
proves equality of complete physical records in a common completed cache.
`represented_meet` first executes the actual source meet. It then constructs
a finite cache extension that replays the compiled abstract result as the
already-returned source value. All payload invariants follow from execution.
The builder also supplies ordinary inputs and allocation-free requirements.

`EqualityOrdinaryReadback` derives reconstruction of an actual ordinary
value from its own outgoing records. Completed node and ordinary union
constructors preserve this property. `keys_ext` derives complete-record
equality from equal resident outgoing-key sets.

`EqualityRawLeafUnion` uses those results for actual projection union.
`union_keys` accounts for empty operands and duplicate node identities.
`union_record` gives exact complete-record correspondence with the finite
predicate union. `union_completed` executes the actual union first and
constructs a finite later cache that represents that exact result.

The finite preparation is part of the correspondence proof. It does not
assert that the runtime executes those additional requests or that one
finite cache contains every possible future request. Whole recursive path
and fixed-schedule composition remain separate obligations.
