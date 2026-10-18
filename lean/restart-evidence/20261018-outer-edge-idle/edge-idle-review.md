# Edge idle at actual reached outer phase entries

Date: 2026-10-18 08:09 CEST.

## Existing result and additive scope

SourceCurrentOuterEdgeIdle.lean already proves initial EdgeIdle and Safe
for all eight literal worker entry points. Safe retains EdgeIdle on done
and excludes edgeMemo busy on failure. It does not exclude edgeMemo absent.
The old source remains byte-identical at SHA256
`4ced480a88de5e01db05579b1019635626d5c7207d626b3d1cadc31357032ba5`.

The new SourceCurrentOuterEdgeIdleReached.lean has SHA256
`b5e0b3e1eaa7e3942f0781c84b11748d979c2180bc32991d7dc6d179b64d2b06`.
It adds two public theorems, step and reached. These consume the actual
Step and Reached of SourceCurrentOuterExecutionAncestry. They transfer
EdgeIdle from the exact first caller to the exact last caller. They need
no Context, operation validity, initial operand support, resources, fuel
comparison or successful enclosing-worker premise.

## Literal prefix proof

Node demand changes only the node result table. The proof derives this
fact from beginNode_components at the actual selected owner. Body entry,
inherited prefix, live child entry and indexed descent keep
the edge result table.

A rows_edge step supplies the actual completed edgeCall. The old literal
Safe theorem derives EdgeIdle at its return. A rows_tail step supplies
both the completed edgeCall and descendants return. The proof composes
the same safety facts in that order. A walk_tail supplies a completed
nodeCall; its old Safe theorem derives idle at the next slot. No semantic
Reads or future sibling result is assumed beyond the actual past done
equations in Step itself. Induction on Reached composes these exact steps.

## Validation

edge-idle-direct-1 checks the immutable source with all linters. Its raw
log is zero bytes. edge-idle-canonical-1 completes the single new target.
edge-idle-public-1 checks and prints both complete signatures, proofs and
axiom lists. All eight required settings are explicit. The component
verifier rejects diagnostics, omissions, sorry and printer failures. It
allows only propext, Classical.choice and Quot.sound.

All selected workers use a five-minute cap. Their effective memory.max
and memory.high are 4294967296, and memory.swap.max is zero. The distinct
runner, worker, readbacks and peak log are retained. No attempt failed.
This component has two public pairs and no constructed pair. It does not
pin or count a shared mutable fixture. No resource queue setting changed.

## Boundary

Reached describes actual unfinished prefixes with completed earlier
siblings. It does not include the terminal failed Parent body state. Such
a failure can keep its selected edge evaluating. The theorem makes no
all-fault-state idle claim. It does not prove edgeMemo absent impossible,
node-owner separation, a fresh-call bound, completion or termination.
No Haskell source or runtime correspondence result changes here.
