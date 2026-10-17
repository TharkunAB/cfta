# Active callback reference and ordinary-source induction

Production: SourceCurrentStoredMuActiveChildLineage.lean
SHA: 951dccf930b2ec187ec09e819c33ba337af8d63fc45bb1953208b8bf7ff524ab

## Exact public scope

Compatible requires equal resolved replacements for the two own names. The
outer replacement maps agree on each fixed captured value's free names.
The captured values are complete immutable records. They can contain arbitrary
nested raw or smart Mu values. The two maps need not agree elsewhere. Aliased
names are not excluded. No freshness or noDeep condition is present.

Aligned is a source induction case. It quantifies both own names, both outer
maps, the common Ready reader, available lexical inputs, and available map
replacements. It compares two actual raw source calls that replay at that
reader and their actual warm stored reconstructions. Its conclusion is Related:
physical Empty agreement and every finite open observation in every view.
Rows retain complete symbols and guards. Child relations remain ordered.

StrictChild records the exact source-row membership and child membership.
It also records sizeOf child < sizeOf (.node sourceRows). The ordinary proof
constructs this strict-size witness from these memberships. The induction
hypothesis applies only to these actual strict children. It does not apply
to the enclosing node, an arbitrary future result, or an unrelated smaller
expression. The first provisional interface used a stronger size-only IH;
its successful checks remain evidence but are not selected final checks.

reference proves Aligned for any lexical variable. An active own reference
uses the equal resolved replacement. A fixed captured value uses the repaired
execute_congr theorem and the outer maps' agreement on that capture's free
names. Missing lexical slots return Empty. The proof needs no relation on
returned values and no restriction on captured Mu records.

ordinary proves the complete ordinary-node induction step. It derives every
raw source row's actual warm child build from the actual parent build. Each
original source row has the same raw Empty tests under both own names. This
fact preserves source-row survival through the first makeNode normalization.
The proof expands both stored node reconstructions, including closed opaque
node shortcuts. It then aligns the same original source row in both lists and
uses only the strict child IH for the actual ordered child calls. Related
children derive the second row-survival agreement. Bidirectional row matching
retains full symbols and guards, and gives all finite observations. Available
ordinary outputs in the Normal reader derive physical Empty agreement.
No canonical-order premise is imposed on closed original nodes. No physical
identity of the two reconstructed parents is claimed.

node_complete is the initial reconstruction producer. Its past raw source
calls, actual Contexts, and growth into the initial reader are explicit
component inputs. It replays those calls at that reader and derives both raw
values' availability there. Ready and available replacements construct the
first stored reconstruction. Its actual Keeps transports the inputs for the
second reconstruction at the exact first returned heap. Both calls retain
Keeps, result availability, and local MuPublication Histories. Actual replay
at the second returned heap supplies the common warm calls used by ordinary.
No stored completion, expected result, expected final heap, parent output
relation, Alpha relation, or returned observation is a public input.

## Constructed active case

The fixture constructs a closed productive used Mu from source. Its body is
a union of a nullary leaf and a recursive step. That complete Mu and Empty
are fixed captures. Two actual ordinary source calls use own references 0
and 9. The second call starts at the exact first returned source heap.
Their source rows contain a nested ordinary node that reads the active own
slot, a second direct active reference, and the productive Mu capture. The
source contains a duplicate row and a separate row with an Empty child.
The fixture proves the two raw parent identities differ.

Each replacement map substitutes the same actual captured Mu for its own
name. Ready, input availability, map replacement availability, Contexts, and
growth all follow from the fixture's actual source constructions. The strict
child IH is discharged by reference and one smaller ordinary-source step.
The fixture invokes node_complete to construct both stored calls and their
Histories. It proves the reconstructed left result is a nonempty ordinary
node. The theorem gives both exact common-reader warm replays and Related.
The fixture signature has no successful future call, future heap, result
relation, or induction-hypothesis premise.

The first fixture attempt failed because decide did not unfold the private
source-build constants in the distinct-identity assertion. The next attempt
uses cbv before decide. No different behavior or production defect was found.
All failed snapshots and raw logs remain intact.

## Remaining coupled induction

This module proves the active reference base and the actual ordinary source
induction step. It does not prove Aligned for every source expression. Its
ordinary theorem intentionally retains the proper strict-child IH. The new
producer does not assume this IH for a whole parent or future callback.
The exported case fixes one shared list of complete outer captures while
allowing different own names and compatible outer maps.

An active nested binder can reconstruct a Mu on one side and smart-erase it
on the other. Its raw probe slots introduce further paired names, so the full
binder invariant must also cover the corresponding compatible extended
lexical environments. A warm request may select an older writer with source
syntax different from the current callback. A source-size induction alone
cannot supply that writer law. The required full proof must couple strict
source subcalls with chronological selected-writer histories under compatible
outer environments and the same replacement for the differing own names.
No such chronological binder induction is claimed here.

Union normalization also needs the proved literal and observational fusion
laws. General physical reconstruction/makeUnion commutation is false. This
module does not replace that boundary with ordered Alpha or noDeep premises.
It does not prove complete retained-Mu correspondence or outer termination.

## Validation

The final direct snapshot is direct-7 and its raw log is exactly zero bytes.
The selected canonical-2 target passes 587 jobs. The public group has six
complete explicit signatures, full declaration/proof prints, and axiom reports.
The constructed group has one complete explicit signature and axiom report.
Both groups set linter.all and all seven printer options, including proof
threshold 254, and use #check @. No omission or printer failure occurs.
Only propext, Classical.choice, and Quot.sound occur. The printer-free
constructed check kernels-2 also has a zero-byte raw log.

Each selected worker records effective memory.max=4294967296,
memory.high=4294967296, and memory.swap.max=0 from its own cgroup. Every direct
attempt executes its immutable absolute source snapshot with pinned Lean
4.34.1 and linter.all=true. Both provisional canonical attempts remain in the
component archive. Only canonical-2 and the six-public-pair and one-constructed-pair groups are
selected. No old production source or evidence was changed.
