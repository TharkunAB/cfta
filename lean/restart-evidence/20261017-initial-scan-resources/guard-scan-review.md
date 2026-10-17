# Current gate and Scan contract review

Reviewed 2026-10-17 12:58 CEST. This is a bounded source review.
The source hashes and exact selected headers are separate artifacts.
No Haskell or older proof source changed in this review.

## Literal gate policy

Operations.hs 255–271 treats Rec and InternedUnion as true before the finite
shortcut. An empty forest path and a missing selected child return false.
A constrained Mu at a closed endpoint returns belowEnd. At an interior path
it returns true. An open unconstrained Mu follows its actual unfolding at
the same path. An unconstrained closed Mu returns false.
An ordinary endpoint tests free variables. Only primary mode also reads
reachesConstrainedMu. Ordered row and class disjunctions retain false-prefix
heap effects and stop at the first true result.

SourceCurrentMuEndpoint and SecondaryTrace retain this constructor schedule.
The secondary module takes a fixed unconstrained predicate. It does not derive
that predicate from Haskell runtime objects. Natural paths require the existing
source adapter. This review does not prove Haskell evaluation demand or cache
publication order. It found no new Haskell defect.

## Initial bounds and support

SecondaryGateResources.class_complete now constructs its own graph from
SemanticReady, CostHeap, available original values, and scalar Fits. It has no
closedness, Cap, or WarmHead premise. The actual repaired unfold decreases
FreeOccurrenceRank; the initial mass bounds that rank. Each ordinary row uses
its original position. Exact class path order determines the scalar schedule.
The node/path/classes APIs verify actual graphs; class_complete constructs one.
The secondary component checks actual source-built cold and warm open-Mu
returns and the closed constrained endpoint/interior distinction.

The old ClassGateCompletion endpoints already construct finite gates, but
choose their worker fuel existentially. GateWorker and GateFields lift the
exact heap effects to checked states and physical fields. Those results do
not alone derive an initial numeric Scan forecast.

## Scan and first-seeded composition

ClassScanCompletion.Ranges is a reached-state native word-range plan. It is
not an initial numeric theorem. Primary false selects the class. Primary true
then secondary true skips it. Primary true then secondary false runs the
literal first-seeded query and current conjunction memo. A true memo result
stops the suffix; a false result passes the exact returned state to the tail.

The first-seeded operand is raw projection. It does not perform the Merge
used by MixedTarget operands. The seeded worker projects the original rest
before the first seed is used as the final fold base, then applies native
queries during unwind. A source-level lazy partition demand theorem remains
separate from this serialized actual-effect graph.

The old SeededWorkerCompletion APIs attach stable bounds to supplied graphs.
They do not by themselves remove SeededRanges. Current numeric Seeded/Scan
composition is owned by the other checkpoint components and is not claimed
by this review. Selected false-secondary certificates permit unrelated open
siblings. Whole-root closure or finite Caps would strengthen that source gate.

## Cap-free native Frame adapter

GeneratedQueryFrameResources.complete constructs its own checked query from
initial Frame, Fits, Room, closed resident queried operands, and valid global
memos. It extends the inventory to the literal query-entry heap. It retains
causal origins and conditional joint laws through the same trace. It does not
ask for input Caps or assert an unconditional output Cap. Numeric count and
mass bounds are proved on that same owned trace. Read-through found no future
trace, desired returned-law, or first-winner substitution premise.

GateGuard and GateFrameResources were also read while root completed them.
Their causal guard proof uses actual stored unfolding. AnnotationHeap alone
would not supply that invariant. Their Frame transport uses exact extension
and unchanged native/domain components. They add no input Cap or closedness.
Their final bytes are owned and registered by root, not this source manifest.
