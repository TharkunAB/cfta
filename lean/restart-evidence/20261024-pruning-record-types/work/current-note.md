# Type-position recording and exact callback observations

Updated: 2026-10-24. Start: `824808fb47ccd3ad7a4da2ff423f05c1dc8fa804`.
Main: `c4f7319acf84213fccc8ea389487d4176e4f0b62`, incorporated.
Proof: `83926524d89062128512a9d43814543dd921f953`.

## Checked helper behavior

SourcePruningPositions implements three pure functions from Pruning.hs.
It uses the existing Fragment, PartialTerm, Term and full refined Symbol.
Ordinary app/4 and filter/2 tests compare the complete label against Top.
Other labels retain their refinements and take the source fallback branch.

Type-position holes insert their raw ID through canonicalIds. Program-position
holes retain the incoming type list. Type nodes traverse all children as types.
The app branch retains the nested right folds: the annotation and marker use
true; the function and argument use false. The filter branch records its program
child before its annotation in the resulting nested expression. Other shapes
traverse all children as types. Literal folds are expanded into the same nested
calls where Lean needs explicit structural descent. Generic children retain foldr.

programHoles preserves raw IDs, order and duplicates. It returns no holes below
a type position. For an application, function holes precede argument holes.
A filter contributes only its program child. The repeated-hole theorem retains
both occurrences. Other shapes contribute no program holes.

openProgram replaces a type hole with ordinary ?, a program hole with ordinary
?program# followed by its Nat decimal ID, and truncation with ordinary Mu.
Concrete app/filter nodes use the same mixed child positions. Other concrete
nodes map every child as a type. Hole and truncation branches ignore children,
as the source does even for malformed partial-term inputs. This is openProgram.
The distinct openTypes function and its runtime-error exclusion remain open.

Insertion has exact membership, uniqueness and ascending-order laws. The module
does not prove global canonicality preservation for the complete helper.
Native IntSet extraction requires ascending unique input lists and that remaining
preservation argument. An arbitrary List Nat field does not encode that invariant.
Native nonnegative representable Int IDs, show/Text formatting and symbol
interning remain separate correspondence obligations.

## Checked callback behavior

SourcePruningRecordTypes uses the actual enumeration Oracle and State. Its four
metadata fields retain ordered pending groups, type IDs, open-program IDs and
opaque caller typing. Type and open lists represent source set observations;
pending groups and their entries retain their source order and duplicates.

The pure typesLast selector gives pending candidates priority, including type
holes waited on by a pending group. If no pending candidate exists, it chooses
the first supplied candidate outside the type set. It keeps candidate order.
atTypes is exactly raw type membership and absence of that raw ID from every
pending pair. These equations do not prove whole-driver stopping correctness.

updatedTypes tests the incoming raw current ID against the incoming type set.
For a fragment, it invokes the concrete checked helper. For a pre-expansion
node event, it retains the original types. No representative lookup is inserted.

An empty template catalog skips the oracle and performs the pure type update.
It returns false and retains pending, open and typing. This is different from
calling oracle with an empty catalog: that oracle can still read the fragment
and resume pending groups. A nonempty catalog calls the actual SourcePruningOracle
on the original pending/current/input. The final metadata uses its actual pending
result and flag, the computed types, and the original open and typing. This
reconstruction also applies when the prune flag is true. A pre-expansion event
returns false and the complete original metadata for every catalog.

Every successful call has the exact computed types and unchanged open/typing.
With representative totality, a successful call preserves the complete modeled
compression frame. This retains counter, values, obligations, both ancestry
fields and exact root identities and stored root sizes through Reaches.
It permits different parent paths in the two representative forests.

Related incoming states, identical metadata/inputs and independent successful
fuel bounds yield equal complete Bool/Metadata results and related final states.
Increasing fuel retains the exact result and actual final State. From one actual
success and a related input, the transport theorem constructs a finite matching
run and its final frame. It does not assume the desired right success, equal
fuel across forests, canonical current, Safe, completion or pruning soundness.
Intermediate states come from the actual concrete oracle action.

## Main claim and remaining work

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined result. Covered closed construction, a valid initial cache, original
guard-allocation history and the empty inherited payload yield a finite trace
of repeated modeled node calls. The theorem derives sufficient mathematical
identifier width and fuel. The final node has exactly the same finite-tree
language. It excludes withoutRedundantEdges and does not prove convergence.
The callback results above add observation guarantees, not a larger H6 theorem.

The next prerequisite for typedTypes is a concrete native node view. narrow and
emptyAt exempt Mu alone. The renderer boundary also includes union. The existing
enumeration graph combines those tags and cannot implement the Mu-only test.
The retained plan uses the existing interned Value, repaired nodeEdges reader
and actual smart makeNode constructor. It preserves genuine rows and cache
history. Smart construction removes edges with empty children; the existing
live-row theorem can discharge this filtering for genuine closed reader output.
The enumeration-ID to stored-Value/history bridge remains a separate obligation.

Complete typedTypes must retain the fresh second partial render, actual extend,
ascending unique raw open IDs, every hole read before pure or, aliases and all
compression when rejection returns earlier metadata. It must use the concrete
node-view behavior. An arbitrary emptyAt callback would assume this obligation.

Full canonical mutation histories, selected-current protection, cached scheduling,
semantic pruning, phase 4, practical native width, resource use, native runtime
and solver correspondence, and convergence remain open. H23 stays queued.
Older constructor and equality targets remain. The full goal is active and
incomplete. No Haskell source changes in this checkpoint. FINDINGS keeps the
external repair index first: five fixes are on main; the trailing-hash name fix
at 07229ca7f3 still needs an upstream import.

## Validation and retained evidence

Both final 209-line modules pass Lean 4.34.1 with warnings as errors and all
linters. The installed target builds. Aggregate Audit passes 3678 jobs and 76071
dependency checks, with the older unused-variable warning in
InternedFreshOrdinaryClosedCompletion.lean:24 and no new-source warning.
All 40 public signatures and 32 axiom reports were read. The reports use only
propext, Classical.choice and Quot.sound; some use proper subsets.
No project axiom or proof-limit override is added.

Evidence is in restart-evidence/20261024-pruning-record-types. It retains all six
helper attempts and both callback attempts, exact final inputs, raw logs and
resource receipts. The first helper attempt failed on a staging import path
before elaboration. Later attempts retain the termination and equation-proof
errors. Explicit recursive calls preserve the recurrences; explicit eq_def
rewrites prove the generic type-node equations. Callback repairs change only
proofs: split the conditional bind and rewrite under the existential.

The frozen 188-line helper proposal, complete source cuts and independent
reviews remain. The native-node-view plan records exact source pins and the
next proof route. Previous-publication retains the prior checkpoint's post-seal
publication receipts. The preservation verifier checks every baseline file and
mode, the nine exact documentation insertions and the single Audit import.
It checks all retained hashes, final source identity, actual public declarations,
axiom reports, strict logs and 4 GiB/no-swap receipts. It does not prove native
extraction. Earlier sealed evidence remains unchanged.
