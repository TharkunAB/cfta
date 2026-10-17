# Actual class leaves, native writers, and paired binder inputs

Proof checkpoint: `5daed6fb`. Starting checkpoint: `05610fde`.
Source main remains `c0cc8a05`, merged at `896b0a1c`.
The full-library goal remains active. Read
[the proof status](notes-proof-status-20261017.md) for the target and limits.
This checkpoint adds no Haskell patch or new production defect.

## Captured ordinary native bodies

`SourceCurrentNativeNodeRowLineage.Lineage` retains one captured node owner,
its actual compiled body, its protected finish, and its literal result.
The same body has a derived ordinary row-compiler trace. Good, readiness,
owner retention, ready-cell retention, and growth into the reader remain
attached to those exact captured states.

`ordinary_body` derives the row compiler from an actual `compileNode` trace,
literal ordinary branch selection, and the two input node shapes. It uses
final-reader history and actual ready-cell retention. It needs no node-cell
premise or internal active-owner history.

`ordinary` starts from the final returned node cell. Actual causal history
supplies its captured body and finish. The theorem derives the row compiler
and full source row and ordered-child lineage. `warm` identifies the exact
captured request from literal lookup and ready demand, under initial Good,
readiness, and key safety. It also proves that the selected and demanded
states equal the reader's native state.

The lineage retains full symbols and joined guards. Original row indices
and child indices identify the earlier child request. Both child-call heaps
grow into the reader heap. A warm row's writer can predate the current node
body. These theorems do not assert ancestry inside that current body.
Other native branch selectors still need their own row-origin consumers.

## Actual leaf queries and historical target slots

`SourceCurrentSharedLeafNativeLineage.Origin` distinguishes the unresolved
direct query branch from a returned complete-request cell with its captured
writer. `request` derives this relation, Good, history, and heap growth from
initial Good and history and an actual completed request trace.

`Origin.returned` excludes the direct branch when both operands are closed.
Closed operands have a native source key. The theorem does not assume a
returned cell separately.

`leaf` follows actual `LeafReads`. It retains the target force, the following
native query, and their exact captured states. The target's historical
`SlotReceipt` follows from the actual force receipt on both misses and hits.
The theorem derives history and Good at the query entry and return, with
chronological growth and the exact native origin. It adds no global Cap,
whole-forest closure, new range plan, or future writer law.

A target can consist of one selected operand. The theorem does not claim
that the target itself must have a native intersection writer. Its historical
target graph retains the actual operand and query schedule that produced it.

## Class phases produce selected native writers

`SourceCurrentClassSelectedChildLineage.Selection` retains the class compiler's
actual selected map, source child index, original class-entry value, exact
preceding and following child schedules, selected node call, and global memo
bundles. It includes the selected source domain, captured Ready data and
native histories, and chronological heap growth.

`class_selected` derives that receipt from actual class reads and initial
class support. `Selection.grows` retains the same receipt at a later growing
heap. `fold_selected` follows the source-indexed right-fold phase decomposition.
It supplies the actual tail, selected class, and later head execution, with
the selected class's child receipts at the complete fold reader.

The selected compiler lookup is not vacuous. Coherent nontrivial class records
compile to an actual child map. Existing selected path domains supply safety
for that map. No global closure is required for unselected siblings.

`Selection.native` handles a selected child whose compiled edit is a leaf.
The original selected domain derives input closedness. The actual force
derives target closedness. These facts exclude the direct native branch.
The theorem returns the exact complete-request cell and captured native
writer at the actual leaf finish. It retains the original class-entry input,
the actual leaf and query receipts, the target's historical slot receipt,
and history at the leaf entry, query entry, and query return.

For an ordinary captured query, the same theorem invokes the native node-row
consumer. It derives the actual row compiler, full guards, source row and
child indices, and historical child calls. The caller supplies only the
literal branch and input-shape facts and the selected returned row/child.
The caller supplies no desired origin law or internal row-compiler trace.

Native cells and `Lineage` remain at the exact leaf finish. The complete fold
reader receives heap growth. The theorem does not assert retention of that
cell into the whole fold's final native table. The class-entry forest is the
actual tail return. It is not identified with the unmodified initial forest.
Nested selected edits still use their node and row receipts; this new native
composition specializes the selected class-child leaf case.

## Paired lexical inputs through actual reserved binders

`SourceCurrentStoredMuBinderChildLineage.Slot` compares two bare references
by their resolved replacement values. Other captures must be the same opaque
value, and both maps must agree on its free names. `Paired` retains these
slot relations in source order. `of_compatible` embeds the older compatibility
relation. `bind` describes exact local shadowing.

`reference` proves equality of the complete repaired execution outcomes for
each indexed variable under paired inputs. It uses coherence and available
left inputs. It does not promise that arbitrary executions are completed.

`publication_extend` consumes two actual publication events and paired outer
environments. Each actual cache miss gives the reserved identity as the
cache's next identity. The cut context and issued-reference ledger prove that
this name is absent from every outer capture's free list. No separate
freshness premise is supplied. Extending both maps at their own reserved
names with the same argument preserves paired inputs. The theorem retains
both actual raw reserved-body builds, self filters, and growth facts.

This is an induction boundary. The events can have different expressions;
the theorem exposes each event's actual calls without relating their body
results. It supplies no argument-availability or full binder-result promise.
The old ordinary `Aligned` law still requires identical capture tails.
General ordinary induction over unequal paired tails, support-scoped depth
and ordinary-probe names, smart cleanup, and older warm winners remain open.

The constructed binder case contains two actual sequential used-binder
publications with unequal outer-reference tails. It proves that no single
identical tail fits the old induction index. A second endpoint proves that
the shifted outer variable reconstructs the same leaf at the exact common
heap. This is not a counterexample to the old `Aligned` theorem, and it does
not establish general binder-result equivalence.

## Validation and preservation

All four final strict source logs are empty. All canonical targets pass.
The 19 public declarations have complete signature, proof or definition,
and axiom output with all eight required print options. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. No omission or printer failure is
accepted.

Five constructed declaration pairs pass. Three have complete proof output.
The two binder endpoints have signature and axiom output. The native fixture
uses an actual ordinary owner, an earlier warm row, and ordinary and productive
Mu children. The leaf fixture constructs a target-slot miss followed by a
same-path hit, with an unselected open sibling. The three-class fixture
constructs the right fold from its own initial numeric room. It selects the
first executed source class and retains the later two-class schedule. It
derives the exact native leaf writer and growth to the complete fold reader.
Its returned rows are nullary. It does not separately instantiate the
conditional ordinary descendant-row law in that combined fixture.

Full pinned Audit passes 3158 jobs and 69534 dependency checks. It replays
only the unchanged unused `inputs` warning in
`InternedFreshOrdinaryClosedCompletion.lean:24:5`. Effective memory maximum
and high are 4 GiB. Swap maximum is zero. Audit peak is 375 MiB.

Evidence is in `restart-evidence/20261018-native-node-lineage/`. Preserve all
failed attempts and older evidence. The baseline has 22377 files, including
3153 old non-Audit Lean files, 242 Haskell files, and 206 active-package files.
The preservation verifier checks 121 frozen manifests with 915 module pins,
two stashes, and three other worktrees. Audit adds only four declared imports.

No Haskell source changed. Reuse the retained strict Nix build, 798 examples
plus golden, Fourmolu, and Cabal-gild validation for source `c0cc8a05`.
Root FINDINGS retains the external repair registry first. Field-pool repair
`b9219b9e` remains merged and validated.

## Remaining proof

General outer-node progress remains the largest mathematical gap. Compose
the phase-relative class inputs, original full fields, selected edits, and
captured native writers into one causal argument. A warm writer can predate
the current body. Prove a decrease or owner separation compatible with
physical request keys and every active ancestor. Include Top inherited data
and nonempty local classes. Whole-value descent and source-only labels do
not suffice.

Complete paired ordinary and binder-result induction and chronological warm
winners. Keep actual issued-reference facts separate from four-table heap
growth. Then complete repeated-pass convergence, recursive callers, frontend
validation, concrete lazy runtime and external adapters, and full public
pipeline correspondence. Keep the optimized interned core and full scope.
