# Independent review of guard edits and class passes

Date: 2026-10-16 23:17 CEST.

No material defect was found in GuardEdit (334 lines) or GuardClassPass (159 lines). All 26 entries in the owner manifest match. Its SHA is `1583c9b13cf7c034764982f744d46e3aa4a7c6d3f2171361a5fe6c779d562f83`. The final logs contain eleven public axiom/full-signature pairs and three integration pairs. They contain no warning, error, sorryAx, or omitted marker. This review reads the frozen sources and existing logs. It does not rerun them or change production.

## Original callback inputs

`GuardEdit.lean:157–187` is the critical selected-child case. The head callback receives the original head value with its original profile. The suffix receives the original tail values and original tail profile at the actual returned heap. The proof transports their availability through the actual first prefix. It passes the newly derived universal slot store to that suffix. It does not pass the edited head result as another callback input.

The row case at lines 193–241 follows the same rule. Each original edge's children use the original input vector. After the current row is rebuilt, the suffix still contains original source edges. This justifies one common leaf envelope for all callbacks. The final output list contains their edited results. Callback multiplicity does not add guard iterations when results are not reused as callback inputs.

Skipped children widen the original profile through `leafLimit_input_ge` at lines 141–156. Empty, empty lists, and the root-list leaf skip retain the stores. Recursive head cases are excluded by the initial finite ordinary domain at lines 122–135. No whole closure premise for unrelated siblings is added.

## Literal rebuilding and stores

The ordinary node case at lines 103–121 applies the guard induction hypothesis and physical effects theorem to the same actual RowsReads. It obtains current coherence, linkage, and returned-row residency at the actual middle heap. GuardConstructors.makeNode then identifies the full actual result, including coherent cache hits. Constructor advance retains the exact slot and lower guard tables.

The row case derives the original loaded field, child result availability, current Ready, and global validity from the same actual child prefix and literal edge constructor. The remaining original edges grow through both prefixes. At lines 232–241, makeEdge receives the complete original raw constraint and actual rebuilt children. The original constraint bound widens to the common leaf vector. No result guard profile is supplied to this step.

`GuardShared.Stored` remains parameterized by the fixed record and captured original forest. Its slot laws are universal in the captured vector. Earlier prefixes can change inventories and checked state without changing that reference forest. The proof passes the actual native and Merge guard stores forward. It does not infer them from domain, language, heap growth, or the older structural stores.

The four public Edit endpoints verify supplied actual annotated reads. Initial safety, physical readiness, domains, semantic cache facts, global validity, old structural stores, and new guard stores remain explicit. There is no range plan, desired output profile, future readiness, or callback-law premise.

## Captured class and right-fold order

`GuardClassPass.lean:70–101` captures exactly the forest at class entry. It initializes only fresh class-local slots. Warm native and Merge tables retain their initial guard laws. The compiled edit's safety and shape follow the actual original class record and current forest. Both captured and original input vectors start at the same G for that class.

The common class result fits `foldLimit G (record.paths.length + 1)`. This is conservative and does not claim the exact native query count. The tail-first recurrence at lines 104–130 first derives guard stores and the profile of the actual smaller tail. The same smaller tail's existing physical receipt supplies its actual inventory, Ready, availability, structural stores, and globals. The head class then captures that returned forest with that produced vector. It does not capture the pre-tail forest.

`passLimit_eq` composes the source-order transforms using the literal class step sum. Addition commutes in this pure equality because every stage iterates the same step function. The execution proof still follows tail before head. Final Empty propagation changes only values and retains both tables and the produced envelope.

## Three integration kernels

The first kernel constructs an actual Empty callback, retains the same NodeReceipt, and proves callback count one. The second constructs two repeated Empty positions and proves count two on the same actual graph. Both callbacks use one common original-input envelope. These parameterized Empty integrations check multiplicity and composition. They are not concrete nonempty-guard constructor fixtures.

The third kernel constructs a complete actual class pass from initial facts and reached machine checks. It retains the same full PassReceipt and both new stores. Its class-step bound is a bound on the supplied original record list, not a desired result law. The principal supplied-read endpoints add no range premise. The kernel uses the existing constructive completion theorem to obtain its reads.

The public and kernel sources enable full explicit arguments, universes, deep terms, proofs, and a 10000000 printing limit. The owner's validation records both unused-variable linters. This review does not make a stronger standalone linter-configuration claim than that evidence records.

## Scope

These are finite ordinary hereditary guard producers. They exclude Mu, explicit union, and references. They do not produce quantitative outer returned-cell row, arity, and guard profiles. Lower native and Merge guard retention alone cannot bound an arbitrary warm outer result. No general outer completion, initial-only root capacity Plan, GHC demand order, HashMap event replay, or whole-library Haskell correspondence is established by this component.
