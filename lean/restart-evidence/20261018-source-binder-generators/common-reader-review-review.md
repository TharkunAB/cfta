# Independent common-reader support review

Reviewed on 2026-10-18. No material issue was found.
The reviewed production source is `SourceCurrentCommonReaderBinderSupport.lean`.
Its SHA-256 is `1f1b667d94cb71da9b95ec1a001ba35d88abb1018c7c82c565d9443536b7f2ea`.

The public `node` theorem starts from `Ready`, an available literal node-body Mu, and an existing `WarmSupport` predicate. The recursive premise concerns only an actual child of an original stored body row. It includes a checked strict-size inequality. For every later reached cache and actual effect-free child execution, that premise places the returned child in the old support or identifies it with this same recursive Mu. This is an explicit induction hypothesis. The theorem does not derive it for arbitrary nested Mu children.

The proof constructs the full body execution from initial availability and the sparse self replacement. `StoredReconstruction.execute` produces the actual result, final `Keeps`, and result availability. Exact unfold replay then gives an effect-free unfolding at that final reader. This replay is forward from the returned state. It does not infer earlier history from a later heap.

`StoredNodeExpansion.node_warm` supplies actual complete row calls at the final reader. The physical result row first gives an `Origin`. The survivor equivalence identifies a rebuilt row before filtering. The ordered row relation finds an original source row and its actual child calls. `StoredCallsReplay.replay` then finds the particular original child that returned the selected output child. The strict-size proof applies to that original child. It does not compare a generated child's size with the Mu.

The old support moves forward through `WarmSupport.grows`. The new Mu has exactly the actual replay result as its epsilon successor. The result is ordinary, so it has no epsilon successor. Its physical row children belong to the old support or equal the same Mu. These facts establish the three `WarmSupport` clauses for the enlarged support. Physical Empty agreement and observation equality between two Mu values are not asserted.

The constructed `open_used` theorem has no input premises. It builds `.binder true (.node [.mk 0 false [.var 0,.var 1]])` with an external uninterned marker from the empty heap. The fixture derives `Ready` and availability from source completion and its actual effects. The returned Mu is open, has positive stored-plan binder depth, and uses its local slot. The initial support contains only the primitive marker reference.

The fixture proves that each stored body child is the exact local interned reference or the external marker. Actual reference execution returns the same Mu in the local case and the marker in the other case. This discharges the strict-child premise without a desired parent-output relation. The actual unfold grows the node counter strictly. The final enlarged support and warm replay therefore validate a non-reflexive open-Mu preparation step.

The selected production strict log and fixture strict log are literal zero bytes. The canonical build completes without warnings. Both full probes use all eight required options and pass the hardened output and axiom checks. The fixture retains a private checked proof and a public exact-statement alias. This review runs no Lean command. It adds no public or constructed declaration. It reuses one production pair and one constructed pair.

The result does not settle all resident open Mu records. It does not prove that every strict child satisfies the support-or-self hypothesis. It does not compare changing captures, align different retained writers, or transport observations from an unsupported reader. General source-directed binder construction and recursive execution progress remain open.
