# Exact recursive values through class folds

Checked on 2026-10-19 at 11:24 CEST.

The production source is `lean/MicroCFTA/SourceCurrentClassFoldRecursiveValueOrigins.lean`.
Its SHA256 is `575bcd4e7094747ef30d139577598b8b40be466a5f1acf87caa4845940ccc125`.
The four public producers are `children`, `list`, `class_sources`, and `fold`.
The module imports the checked node producer at SHA256
`64d2457c480ad16aa2d902522e40b61794a520770e9f97b3e5b014fdb13061d8`.

An actual recursive output occurrence retains the exact complete Value.
The source arm keeps the same forest slot and the same child-position path.
The event arm keeps an actual native or Head event and a residual literal
occurrence of that same Value. The proof reuses the existing ChildEvent,
ListEvent, ClassEvent, and FoldEvent relations. It adds no event hierarchy.
The existing ListEvent includes the exact indexed child Slice. FoldEvent
retains each actual later head graph and the completed tail before a head event.

The children proof follows the actual ordered dispatch. An unselected child
retains its literal input. A selected child uses the new node producer. Earlier
selected children derive the next readiness, available inputs, memo validity,
and native History through their actual completed effects. A native event in
another forest slot cannot justify the selected slot.

The class proof uses that class's own captured input forest and base heap.
Coherence, active paths, and the initial domains derive compiled edit safety.
The right-fold proof verifies the completed tail before applying the current
head class. This derives the actual phase forest, readiness, inventory,
availability, domains, memo support, and History. A source in the phase input
then recurses through the tail at the same positions and with the exact same
recursive Value. No field-only RowOrigin composition is used.

The initial physical, domain, and memo support remains explicit. The theorem uses
actual completed read graphs. It does not establish that those calls finish.
It does not require a false gate, Required.Origin, a prepared-to-phase forest
identity, or a supplied ancestry law. The Occurs relation crosses ordinary
rows only. It does not cross Mu bodies, union members, or observational
unfolding. The event arm is value membership. It does not assert a completed
projection or read of the entire event value. An indexed selected-reader Flow
remains a separate obligation. No mass decrease, renewal bound, termination,
or Haskell correspondence claim follows from this result alone.

The first strict attempt passed with a literal zero-byte log. The canonical
build passed with 1480 jobs and only the unchanged ClosedCompletion unused-input
warning. The full public group contains four #check @, #print, and #print axioms
triples. It passed all eight printer options, full proof output, the standard
three-axiom check, and omission checks. Every owned Lean job used the effective
4 GiB / 5 minute wrapper, memory.high equal to memory.max, and swap disabled.

This component owns four public pairs, zero constructed pairs, zero auxiliary
pairs, and three capped Lean runs. The source-built recursive fixture belongs
to a separate component. No prior source or frozen evidence file was changed.
