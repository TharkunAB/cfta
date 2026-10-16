# Finite ordinary projection validation

Validated on 2026-10-16 at 16:37 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryProjection.lean`.
SHA256: `6ab6a25212466138ca92212acaf23de5a34df1ccf9a9770e16eb0861943af0ee`.
The source has 178 lines and six public theorems.

`projection-direct-3.log` records direct pinned Lean exit 0 with no warnings.
Root observed canonical terminal exit 0, 1115 jobs, in `projection-build-1.log`.
The canonical log contains only the historical unused-input dependency warning.
`projection-checks-4.log` records final canonical-imported direct Lean exit 0 with no warnings.
It contains six public axiom/full-signature pairs and four integration pairs.
Dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
No final declaration uses `sorryAx`.

Public APIs: read_domain, readAll_domain, union_domain, project, rows, forest.
All are generic in Symbol and Guard. Ordinary Read and ordered ReadAll derive
literal domain rows and exact heap identity. Union uses actual ordered row
reads and actual makeNode readback. Project and ProjectRows use mutual graph
induction. The selected child comes from the exact signed select result.
Prefix Keeps and semantic readiness derive the actual tail residency.
The recursive-head case is impossible from the input domain. Forest retains
its distinct root-union, missing-position, and selected-child branches.

Project, rows, and forest return Keeps, SemanticReady, result availability,
and result domain at the same actual returned heap. Initial domain and
availability derive all needed cached closedness internally. No output-domain,
closed-input, semantic callback, or future-state invariant is supplied.
Guards and equality classes have no restriction. No height bound is claimed.
No native execution, merge cache closure, target closure, or general constrained
outer completion theorem is claimed by this module.

The integration checks cover literal ordinary Read with unchanged heap,
negative-index missing projection, actual full-guard/nonempty-equality root
ReadAll then makeNode, and a second actual forest projection at the first
returned heap using its derived readiness and residency.

Earlier logs retain corrected errors. projection-direct-1.log records a tuple
proof grouping error. projection-direct-2.log records a mistyped executable
path (exit 127). projection-checks-1/2.log record external check elaboration
errors; their partial declarations are not accepted evidence. The isolated
projection-checks-3.log passed; projection-checks-4.log repeats the final checks
against canonical imported objects. The production source stayed unchanged
from its direct green result through all final validation.

No older proof, Audit, documentation, Haskell, or Git state was edited.
This task ran no Lake command. No compiled artifact is stored in this evidence.
