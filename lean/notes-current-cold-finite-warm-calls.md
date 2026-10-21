# Finite calls from a constructed source

## Finite calls from a constructed source

Updated: 2026-10-21 23:25 CEST. Proof checkpoint: `15da5fe564`.
Start: `93f3d0ad7a`. Imported main remains `794903b3f`.
Read `lean/notes-current-cold-finite-warm-calls.md`.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls now starts from
a genuine covered source expression, its actual allocation history and a
valid initial cache. It constructs the heap ONCE. It chooses one finite-N
mathematical width and ten common fuel arguments BEFORE the fresh caller.
It invokes the checked finite-call producer once. Zero rounds are included.

The theorem returns the literal SAME actual caller trace and final heap
availability. Every round uses the previous full returned caller, with
the SAME empty inherited value from the final source interner. Its final
finite-tree language is equivalent to the original constructed value for
every ambient environment and finite term. Empty inherited constraints discharge Sat.
The result has no initial caller-packet, future Room or success premise.
It does not reset or widen an existing caller.
Each trace point retains its actual inventory and global memos under the corresponding stage seed.
No C monotonicity across seeds or
Room for the common-outer-fuel schedule is assumed.

This is the strongest combined COLD finite-N semantic theorem. Its source
has 157 lines and one public theorem. Selected ordinary strict2 passes at
default declaration limits with an empty raw log. Accepted FULL2 has 268
logical public TYPE lines: 267 LF characters and no final newline, 21099
Unicode characters and 21121 bytes. Complete check/print TYPE bytes match.
The TYPE has two public FormulaExecutable.formulaDecidableEq occurrences.
All four private/dagger markers are absent. Actual axioms are the standard
three. FULL2 raw has 731663 bytes; SHA256
d84c0cdcd3e399a5f75fea97834a3d651ac25003dce70615e5cc3781edcbce9d.
Audit passes: 3623 jobs /75263 theorem dependencies.

Five actual ROOT Lean/Lake commands are retained: strict1, FULL1, strict2,
FULL2 and Audit1. All exit zero. FULL1 was PUBLIC-TYPE REJECTED despite its
kernel success: two private Formula equality instances remained in its
TYPE, and reader1 metadata failed. Four explicit public instance arguments
fix two header and two matching proof-goal occurrences. The old 153-line
source and 30-line header, corrected 157-line source and 32-line header,
both FULL variants and failed reader output remain. Each source variant
has one FULL. Copies and metadata add no proof jobs. Only the old Audit
inputs warning remains.

The next withoutRedundantEdges inventory is SOURCE-ONLY. It has no public
Lean header or implementation. Root has read its note, contract outline
and some source cuts. Detailed range review and independent review remain
pending. Finite partial nodeCall rounds do not include that public pass.
Practical fixed-width feasibility, public-pass composition, convergence,
solver-contract/exported-table composition and Haskell refinement remain
open. Mathematical reservation bounds do not prove those results.

All old proofs, counterexamples, marked drafts and optimized core remain.
The only old Lean edit is one Audit import. All 268 Haskell files and 207
active package files remain unchanged. No Haskell fix or runtime change
is claimed. FINDINGS keeps the external Haskell repair index FIRST.
Work continues.

lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean: source SHA256 e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.
Sole accepted FULL2: 731663 bytes; SHA256 d84c0cdcd3e399a5f75fea97834a3d651ac25003dce70615e5cc3781edcbce9d.
