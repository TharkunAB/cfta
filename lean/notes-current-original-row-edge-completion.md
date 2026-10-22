# Semantic completion for original parent rows

Updated: 2026-10-22 03:09 CEST. Proof checkpoint: `26a01918be8b5a4b2232dbabe3d1ccb8b51a14da`. Start: `47c597a8e39cb82aa158a9fca104ed41b24849ef`.

edge_complete consumes one actual source heap and its Facts, two parent
values with OriginalInput witnesses, Available at that SAME source, empty
free lists, and literal row memberships in those parent values.
It derives Completes for edgeSemantic at the exact emptyDomain request
using those two edge records. This is generic in Symbol and Guard with
arbitrary holds. The parent values may be the same. The theorem requires
no equality of row symbols, semantic success, native success or caller
FreeCorrect oracle. Source Facts supply the view's free-correct law.

Completes states that some semantic interpreter fuel returns an ok result.
The proof uses finite-input bounds and the direct-row eventual execution
endpoint. It binds the OriginalInput witness to the actual available
parent by payload readback. Closed Mu values do not establish
closedness of every nested parent or arbitrary generated parent.

Selected source: 81 lines, SHA `646095a73f7927c820752de30b47275abf879783760d54f8c31611b93e35feb0`.
Selected clean strict: `original-row-edge-completion-strict-1`. Sole selected FULL: `original-row-edge-completion-public-1`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains 149353 raw bytes. The theorem check/print TYPE bytes match.
edge_complete TYPE: 31 logical lines, 30 LF, 2853 bytes, 2825 characters.
edge_complete actual axioms: Classical.choice, Quot.sound, propext.
The complete public theorem TYPE was read by root and an independent reviewer.
All four private markers and recorded helper names are absent from TYPE.
Private body names are permitted. The complete proof body remains retained;
no whole manual body read is claimed.

The actual ledger has 3 Lean/Lake commands:
2 source and 1 Audit commands,
0 failed commands, 0
warned source exit-zero commands and 0
rejected PUBLIC TYPE commands. Actual inputs, raw logs and exact repairs
remain. Metadata work creates no proof command. Audit passes with
3628 jobs and 75379 theorem
dependencies. The actual warning log remains. No seal or publication
success is claimed by this document writer.

The theorem can discharge a semantic completion premise only after a
consumer identifies the same actual original closed parents and rows.
Native readiness, admission, WordRanges and actual execution still need
separate producers. No physical language iff, whole same-symbol scan,
cache rebasing, cluster reconstruction, the public Mu branch or full
withoutRedundantEdges result is produced by this theorem.
H6 constructed_node_calls remains the strongest combined semantic result.
Convergence, practical host width, external solver contracts/exported
tables and Haskell refinement remain open. No Haskell fix or runtime
change is added. The whole formalization goal stays active and incomplete.

Preservation covers all 81460 starting files/modes, 298 baseline Haskell
files and 207 active package files. Additional H11 Haskell archive copies
must match pinned baseline live-source bytes and remain under H11.
All old proof components, drafts, counterexamples, reproducers and
optimized code remain. Only the Audit import and nine additive prefixes
may change old files; every old text has an exact inverse.
The original Audit has 3116 lines and SHA d88c464169937b31eef6302946a736116e9449e14fdb965ec23ea49eb05bb769.
FINDINGS keeps the external repair index FIRST. The field-pool repair in
PR #65 and typing-documentation repair in PR #97 remain fixed.
No new Haskell repair is required by this checkpoint.
