# Independent operation-invariant review

Reviewed on 2026-10-18 at 02:16 CEST. This review used source inspection only. It made no production edits and ran no Lean builds.

## Reviewed source pins

| Module | Initially reviewed SHA256 |
| --- | --- |
| `SourceCurrentNativeOperationHeap` | `8ef0c487aab0c1268694e6293ea405552ed75298c0347eaee250a0a2b4dcfbc7` |
| `SourceCurrentOpenProjectionFields` | `3f104a35875fa6e8687f6cee1ec035480377b16ff6acb29c751427798b3e9a99` |
| `SourceCurrentLowerOperationInvariants` | `cf7bafa2e8f22b30b06df1887024326155b167f7401116032d2431cf410dac97` |
| `SourceCurrentParentOperationInvariants` | `89eb62d992d995c11905475a91d7db9055d2d9a47ca1307a32791f4e256e7394` |

All paths are under `lean/MicroCFTA/`.

## Result

No material mathematical defect was found. The successful execution equations fix the actual intermediate and final states. The proofs derive invariant transport through those states. They do not take final Good, final field availability, final merge residency, or a generic callback preservation law as public inputs.

## Initial assumptions

`NativeOperationHeap.Good` is an initial physical invariant. It includes a valid native machine; physically ready inputs in every native cell; availability or residency of every returned cell value; constructor Ready; valid equality operations; allocated fields for stored edge guards; semantic probe heaps; and the stored cost heap. These are stronger initial conditions than bare constructor coherence.

The native cell key predicate is deliberately `True`. Thus this Good does not establish that every table key denotes its complete captured request, or that a warm result has the intersection language of the current request. The proof uses captured cell input readiness and returned physical availability. This is sufficient for the stated physical invariants. It is not a native result-law proof, key-identity proof, or word-range proof.

`Merge.Stored` means that each entry's key equals its original's reference; both original and result are available; and a closed original has a closed result. It does not supply a Merge language law or a finite Cap. This is a condition on initial completed entries. It is not an assumption about the output of a future call. Empty tables satisfy it without an entry premise. `SharedGood` adds availability of all installed target slots. Each new class constructs empty slots and derives its shared invariant from initial Good and Stored.

`ParentOperationInvariants.parent` requires Stored uniformly, including raw rejection. Its additional live support is conditional on the literal raw `original.contradictory = false`. In that branch it requires initial `FieldAvailable original`, inherited equality Ready, and available children. `FieldAvailable` contains cached original equalities and an actual successful load at the initial operation cache. Validity then derives the loaded value's stored readiness and exact raw readback. The theorem does not require a future load or future local result.

The separate `reject` endpoint needs only initial Good. The Parent rejection branch needs no child availability, inherited Ready, original edge residency, or original field receipt. The general `reduce` and checked `build` endpoints retain their own unconditional initial readiness hypotheses. The review does not claim that those hypotheses are minimal in each internal branch.

## Execution and proof composition

- Native `code` consumes an actual successful bounded executor equation plus structural `Safe`, `Operands`, and code-field certificates. These certificates include quantified continuations. The specialized `node` and `edge` endpoints derive those certificates for the literal request programs from initial request readiness. They do not ask the caller to certify reached internal instructions or returned output invariants.
- The native proof inducts on the consumed successful trace. It handles direct compilation, captured memo evaluation, ready readback, actual primitive work, domain entry, and optional binding. It derives semantic and cost heap preservation from the actual available primitive inputs. Busy, absent, pending, and failed branches are excluded by the successful equation; their exclusion is not a progress theorem.
- Open projection preservation takes actual completed Read, ReadAll, Union, Project, ProjectRows, or Forest graphs. It needs initial semantic/cost heaps and availability or row residency. It imposes no global closedness or selected-domain support because it verifies an already completed graph. Head and projection effects are composed at their actual returned heaps.
- Lower workers derive those graphs from literal successful worker equations. Their Merge case uses the actual allocated call graph derived from that same success. The private child contract is discharged by strict edit-fuel induction. It is not an exported callback oracle. Ordered row reconstruction retains the exact source symbol and complete guard while deriving each reached child and constructor invariant.
- Target slots, target folds, class edits, and the right fold retain the actual successful order. Old operands and slots are transported through derived Keeps. Warm target hits use initial slot availability. Misses derive their own target completion facts from the supplied successful target equation.
- Parent scanning derives the actual primary, secondary, seeded native, conjunction-decision, Required, and class-pass effects. The conjunction helper constructs its own graph and uses uniqueness to align it with the observed successful call. Local precheck validity and operation growth come from the initial loaded and inherited receipts. Parent construction derives the final resident edge at the exact observed checked state.

## Documentation correction

The initially reviewed OpenProjectionFields header said: `No complete projection or future output invariant is supplied as a premise.` Its public projection endpoints do take completed projection graphs. The mathematical statements and lower-worker composition are correct. The module owner corrected the header to state that these are completed-graph preservation results and that the lower worker derives those graphs from successful returns.

Final corrected OpenProjectionFields SHA256: `befa98e79e8e32e1e8bae98ac06eaf5ddb92fcad9c40084ec08361588ad3b2c0`.
The diff from the initial reviewed snapshot changes only this module header. No declaration or proof changed. The initial source and its checks remain preserved. Final owner receipts are `parent-invariants-projection-direct-3` (exit zero, zero-byte log) and `parent-invariants-projection-canonical-3` (exit zero). These receipts were inspected, not rerun. This correction was confirmed at 02:17 CEST.

## Remaining boundaries

These modules prove successful-return preservation. They do not establish an initial successful fuel, arbitrary outer completion, exclusion of busy node owners, or a fresh-call bound. They make no statement about failed, blocked, pending, unresolved, or exhausted final states unless another imported theorem supplies that separate result.

`Effect` returns final Good, constructor Keeps, and equality-operation Grows. It does not itself return a full semantic Frame/Post, global memo validity, a numeric Fits forecast, a native result language law, a guard-origin classification, or a retained-Mu callback congruence. Those conclusions need their separate producers. The modules make no whole-forest closure or finite-Cap assumption.
