# Independent review: literal eight-family outer worker

Reviewed 2026-10-16 14:18 CEST. Verdict: no material defect found. Source `lean/MicroCFTA/SourceCurrentAllocatedPartialWorker.lean`, SHA256 ed3921e17d46e64b5bdae1c5bcdb00312d1c81549a13aac3fb63d868f8f414d6. The imported canonical source has 248 lines and ten public protocol lemmas. This is an executable bounded serial observer. It is not a general constrained-termination theorem or a proof of GHC demand order.

## Literal source order

The worker preserves the schedule in `cfta/src/Data/CFTA/Equality/Operations.hs:80–96,143–145`. `nodeCall:62–72` and `edgeCall:99–108` run begin/publish/demand first. A ready cell skips the body and every lower bound. Evaluation uses the stored winning request and the handle returned by that same begin. Only body success enters finish. Busy and absent have separate faults at the actual post-begin caller state. Failed evaluation does not finish or reset the owner. The full lower diagnostic is retained.

The node body keeps Empty and InternedUnion unchanged (`:78–79`), reports unexpected references (`:80`), and executes actual Mu reconstruction (`:81–88`). A pending Mu retains the exact constructor heap in both the diagnostic and advanced Caller. Operations, fourth, merge, and both outer result tables remain exact. The Mu pattern in Haskell reconstructs through createMu (`Interned/Type.hs:671–676`); no identity shortcut replaces it. Under valid probe invariants, the older physical receipt can derive cleanup and the unchanged heap separately.

Ordinary nodes call rows, then the literal RawRebuild.modify with the original node, original ordered rows, and returned ordered rows (`:89–95`). The checked modify branch retains its physical ordered-identity fast path. It does not substitute a language-equivalent node or sort the input traversal.

`edgeBody:111–117` invokes the literal ParentWorker once with the winning original edge's symbol, full raw guard, inherited value, children, and current checked/fourth/merge state. The full parent fault is retained. Checked and both warm lower memos are installed at the literal parent return, while both outer tables are retained. No old scoped execution is used.

`rows:120–131` executes each original edge call, descendants of its RETURNED edge, and then the suffix at that actual descendant return. A parent sentinel can change the raw field and child list. The worker correctly gives those returned fields and children to descendants. It does not reuse the original edge's children for that phase.

`descendants:135–148` computes one inherited prefix at the current operations. Error and missing retain its actual returned operations and remain distinct. A successful payload enters children at that exact state. The raw edge rebuild uses the returned edge's full raw guard and the child result. It is raw setChildren, not a repeated MkEdge check.

`children:151–156` erases the current child slots on inherited contradiction without child calls. A live payload starts walk at index zero. `walk:159–171` computes each literal descent at its current Caller, calls the descended request there, then passes the returned Caller to the next index. It neither precomputes all inherited payloads from the initial state nor resets warm tables between siblings.

## Bounds, owners, and contract limits

The source conjunction admission budget remains fixed. The nine lower execution bounds are separate from the outer fuel. The mutual termination pairs use nodeCall phase 3, nodeBody/rows/descendants phase 2, children phase 1, and walk phase 0. Ordinary node bodies and nonempty rows/walks consume outer fuel before recursion. Edge body and terminal branches can run at fuel zero. In particular, terminal or ready calls are not rejected merely because body fuel is zero.

The definition's totality follows these bounded recursion equations. It does not prove that every intended unbounded source call has a successful bound. A body failure retains all actual changes, including an evaluating owner. Exact owner-cell physical guarantees for arbitrary nested success/failure require the legitimate protocol/frame invariant; the raw total function also admits malformed tables. No theorem here turns busy into a successful graph, assumes ancestor completion, or interprets an incomplete observation as an empty language.

The ten public lemmas expose actual begin/body equations. They contain no physical/semantic result law or future completion callback. They show exact branch behavior and same selected finish handle. They do not supply a body completion theorem.

A raw successful Parent/Local worker cannot be converted unconditionally to every physical graph merely by unfolding. The Actual layer needs the legitimate initial Context, field readback/residency, and reached range checks that discharge native physical plans. Therefore a whole-worker raw-success-to-physical-graph endpoint must retain those initial facts or derive them along its actual trace. Do not import historical primary reads or claim an unconditional physical converse from this definition alone. Stable graph-to-execution completion proves finite supplied graph realizability, not general graph existence.

## Imported checks

All ten public axiom/full-signature pairs pass, with only propext, Classical.choice, and Quot.sound. Twelve kernel examples pass with no warnings:

1. A literal returned node cell gives a same-whole-Caller hit at zero outer and lower bounds.
2. A literal returned edge cell likewise skips the parent at zero bounds.
3. A suspended Empty winner overrides the later candidate and finishes its selected cell with the exact original request retained.
4. A suspended ordinary winner exhausted at body fuel zero stays evaluating at its actual selected cell.
5. Busy node and absent edge observations remain distinct incomplete results.
6. A rejected winning edge runs the actual parent sentinel and finishes the original selected handle.
7. Prefix error retains its returned operation state and skips children.
8. Missing inherited payload remains a distinct result at that same prefix state.
9. Contradiction erases slots at zero fuel and preserves list length, including an empty list.
10. Mu pending retains its literal partial heap and all other Caller components.
11. Rows use the narrowed returned edge, descendant return, and then suffix in that order.
12. Walk uses current-state indexed descent and passes its node return to the next slot.

The first draft probe used rfl for well-founded recursive equations at three points. The corrected probe uses the public defining equations. The first failure log is retained; no proof source changed.

## Next proof boundary

The eight-family driver is now implemented. The earlier `outer-worker-plan.md` is the prior design inventory, not a statement that the driver is still absent. Next compose supplied successful execution with same-graph strict Reads and PartialActual under legitimate initial Context/reached checks; combine the new finite-graph completion and unconditional successful monotonicity/uniqueness proofs when frozen. Preserve computed inventories and all returned states during alignment. General outer completion needs a separate decreasing-domain argument. Unequal-length classes and repeated-pass convergence remain open. Host publication, GHC black holes/forcing, actual global event execution, concrete containers, and machine identities remain external transfers.

No older proof, Haskell file, Audit, Git state, or prior evidence was edited. This independent review runs direct pinned Lean only and holds no canonical or Haskell slot. Source is unchanged, so the existing 798 examples plus golden are reused.
