# Actual open body and reference origins

Updated 2026-10-18 10:04 CEST. Proof checkpoint: `cf2dc597`.
Starting local checkpoint: `5d321e71`. Main source: `c0cc8a05`.
The full-library goal remains active.

## Completed result

An actual successful reference compiler trace now derives its domain
membership test, exact binding read and correctly ordered child request.
The read keeps the entire checked state unchanged. The child uses exactly
one less instruction. The left and right compiler theorems derive the
interned reference name from the successful trace. They do not assume it.

The actual final reader identifies the earlier captured reference writer.
Its receipt keeps the same evaluating owner, original request, compiler
trace, finish trace, writer heaps and forward growth. It also retains the
resolved child call. That child either executes a direct unresolved
compiler body or has a returned cell with its earlier captured writer.
No history at an internal active owner is an input.

An actual Mu compiler trace now derives the full checked body-entry state
after its literal domain allocation. The proof uses captured Good, the
actual first instruction check and the exact enter result. The actual
child trace derives Good at the body return. Optional-binder execution
keeps both memo tables, so completed child cells remain available at the
final reader. The body receipt keeps the exact entered domain, original
two body inputs, returned value, internal fuel and optional-binder result.

The Mu query theorem needs no closed-operands premise. Its actual selected
Mu branch supplies both source identities. Those identities supply both
tagged memo inputs. The complete outer request therefore has a memo key.
The body retains the direct-or-returned provenance split. Key presence
does not prove machine safety. The actual checked trace retains the
separate instruction safety checks.

`SourceCurrentNativeReferenceOrigins` adds `reference`, `left`, `right`,
`forwarded` and `writer`. `SourceCurrentNativeMuBodyOrigins` adds `Body`,
`trace`, `returned` and `request`. Both modules retain arbitrary recursive
inputs. They add no closedness, Original, BinderFree or finite ordinary
Cap premise to the actual reference or Mu query inverses.

## Remaining work

These results describe actual completed calls and their causal writers.
They do not produce completion from arbitrary raw execution. A current
Good state and available operands alone do not imply a memo key: unresolved
placeholders can also be available. The proof keeps this distinction.

The new reference and Mu body producers can now support general query
ancestry under entered domains. That ancestry must still compose actual
reference calls, swap/reset forwarding, ordinary joins, unions and nested
Mu writers. Ordinary origins must retain both operand row indices, actual
guard conjunction and ordered child pair requests. A row anchored inside
a generated body is not yet a row of an initial query operand.

General retained used-Mu alignment remains open. Causal publication history
identifies the actual earlier stored writer. It does not yet derive the
required relation between that body and the current ordinary callback
under one replacement. Literal row occurrence also keeps retained Mu
opaque. Exposure through such a Mu remains a separate obligation.

Source ancestry must then compose through class folds, Parent and walks.
All active node-owner exclusions, a finite fresh-call bound or another
well-founded measure, general outer completion and repeated convergence
remain open. Equality-operation resources, host Int adequacy and public
Haskell correspondence remain separate obligations.

The strongest general recursive outer claim is unchanged: under the stated
initial semantic and scheduled resource conditions, a successful recursive
normalization preserves exactly the accepted terms when inherited
constraints are empty. This is partial correctness, not general termination.

## Verification

Full Audit passes 3283 jobs and 71419 dependency checks. All nine production
declarations pass full statement, proof and axiom checks with all eight
printing options. Both selected production strict logs are empty.
Canonical builds and Audit retain only the existing ClosedCompletion
unused-variable warning. Independent review finds no material issue.
Jobs use 4 GiB maximum/high limits and zero swap. Successful root jobs
peak at no more than 385 MiB.

The two source-built integration theorems pass full checks in the third
probe group. The first constructs its own source, semantic state and
publication history. Its actual closed Mu call enters an open reference
request, swaps to the right-reference branch and reads the bound value.
The same witness applies the new Mu body query theorem. The second uses
an unresolved placeholder and Empty. It has no memo key and completes
directly in one checked step with the same full state. Both return Empty.
They do not establish nonempty output or general completion.

Four component manifests pin 166 entries. All 29233 baseline tracked files
remain present. All 3280 older non-Audit Lean sources, 242 Haskell files
and 206 active package files retain their bytes. Two stashes and three
other worktrees retain their metadata. Preservation checks 154 frozen
manifests with 1040 module entries.
Earlier linter-warning attempts remain recorded. They are not selected
as clean strict checks.

Evidence is in `lean/restart-evidence/20261018-open-domain-reference-origins/`.
No Haskell source changes and no new executable defect is asserted.
FINDINGS preserves the external repair registry first. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Publication awaits the existing
direct approval. No push is retried. The full-library goal remains active.
