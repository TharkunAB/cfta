# Checked ordinary node row meaning

Date: 2026-10-16 05:24 CEST.
Read-only validation HEAD: `7dccd588ddd60bf4daabd6e2b11bcd09050f3579`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeNodeRowsMeaning.lean`.
SHA256: `850ec6f03a0acc4907c2bc65b220f3049333582f297101a50961bfe358f47ab9`.
Length: 277 lines.

## Derived result

The independent original input model remains fixed at `view source holds`. The later execution heap supplies only the actual constructor and physical result facts.

- `row_forest` retains the original physical child order when rows copy children through `inputOf`.
- `node_language` combines actual original physical row readback with `InputMeaning.row_exact`. It derives the unranked original node language from its literal stored rows. `node_rank` derives one actual stored row from each original bounded derivation.
- `joined_inputs` derives the original and valid child scope of each actual hash-joined edge request. It uses the original parent `NodeInputs`, actual row readback, and the model's child-validity law.
- `common_pair` derives actual hash-join membership from two stored rows with a common ranked term. Their accepted term shapes force matching labels. The existing hash-join membership theorem supplies both matching and completeness.
- `rows_law` derives the ordinary parent `NodeLaw` from `All₂ EdgeLaw` for exactly the ordered hash-join requests and their returned edges. Actual `makeNode` normalization handles duplicate edges and dead edges. The theorem uses no parent node law.
- The indexed `Walk` stores actual checked edge `Steps`, each call's heap retention and returned edge residency, and that edge's local contextual law. `Walk.actual` erases the receipts to the actual ordered execution. `Walk.effects` derives residency of all returned edges in the actual final child heap.
- `rows_trace` appends exactly one final node constructor to that actual row walk. `rows_body` derives exact `execute (fuel + 2)` completion, the parent contextual law, heap retention, and output availability. `ordinary_body` exposes the same results for the actual `compileNode` ordinary branch.

The completed state retains the final child operation cache and native memo tables. Only its native machine heap advances for the actual final node constructor.

## Scope

Each reached row call still needs its local contextual `EdgeLaw` and actual physical effects. These are the recursive induction hypotheses. The indexed walk does not supply a same-parent node law, a global future finish invariant, an eager execution equality, or completion of an unexecuted child. The module does not derive all recursive row calls from an arbitrary starting query.

The original physical input heap and its coherent facts are explicit. The original operands are available there. The language laws apply under the original and valid input scope required by `NodeLaw`. No whole-forest closedness or input closedness premise is added. The original model does not change to a model of the final construction heap.

The ordinary branch premise is explicit. Other node branches remain outside this module. Global checked node completion, contextual Mu body induction, cache finish validity, and the complete current query theorem remain separate obligations. The result derives ready heap retention and output availability. It does not assert new cost, annotation, equality-cache validity, or contextual-cache invariants beyond its stated conclusions.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning
```

PASS exit 0, 1077 jobs. The only warning is the existing unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`. This new module has no warning. Log: `node-rows-meaning-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/node-rows-meaning-public-probes-20261016.lean
```

PASS exit 0, no warning. All 11 public theorem axiom reports, 11 public signatures, and 10 kernel checks pass. The maximum axiom set is `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

Kernel checks cover original child order, common-row join completeness, exclusion of different labels, the literal reversed right bucket, all four duplicate requests, empty and singleton actual row walks, the final constructor trace, exact empty-row state retention, and an empty-row parent language proof without recursive edge assumptions.

## Preservation

Only this new proof module and owned evidence files were written. Every frozen proof source, Haskell file, Audit file, repository documentation file, Git state, and sibling file was left unchanged. The source snapshot and updated owned SHA256 manifest are in this directory. No owned process remains.
