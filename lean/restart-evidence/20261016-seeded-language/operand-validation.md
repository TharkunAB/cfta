# Checked seeded operand validation

Date: 2026-10-16 07:57 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedSeededOperandLanguage.lean`.
Source SHA256: `2d191adfef1d0e17b085f43c10c934be60ec9b274259b1d4a2730b9ff050021f`.

## Exported contracts

Namespace: `MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage`.

`Operand.effects u anchor anchorSemantic anchorReady actual good ready
scoped idle available growth supported` derives, at the literal actual
operand result and complete returned checked state:

- `Good`;
- physical `Effects`, including semantic heap validity, stored `CostHeap`,
  equality-operation validity, loaded field coverage, and operation growth;
- native machine `Extension`;
- scoped native memo tables and idle status;
- returned value availability and an empty free-reference list.

The proof obtains supported finite operand completion and applies
`SourceCurrentAllocatedSeededQuery.Operand.unique`. It does not replace
the actual operand state with a chosen final state.

`Operand.included u anchor anchorSemantic anchorReady actual ready
available growth supported nonroot holds ambient symbol terms part
accepted selected` proves independent physical meaning of the selected
subtree in the actual result. The original forest acceptance and literal
signed-path lookup remain explicit. The proof uses the actual operand's
`SourceEqualityProjectionGraph.Forest` receipt and
`SourceCurrentSecondaryProjectionLanguage.forest_included`.

Neither theorem requires unrelated original siblings to be closed.
`PathSupport` retains its actual natural-path witness and gate anchor.
The inclusion endpoint requires a nonempty path. It does not transfer the
special forest-root union case to selected-subtree inclusion.

These endpoints do not execute a native intersection or prove a whole
seeded fold. No contextual cache or result-language law is a premise.
They do not establish GHC forcing order or global unsafe-IO behavior.

## Commands and results

Direct source check:

```sh
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedSeededOperandLanguage.lean
```

Terminal 0, no warnings. Log: `operand-direct-2.log`.
The first direct log retains a repaired constructor-pattern binder error.

Focused canonical check:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage
```

Terminal 0, 1185 jobs. Log: `operand-build.log`.
Only the preexisting unused `inputs` warning appears.
The canonical build slot was released to `required_memos` immediately.

Direct public and kernel checks:

```sh
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-seeded-language/operand-publicprobes.lean
```

Terminal 0, no warnings. Log: `operand-publicprobes-2.log`.
Two public axiom checks, two full signatures, and six kernel examples pass.
The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The first probe log retains a repaired local name ambiguity.

The examples construct a literal selected-root projection beside an open
external reference. They prove the original forest is not wholly closed,
derive support from selected-value closedness, and check exact retained
operation/native-table/domain fields. The effects and language endpoint
examples keep their explicit initial readiness and acceptance witnesses.
They do not claim to construct a complete ready caller from scratch.

Frozen artifacts:

```text
e77378fc61e9ee1c808959801029ae571ed65ee0745ee557753350b487c79e59  operand-publicprobes.lean
11bac0d3c003613351e9f3af457102ac6d0219acddcd9ced64577a0c549f3da6  operand-publicprobes-2.log
b2726d06202b2e0bee60adbacc27acbac2432105b8b3d123e82ed03bb51a1208  operand-build.log
```

Only the new source and its owned evidence files changed. No old proof,
Audit, root document, Haskell source, or Git metadata changed.
