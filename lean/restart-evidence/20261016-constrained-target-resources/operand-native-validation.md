# Native certificates through actual operands

Validated at 2026-10-16 20:36 CEST with pinned Lean 4.34.1.

`SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores` has two public theorems. `native` takes the existing exact full Operand receipt and initial native structural certificates, output-profile certificates, and Idle. It derives those three facts at the same returned checked state. The receipt's literal node and edge table equalities suffice. The certificate predicates use the captured requests and returned results; they do not depend on the changed constructor heap.

`receipt` also retains the Merge profile table. It takes the same Operand receipt, initial physical Merge storage, initial Merge profiles, and the three initial native facts. It opens that receipt's actual projection and Merge. Projection effects retain initial physical Merge storage at the exact intermediate heap. The projection receipt supplies its derived readiness and projected availability. The independent Merge profile producer applies to the actual Merge call and derives the exact saved profile table.

Neither theorem takes forest profile bounds, constructor counts, capacity, future query success, or a desired output law. The module adds no duplicate completion endpoint. It preserves native cells through the existing receipt; it does not execute or reset either native family.

Direct attempt 1 passes with both unused-variable linters enabled. Canonical `operand-native-build-1.log` passes all 1293 jobs. The only warning is the historical `InternedFreshOrdinaryClosedCompletion.inputs` dependency warning. There is no new source warning.

All two public full-signature/axiom pairs pass in `operand-native-public-1.log`. Both integration pairs pass on their first attempt in `operand-native-kernels-1.log`:

- Two actual serial Operand receipts derive all final certificate families and Idle. The probe also retains the original complete node and edge tables, domain cache, and global query tables. It supplies no second initial native invariant; the first receipt derives it.
- Initial forest profile and height bounds invoke the existing `OperandResources.complete`, which constructs its own exact receipt and resource trace. The new theorem retains native structural/output certificates and Idle at that same returned state, alongside the derived Merge profile table and request budgets.

The final logs have no errors, warnings, or `sorryAx`. Source and probe files have one terminal newline and no trailing whitespace. No older proof source, Haskell file, Audit file, restart authority, Git state, or older evidence was edited by this component.
