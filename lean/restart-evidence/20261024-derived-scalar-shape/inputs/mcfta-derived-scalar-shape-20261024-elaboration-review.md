# Scalar-shape elaboration review

Recorded: 2026-10-24T03:45:11.979922+02:00. Status: SOURCE_ONLY_PROOF_REPAIR_REVIEW.
I read the complete 255-line failed checked input and complete 29,581-byte log.
I inspected the exact v4.34.1 APIs below and the imported module routes. I did
not run Lean or change any source. I authored the original 220-line proposal;
Root authored the repaired model and runs the checks. This is not a compiler pass.

The reported failures do not require an executable or public-contract change.
The smallest repair keeps the current model, adds required documentation and
makes the existing proof terms use the same overloaded operations as the goals.

1. Add documentation to the nine public constructors and four public fields.
   The failed input reports all thirteen missing doc strings. Keep all linters.
2. Remove `eq_comm` from the two broad simplifier lists. It interacts with
   `Bool.true_eq` while `generatedName` and `ValidName` are unfolded. After the
   Boolean cases are reduced, discharge the remaining equality-direction iff
   with the term `eq_comm` or two explicit `Eq.symm` applications. This does not
   add equality commutativity to the simplifier's rewrite set.
3. State the private bind lemma at the notation level:
   `(first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result`.
   The old statement uses the protected concrete `Except.bind`. The actual goals
   contain overloaded `Bind.bind`. Keeping the statement at notation level lets
   both `rw` uses match without changing the executable actions. In its proof,
   reduce the actual `Except.instMonad` projection and concrete `Except.bind`,
   or change locally to the concrete operation and case-split the first result.
4. Reduce map and pure as well as bind where they actually occur. `Except.lean`
   lines 23–36 define `Except.pure` and `Except.map`; lines 66–69 define bind;
   lines 121–125 explicitly install all three operations in the Monad instance.
   Unfolding `Except.bind` alone cannot reduce an overloaded `<$>` or `pure`.
   The raw namedScalar goals contain `<$>` and the nil traversal goal contains
   `pure []`. Use the actual instance projection and `Except.map`/`Except.pure`
   only at those sites. Do not add an unused bind argument to every simp call.
5. Rewrite the first-error induction hypothesis into the cons goal. Its current
   `simpa ... using ih restValid` asks the tail error equation to prove a result
   under the preceding constructor/map. After exposing `List.cons_append` and
   `List.mapM_cons`, rewrite `firstDone` and `ih restValid` in the goal; then
   `rfl` reduces the resulting successful-head and failing-tail Except actions.
   The nil case likewise reduces by the concrete `failed` equality and `rfl`.
   This keeps the actual tail action and needs no result premise or new helper.

The existing lawful instance is already available. Language imports Std and
SourceDeriveNodeViewNames imports Language. Neither project module adds a
competing Except instance. `Init/Control/Lawful/Instances.lean` lines 159–167
supply the lawful Except instance. No local Monad or LawfulMonad instance is
needed. `List.mapM_cons` at `Init/Data/List/Monadic.lean` lines 66–67 has the
usual LawfulMonad prerequisite and retains the actual head-then-tail sequence.

One precise reason map terms appear is the default simplifier rule
`bind_pure_comp` (`Init/Control/Lawful/Basic.lean` lines 132–162). It rewrites
`x >>= (fun a => pure (f a))` to `f <$> x`. The log therefore does not show a
semantic mismatch. Avoid adding the reverse map/bind rewrite to the same broad
simp set. The library itself warns about that loop at lines 169–174.

The accepted-shape predicates remain tests on observed syntax, character
classification and separate type/value lookup results. The proof repair need
not add a desired generated shape, successful GHC output, or native extraction
premise. Preserve the original failed receipt. A later strict check must still
validate elaboration and all-linter acceptance; this static review cannot do so.

Actual inspected input identities:

- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/checked.lean`: 14859 bytes, SHA256 `ecfcec6f013cec35c683c2725153814d3c94bf1ee2d97b8353781c8988e0355e`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/raw.log`: 29581 bytes, SHA256 `e48a78987fb097855c5396b980b69e6cac789bba692048993ea7213a3a9747ce`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/report.json`: 508 bytes, SHA256 `35f07c51ed7268aa316292bdf1c4676120adad76deea881dd3f67cb1c439d866`.
- `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Control/Except.lean`: 11467 bytes, SHA256 `d388b93b3a59dc804743a0cfa7394f64653f5a15d54e584736aa61e1660c7e4c`.
- `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Control/Lawful/Instances.lean`: 24243 bytes, SHA256 `bc5912c44eb77a58e8e2d129c0f721cc6670338a86f866a6e5771c2eaff1f206`.
- `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Control/Lawful/Basic.lean`: 11975 bytes, SHA256 `7aee65ffd017978662f01ddc90932fbbe50379ee36267967d29bb7cf4cb5d2e0`.
- `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Prelude.lean`: 238777 bytes, SHA256 `2a3163bdd830cd31f1f1bc9bc79ea6bdad6a3b2c6f334166792bbc73631f3b10`.
- `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Data/List/Monadic.lean`: 24537 bytes, SHA256 `6ba9e4977f92ae19fab7f283fc04d7c0071464a8452c528167df52119dcefbf0`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceDeriveNodeViewNames.lean`: 4974 bytes, SHA256 `f322435fc4108f5c4632691922901a1906861bfc1d3c0f0f0cf6da19bd327d3b`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/Language.lean`: 24311 bytes, SHA256 `fd78e01d01a4894a6580be076e3fdee877d171ca1d31525876cc2539386573fc`.
