# Prepared-action totality

The proof is `MicroCFTA.SourcePruningEnumerationActionTotal.prepare_total`.
Its source is `lean/MicroCFTA/SourcePruningEnumerationActionTotal.lean`.
The source has 3348 bytes and SHA-256
`e4bc14ff590068ca156e9f02e07b1a72f0257da7573291be67122da1a73597cd`.

Start with total representatives. If the modeled action preparer returns an
operation and that operation succeeds, its output has total representatives.
This statement holds for all local fuel values. It does not use the selected
step's eight caller conditions. The `EdgeKey` equality instance remains.
The statement does not prove that an operation exists or terminates.
It does not prove a common original-input bound or Haskell correspondence.

From the repository root, use Lean 4.34.1 and the Nix environment:

```sh
cd lean
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake build MicroCFTA.SourcePruningEnumerationAction MicroCFTA.EnumerationCompressionFrame'
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake env lean -j1 -DwarningAsError=true MicroCFTA/SourcePruningEnumerationActionTotal.lean'
```

The first command rebuilds missing imported objects in a clean checkout.
The second command checks the proof. Use the repository's serial capped
runner on WSL. The recorded check used 4 GiB and zero swap.
No copied build tree is needed.

To repeat the axiom report, copy the proof to a temporary Lean file and append:

```lean
#check @MicroCFTA.SourcePruningEnumerationActionTotal.prepare_total
#print axioms MicroCFTA.SourcePruningEnumerationActionTotal.prepare_total
```

Check that file in the same environment. The accepted report lists
`propext`, `Classical.choice`, and `Quot.sound`. It has no `sorryAx`.
Checks 453 and 456 failed the unused-section-variable linter. The final
source removes those variables. Check 459 accepted its type and axioms.
Check 463 accepted the exact repository source with empty output.
The JSON files record those checks. Their historical paths and input
identities are audit records; they are not proof dependencies.

The remaining files contain metadata from the existing compiled indexes and
the controlled Lean environment. The two worker keys are definitions in
`MicroCFTA.EnumerationState`. Their optimized-worker behavior remains open.
The two getter records are candidate source envelopes. No getter Source
view or private State-type receipt was performed in this pass.
No Haskell fix was identified. The fresh-identity recurrence in the handoff
is an abstract proof obstruction. It is not a Haskell divergence witness.
