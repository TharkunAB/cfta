# Interface and worker context checks

The proof statement is unchanged in this checkpoint.
See `../20261106-prepared-action-totality/REPRODUCE.md` for the checked proof.
The files here record two ordinary accessor signatures and one nominal
binding lookup. They contain no private State TYPE or worker source body.

Use Lean 4.34.1 and the repository Nix environment. From `lean/`, run:

```sh
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake build MicroCFTA.InternedFreshProbeKeys'
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake env lean -j1 -DwarningAsError=true restart-evidence/20261106-interface-worker-context/two-getter-types.lean'
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake env lean -j1 -DwarningAsError=true restart-evidence/20261106-interface-worker-context/one-expr-kind-owner.lean'
```

Use serial capped jobs on WSL. The recorded checks used 4 GiB and zero swap.
The first command rebuilds missing imported objects in a clean checkout.
The two query sources are byte-identical to the sources checked at their
historical paths. Their actual compiler exits were0. Do not infer that fact
from the outer Python driver's exit code.

The first query prints both complete ordinary getter signatures.
Their accepted context has one explicit ConstantInfo argument each.
It has no implicit or class arguments or free universe parameters.
No getter invocation or implementation proof was performed.
The second query returns one bound INDUCTIVE target with actual owner
Lean.Expr. It reads no constructor, TYPE, value, or actual CI-name equality.

The JSON records contain historical identities and receipt flags.
Physical identities will differ on another machine. They are audit records,
not proof dependencies. The source endpoint and frame records do not prove
source/object correspondence or structural correctness of a State observer.
The private State777 capture remains unviewed. The structural Expr operation
remains open. Neither these checks nor the worker-source inspection proves
the common original-input bound or Haskell/runtime correspondence.

No Haskell fix was identified. The finite-identity and forced-typecheck routes
remain proposed proof work. No Haskell assertion probe was executed.
No copied build tree or large temporary log is needed to run these commands.

The complete worker prefix1..329 is already in
`MicroCFTA/EnumerationState.lean`. Receiver487 restored its namespace,
formal, and local source context. These workers form an abstract Graph/Oracle
Lean model. No actual optimized or older runtime realization was established.
The new receipts preserve this boundary. The earlier context stop remains
historical. It was resolved by the complete prefix.

The Source overlap record was written before final acceptance.
Its pending flag records that phase. The final487 receipt records acceptance.
Five previously API-charged rows also occur in the literal prefix.
Their shared Source union counts those rows once.
The expression-origin plan is a future metadata plan. It was not executed.

The Haskell input record comes from owned metadata. It records a stored
Source expectation and compiler-context pointers. No Original file was
refreshed. Exact getter-expression spans and actual component checking remain
uncertified. No assertion probe or Haskell fix was performed.
