# Package names and source correspondence

Upstream PR #129 is `7bfb69d1` on `origin/microcfta`.

| Previous package and directory | Current package and directory |
| --- | --- |
| `microcfta` | `cfta` |
| `microcfta-generator` | `cfta-generator` |
| `microcfta-ghc` | `cfta-ghc` |

Public Haskell modules retain `Data.CFTA.*`. The workspace remains
`/home/tritlo/Code/mcfta`. Git branches and backup names retain their names.
The Lake package is `cfta`. Lean modules and declarations retain `MicroCFTA`.
This avoids changing theorem names that do not represent public package names.

PR #129 also replaces the reserved `__microcfta_` prefix with `__cfta_`.
The executable source models and probes now use the new actual, bound,
contract, integer, and value names. Their freshness, injectivity, capture,
preflight, and collision proofs retain their statements with those names.
The external solver codec and semantic contracts remain unchanged.
The synthesis function, argument, condition, bound, and pool names also use
the new prefix upstream. Those applications have no complete source model.

Current source links and executable commands use the new package names.
Older source notes retain historical commit hashes. Their paths identify
relocated files. Name examples use the current prefix unless a note marks
an exact historical result. Saved logs and manifests retain their bytes.
No historical failure is reported as a new runtime regression.

The preserving rebase replayed 555 commits and ended at `ede5f85a`.
The backup before rebase is
`backup/formalization-before-package-rename-20261014-2112`, at `2e165b8e`.
All 1,880 saved Lean-tree files matched immediately after rebase.
The subsequent name updates are explicit changes. Their file inventory,
before manifest, complete file copies, and rebase log are in
`/tmp/mcfta-rename-refresh-20261014-2111/`.
The one changelog conflict retained both notes. The three marked drafts and
three untracked fixtures remain unchanged. Other worktrees and stashes remain.

The actual `Data.CFTA.Sized`, native callback, minimum-table, and interned
runtime modules are byte-identical after relocation. Only reserved-name
literals change in the modeled guard and formula source. No optimized core
was replaced. The preceding PR #120 added GHC and synthesis applications.
They remain outside complete formal source coverage.

Run source checks from the workspace root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta:unit-tests cfta-generator:gen-tests cfta-generator:refinement-tests -j1 --test-show-details=direct'
```

Run the dependency audit with the pinned Lean toolchain:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Validation logs are `renamed-audit.log` and `renamed-source-tests.log` in the
evidence directory. The audit passed 1,509 jobs and 44,088 theorem dependency checks.
The Nix suites passed 289 core, 209 generator, and 147 refinement examples.
All five updated native probes and both formatter checks passed.
The old unused `inputs` warning remains. No new warning was introduced.
All work remains local.
