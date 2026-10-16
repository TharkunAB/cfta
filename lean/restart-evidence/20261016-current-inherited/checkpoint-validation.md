# Current inherited caller checkpoint validation

Source main: `8f85ddb605327bd088aae970ab058137c4f6d762`.
Prior published formalize: `a15d614375903096da1ad0d9c7f8e5ad5aec1ab2`.
Proof commits: `e5714c8d`, `0af22f98`, `e37b311b`, `1226b1f3`.
Audit and scope: `0c1f64b2`. Restart documents: `b8b48c26`.
The full library goal remains active.

## Checked sources

Eight additive modules are pinned in frozen-modules.json. Every older
non-Audit Lean source remains unchanged. The new public APIs have focused
builds, axiom and full-signature probes, and external integration kernels.
Independent reviews cover the recursive graph, current Mu source pattern,
warm key semantics, exact owner retention, and reduced-edge completion.

The pinned command is:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Final terminal result: 0, 2371 jobs, 57099 MicroCFTA theorem dependency
checks. Final log: full-audit-final.log. The audit imports all eight modules
and rejects every axiom outside propext, Classical.choice, and Quot.sound.
Only the preexisting unused inputs warning remains. The earlier full-audit.log
records a resolved private unused-section-variable warning. It is not the
final validation log. Both sessions reached terminal results and closed.

The final direct and public logs for each component are identified in its
validation note. Failed development logs are retained. They are not used
as passing evidence. The reduced-edge public probe is
partial-edge-call-independent-public.lean, with final terminal-0 log
partial-edge-call-independent-public-3.log. Its final source hash includes
the explicit omitted section variables on the private not_absent helper.
No compiled artifact is stored in this evidence directory.

Whitespace checks pass for sources, documentation, and probe inputs. Raw
failed-development logs and exact git worktree snapshots retain their
original whitespace and are excluded from that formatting check.

## Integration evidence

The inherited-prefix kernels check source short circuits, allocated errors,
the actual indexed descendant value, and a returned sentinel guard. Raw
rebuild kernels check same-arity source setChildren, fallback independence,
literal modifyNode, and independent edge language. The current recursive
graph kernels check successive actual indices and states, returned-edge
fields, ordered row reconstruction, both busy families, and the Rec error.

Memo kernels derive initial Sound, finish exact evaluating owners, reuse
later aliases, and retain answers through physical effects. The reduced-edge
repeat theorem derives the actual published key and returned cell from its
first evaluated call. It then constructs a second actual warm call at that
same returned state, with no supplied lookup or cell answer. The repeat
retains the whole caller state and global bundle. Further kernels cover
cold initialization and actual busy observations. The read-schedule warm
fixture is only a logical protocol fixture; it does not claim physical
heap validity. The current Mu kernel connects the actual NodeBody result
to its derived smart cleanup under the explicit filtered-probe heap.

These kernels check component composition. They do not prove the full outer
mutual language invariant, general recursive termination, a literal bounded
executable worker, or GHC forcing/publication correspondence.

## Source refresh and retained work

The opening git pull --ff-only returned Already up to date. A later upstream
read through the default SSH connection remained live. Its exact owned
git/ssh process pair was inspected. Only that read-only SSH child was then
terminated, and its tool handle reached terminal 128. A bounded SSH read
through ssh.github.com:443 succeeded. remote-before.txt verifies main and
formalize. No upstream change was available to merge.

verify-preservation.py derives preservation-final.json from the opening
tracked-file hashes. It verifies all 4146 starting files and identical bytes
for all 2362 older non-Audit proof sources. Only Audit and the seven restart
documents may change. It verifies nineteen frozen manifests, unchanged
stashes and other worktrees, and the first Haskell fix registry. Earlier
unavailable external drafts are not claimed recovered or reverified.

No Haskell implementation or test file changes occur in this checkpoint.
The retained source differences from main are the historical fresh-probe
changelog entry and the OuterCallerCycle reproducer comment. The behavioral
repairs already match main. FINDINGS.md records their upstream status and
the required handoff fields for every later fix. Reuse unchanged-source
strict Nix all-component build, 777 examples plus golden, five-file Fourmolu,
and four-package Cabal-gild evidence from the current source refresh.

Read outer-current-next.md for the next actual caller obligations. Keep the
full-library scope, the optimized interned core, all separate Sized contracts,
and all older constructor and equality work. No board post or deployment is
performed. Publish this verified checkpoint only to formalize.
