# Independent outer worker validation

Timestamp: 2026-10-16 14:19 CEST.

Reviewed source SHA256: `ed3921e17d46e64b5bdae1c5bcdb00312d1c81549a13aac3fb63d868f8f414d6`.

Both final imported direct Lean probes terminate with exit 0:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-worker/outer-public.lean > lean/restart-evidence/20261016-parent-worker/outer-public-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-worker/outer-kernels.lean > lean/restart-evidence/20261016-parent-worker/outer-kernels-2.log 2>&1
```

Ten public axiom/full-signature pairs and twelve integration kernels pass without warnings. The foundations are propext, Classical.choice, and Quot.sound. The first kernel log is retained. It records three probe-only equation-unfolding failures, fixed by simp only on the actual well-founded definitions. No source proof changed.

The reviewer runs no Lake or Haskell build. Root owns the canonical build. No compiled artifact is created in this evidence directory. No active process or build slot is held. See outer-review.md for exact source correspondence and retained graph/completion/runtime boundaries.
