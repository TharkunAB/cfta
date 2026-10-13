# Haskell replay of the staged rank fixture

Checked on 2026-10-13 against the local source at `b9fde4a`.
`repro/SourceRankStutter.hs` reproduces
`MicroCFTA/InternedSourceRankStutter.lean` with the actual Haskell
constructors and `unfoldOuterRec`. No production code changed.

The program builds the original two raw binders with fixed captures
`RecDepth` and `RecUnint 2`. It then evaluates both unused smart preloads
and the raw representative with a used smart inner binder. It forces
each stage before the next stage can modify the process-global caches.
Finally, it unfolds the original record three times.

Run from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta lean/repro/SourceRankStutter.hs'
```

The checked observations agree with Lean:

| Observation | Result |
| --- | --- |
| Consecutive stored Mu rank | `[2,2,1,0]` |
| Minimum free-reference occurrence cost | `[2,2,1,0]` |
| Cached maximum Mu depth | `[2,4,5,5]` |
| First unfolding equals the preloaded representative | `True` |
| All four records are open and unconstrained | `True` |
| Free names in all four records | `RecDepth`, `RecUnint 2` |

The occurrence cost uses the actual stored body. It removes each Mu's
own reference and adds one to the other costs. It traverses ordinary
children and union members without an extra cost. Thus both rank
functions match the Lean definitions.

The program also checks the original stored body's substitutions to its
actual depth and ordinary probes. Both equations hold. However, the
unrestricted callback renaming equation in
`microcfta/src/Data/CFTA/Interned/Type.hs` does not hold for this fixture.
For `f = originalBody`, the following values differ:

```haskell
substFree RecDepth (Rec (RecUnint 999)) (f (Rec RecDepth))
f (Rec (RecUnint 999))
```

The first value has free names `{RecUnint 2, RecUnint 999}`. The second
also retains `RecDepth`. The old name aliases a fixed capture, so the
substitution changes that capture on the left. The program checks this
inequality as well as the two actual probe equations.

This is an executable open-cache counterexample to unconditional strict
decrease of either candidate rank. It is not a divergence witness. It
does not establish closed empty-environment reachability. It does not
refute a theorem restricted to callbacks that satisfy the unrestricted
renaming equation, because this callback fails that equation. The two
passing actual probe checks do not replace the stronger contract.
