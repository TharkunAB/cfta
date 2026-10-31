# Train preferences between valid hole fits

`cfta-fit-preferences` learns which complete program to prefer within each
supplied candidate pool. The caller must supply programs that GHC has checked
for the same hole. The trainer does not check their types or intended behavior.

For case `i`, let `b_i(p)` be the existing corpus score and `f_i(p)` the counts
of parent-position-token features. The conditional log-linear distribution is:

```text
P_i(p) = exp(b_i(p) + theta . f_i(p)) / sum_q exp(b_i(q) + theta . f_i(q))
```

Training maximizes the mean preferred-program log probability minus
`precision / 2 * ||theta||^2`. Each case has equal weight and its own normalizer.
The CLI uses precision `0.01` and at most 1,000 steps, including the initial
point. It reports the stop reason. Exact duplicate `Program` values count once.
Different programs with equal features retain separate probability mass.
The preferred program must already occur in a pool with two distinct programs.

## Case records

A file starts with `fit-preference-cases 1;`. Each following record is one
Haskell-readable tuple on one line:

```text
(group, (rootParent, rootPosition), locals, moduleUses, preferred, candidates)
```

- `group` identifies a source file or project. Keep the chosen grouping consistent.
- The root context must match the plugin. Use `("top",0)` for a top-level body.
  A nested function hole can require `("lambda/1",0)` for its lambda body.
  Preserve the context obtained by the plugin; do not infer it from printed fits.
- `locals` contains the exact bound names classified as `arg`, including lambda
  arguments. Module definitions remain `var` unless they are corpus candidates.
- `moduleUses` contains `(name,count)` pairs for module names classified as `var`.
  These counts preserve the corpus scorer's name shares. Counts are nonnegative.
- Programs use the derived `Program` form: `Var "xs"` or
  `App (Var "reverse") (Var "xs")`. Preserve internal labels such as `Var "fmap 2"`.
  Records contain AST data. Haskell expression strings and eta-reduced display
  text do not preserve all internal labels and contexts.

Prefer `PreferenceCase` and `printPreferenceCases` from
`Data.CFTA.GHC.Preference` when capturing real fits. `parsePreferenceCases`
reads the same form. For a function hole, store its body and bound names.

## Small manual example

Run from the repository root. These synthetic cases prefer `reverse xs` over
`tail xs`. Both are valid bodies of functions with type `[a] -> [a]`; `tail`
is still partial on an empty list. This example checks the workflow, not
generalization to new source code. Create three files:

```sh
cat > demo-base.cfta <<'EOF'
fit-model 1;
modules Prelude;
candidate reverse 1;
candidate tail 1;
unigram reverse/1 1;
unigram tail/1 9;
unigram arg/0 10;
context top 0 reverse/1 1;
context top 0 tail/1 9;
context reverse/1 0 arg/0 1;
context tail/1 0 arg/0 9;
EOF
cat > demo-train.cases <<'EOF'
fit-preference-cases 1;
("Training.hs",("top",0),["xs"],[],App (Var "reverse") (Var "xs"),[App (Var "reverse") (Var "xs"),App (Var "tail") (Var "xs")])
EOF
cat > demo-test.cases <<'EOF'
fit-preference-cases 1;
("Evaluation.hs",("top",0),["ys"],[],App (Var "reverse") (Var "ys"),[App (Var "reverse") (Var "ys"),App (Var "tail") (Var "ys")])
EOF
nix-shell --run 'cabal build cfta-ghc:cfta-fit-preferences'
nix-shell --run 'cabal run -v0 cfta-ghc:cfta-fit-preferences -- train demo-base.cfta demo-train.cases demo-preferences.cfta +RTS -M2G -RTS'
nix-shell --run 'cabal run -v0 cfta-ghc:cfta-fit-preferences -- evaluate demo-preferences.cfta demo-test.cases +RTS -M2G -RTS'
```

Use your environment's process memory cap as well as the RTS heap limit.
Evaluation prints the preferred program's baseline and learned ranks, starting
at one. Equal scores keep the supplied pool order. These are score ranks;
the plugin also keeps GHC's own fits first and puts fits that ignore arguments
last. Evaluation uses the corpus model embedded in the preference file. The file
also stores training groups. Evaluation rejects any overlap with the test groups.
Group labels are supplied metadata; this check cannot prove source independence.
Complete-program scores use the plugin reranker's addition order. Optimization
uses aggregated feature counts.

Load the result with the existing plugin option
`-fplugin-opt=Data.CFTA.GHC.HoleFits:model=demo-preferences.cfta`.
The plugin still checks proposed programs with GHC. Preference scores change
the order of fits, not structural term ranks. Legacy `fit-model 1;` files retain
the original scorer. They have no training-group record for this evaluation CLI.

## Scoring cost and current limits

The isolated scoring fixture uses 10,000 varied program trees with 32,500 tokens.
It loads one fitted file for every mode. This excludes training from scoring.
The original implementation is commit `f5b91bf4e3`. The updated scorer shares
token classification with the corpus score through `Model.tokenScoreSharedWith`.
All three mode checksums are unchanged.

| Mode | Original instructions | Updated instructions | Original allocation | Updated allocation |
| --- | ---: | ---: | ---: | ---: |
| Corpus | 384,044,100 | 389,292,801 | 164,047,832 | 168,467,840 |
| Empty corrections | 384,029,867 | 389,282,084 | 164,047,936 | 168,467,896 |
| Learned corrections | 619,896,954 | 431,786,851 | 249,420,456 | 169,650,392 |

The measurement uses GHC 9.14.1, unoptimized project libraries, an optimized
driver, Cachegrind instructions, and `+RTS -s` allocation. Corpus scoring costs
1.37% more instructions and 2.69% more allocation than the original scorer.
This is within the repository's 5% budget. Learned corrections cost 12.43% more
instructions and 3.42% more allocation than the original corpus scorer. Keep
this feature experimental until evaluation on unseen source justifies that cost.
This fixture does not measure complete plugin search or predictive accuracy.

Scores use `Double`. Finite corrections can still overflow when added. The
evaluation CLI rejects non-finite complete-program scores. Accumulated-score
overflow remains a limit of the existing best-first search: it discards infinite
completion bounds. Ordinary positive scores are supported. The search computes
the best remaining score within its finite size bound.

The source package includes
[`ScoreCost.hs`](hole-fit-preferences/ScoreCost.hs). Build the library first,
then compile the driver from the repository root with the same dependency plan
in each checkout:

```sh
cabal exec -- ghc -O2 -rtsopts -package cfta \
  -package-id cfta-generator-0.1.0.0-inplace \
  -package-id cfta-ghc-0.1.0.0-inplace \
  cfta-ghc/docs/hole-fit-preferences/ScoreCost.hs -o /tmp/preference-score-cost
/tmp/preference-score-cost train +RTS -M1G -RTS > /tmp/preferences.cfta
/tmp/preference-score-cost plain 10000 /tmp/preferences.cfta +RTS -M1G -s -RTS
/tmp/preference-score-cost empty 10000 /tmp/preferences.cfta +RTS -M1G -s -RTS
/tmp/preference-score-cost trained 10000 /tmp/preferences.cfta +RTS -M1G -s -RTS
```

Run these commands inside the repository's `nix-shell` with a process cap.
Use the same serialized file for each mode. Use a separate output directory
when compiling against a second checkout. Copy the driver there when comparing
against `f5b91bf4e3`, which does not contain it.

## Training setup cost

Prepare one corpus scorer for each case. Reuse it for every candidate and the
preferred program. Force the preferred offset before returning the prepared
case so that its scorer tables can be collected. Library callers can retain
`scoreProgram model item` once when comparing programs from the same case.

The local real-code pilot has six training cases and 173 corrections. Both
versions use the same base counts and cases, GHC 9.14.1, and optimized code.
The baseline is `c993da9daa`, before scorer sharing. Cachegrind counts instructions.
The RTS reports allocation and maximum residency. The serialized model, fit
report, and five held-out rank rows are identical before and after the change.

| Pilot training | Before sharing | Shared scorer |
| --- | ---: | ---: |
| Instructions | 19,772,196,374 | 2,468,361,626 |
| Allocation, bytes | 4,214,086,528 | 728,084,672 |
| Maximum residency, bytes | 14,169,872 | 13,981,968 |

The source package's `ScoreCost.hs` also has a self-contained `train-wide` mode.
It adds 4,000 distinct parent contexts to the small corpus and fits the existing
three pools of eight programs. This gives 4,013 context records. It prints the
step count, stop reason, and every final step field for exact comparison.

| Synthetic training | Before sharing | Shared scorer |
| --- | ---: | ---: |
| Instructions | 74,273,488 | 36,832,763 |
| Allocation, bytes | 39,192,152 | 12,432,704 |

For this comparison, both versions of `Data.CFTA.GHC.Preference` and the driver
use `-O2` with the same optimized dependency plan. The final fit output is
identical. Copy the same driver into both checkouts and use separate output
directories. Run it inside a capped `nix-shell` after compilation:

```sh
/tmp/preference-score-cost train-wide +RTS -M2G -s -RTS
valgrind --tool=cachegrind --cache-sim=no --branch-sim=no \
  /tmp/preference-score-cost train-wide +RTS -M2G -RTS
```

These measurements cover setup and fitting. They do not measure search speed
or ranking quality. The complete 65-case fit reports 16,235,752 bytes of maximum
residency with this preparation order.

## Origin and validation

This extension uses the corpus scorer and parent-position features from
[PR 194](https://github.com/TharkunAB/cfta/pull/194), and the log-linear fitting
machinery from [PR 196](https://github.com/TharkunAB/cfta/pull/196).
It adds conditional training over fixed pools. It does not reproduce
[PHOG](https://proceedings.mlr.press/v48/bielik16.html)'s context-navigation learner
or [ExplainFuzz](https://arxiv.org/abs/2604.06559v1)'s probabilistic-circuit
construction. The preference API uses parent-position corrections. It does not
learn the context selector.

The manual CLI example moves the preferred program from rank two to rank one.
The actual plugin loads the resulting file in reranking and best-first modes.
Legacy golden output is unchanged. These checks establish the file workflow.

The [fixed package-held-out evaluation](hole-fit-preferences/evaluation.md)
contains 65 training cases and 37 eligible test cases from separate packages.
Top-one source recovery falls from 16 to 14 of 37 test cases. Top-five recovery
stays at 25 of 37. Keep this feature experimental: these results do not justify
its extra scoring cost. The report includes all ranks, coverage, input hashes,
and the limits of the labels and corpus provenance.
