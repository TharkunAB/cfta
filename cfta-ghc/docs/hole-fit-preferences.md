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
Legacy golden output is unchanged. These checks establish the file workflow;
no gain on real held-out hole fits has been established.
