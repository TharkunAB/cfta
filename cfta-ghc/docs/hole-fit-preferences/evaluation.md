# Evaluation on fixed pools of held-out hole fits

The fixed-default preference fit did not improve source recovery on this
evaluation. Top-one recovery fell from 16 to 14 of 37 cases. Mean reciprocal
rank also fell. The feature remains a draft; these results do not justify an
accuracy claim. The evaluation ran on 2026-10-31.

## Result

Each row below scores the same captured pool with the base corpus scorer and
with learned corrections. Rank one is best. Equal scores retain the supplied
pool order. All metrics use the 37 eligible test cases from 36 packages.

| Metric | Base corpus | Learned corrections |
| --- | ---: | ---: |
| Preferred program in top 1 | 16 / 37 | 14 / 37 |
| Preferred program in top 3 | 22 / 37 | 23 / 37 |
| Preferred program in top 5 | 25 / 37 | 25 / 37 |
| Preferred program in top 10 | 30 / 37 | 29 / 37 |
| Mean reciprocal rank | 0.558247751726 | 0.524521786478 |

Ranks improved in four cases, worsened in seven, and stayed unchanged in 26.
Mean reciprocal rank is `sum(1 / rank) / 37`.

Training used 65 cases from 59 packages. It produced 1,113 corrections in 18
steps. The reported stop reason was `ObjectiveTolerance`. The final gradient
norm was `3.292268551e-8`. This is one fixed configuration: the CLI defaults of
precision `0.01` and a limit of 1,000 steps, including the initial point.
There was no hyperparameter retuning against test ranks. Repeated fits used
to check memory and execution costs do not change this configuration.

## Cohort and coverage

The input was the existing 200-module Hackage sample. It selects one
application with two to four named leaves per module. Index 115 had multiple
holes in all four historical final runs. It was excluded before capture.
The remaining cohort has 199 modules from 156 packages.

The package split was frozen before capture. Package names are lower case
and have their version removed. SHA-256 of `cfta-preference-holdout-v1:` followed
by that name assigns a package to training when the first digest byte is
below 128. All other packages go to test. This gives 118 training modules
from 91 packages and 81 test modules from 65 packages. No package crosses the
split. The pilot used ten packages on each side. The remaining modules ran
in the frozen order, without retries or score-based selection.

| Split | Selected modules | Eligible cases | Preferred absent | Compile failed | Preferred only in lower class |
| --- | ---: | ---: | ---: | ---: | ---: |
| Training | 118 | 65 | 46 | 6 | 1 |
| Test | 81 | 37 | 41 | 3 | 0 |
| Total | 199 | 102 | 87 | 9 | 1 |

The eligible cases span 59 training packages and 36 test packages. Seven
compilation failures report ambiguous type constraints after the expression
is removed. One reports a type mismatch. One reports an unused binding under
the source module's `-Werror` option. The lower-class-only match is index 81.
There were no timeouts, ambiguous preferred displays, singleton exclusions,
or conversion failures. All selected modules remain in the coverage counts.

## Capture and interpretation

The existing corpus scorer generated each pool by best-first search. Each
hole had a five-second search budget, a four-leaf bound, and at most 50
returned CFTA fits. Each compiler process had a 30-second timeout. Capture
ran serially under an 8 GiB process cap and a 4 GiB compiler heap limit.

A temporary private hook saved checked `Program` ASTs before display lost
internal labels. It saved the exact adjusted root context, bound names,
generated lambda arguments, and name-use counts from the punched module.
Native GHC fits and `comesLast` flags were recorded separately. The hook is
excluded from the product. No public capture option was added.

Exact duplicate programs were removed before label selection. A label needed
one distinct program whose displayed text exactly matched the original
sample's prefix-form expression. The converter did not remove whitespace or
parentheses, or apply additional eta reduction. It did not add missing answers.
Distinct ASTs with the same preferred display would make the case ineligible.
Cases use only the normal-priority CFTA class and require at least two distinct
programs. A module also had to compile successfully and report exactly one
hole at the selected source path and position.

This label measures exact displayed-source recovery. It does not establish
semantic equivalence or human preference. The renderer itself can eta-reduce
programs. An equivalent expression with a different display receives no label.
The 37-case rank metrics are conditional on successful capture and label
recovery; they do not use all 81 selected test modules as their denominator.

These are offline score ranks on fixed baseline-generated pools. The learned
scorer did not generate new pools. The complete plugin also puts native GHC
fits first and separates the lower-priority class. These results do not measure
its complete displayed order, search coverage, search speed, or semantic quality.

The historical base is `heldout-packages.cfta`. Its supplied training-file
manifest has no package overlap with the original 200-module sample. The base
was not retrained here. Manifest disjointness does not prove that the saved
counts came from that manifest. These modules also informed earlier plugin
development. This is not an untouched external benchmark.

## Evidence and hashes

The complete local evidence is in `/tmp/cfta-preference-combined`,
`/tmp/cfta-preference-pilot`, and `/tmp/cfta-preference-expanded`. It includes
the frozen manifest, original and punched modules, raw captures, compiler
commands and diagnostics, input cases, fit report, fitted file, and rank rows.
The temporary capture revisions were `0852a65b0c` for the pilot and
`796455ea57` for the expansion. Their capture code is identical; the latter
revision adds pilot documentation.

`train-indices.json` and `test-indices.json` map ordered case rows to original
sample indices and raw evidence. `indexed-ranks.json` preserves that join.
Package names alone are not unique case identifiers.

| Artifact | SHA-256 |
| --- | --- |
| Frozen `manifest.json` | `6e6db72c97edb41e180f23b92d983e1405ddcb93fe3162999c8e198fda2bf8cf` |
| `base.cfta` | `0f417c0d7d0e9ba94fc06d4eca073d65d5fdacd5959a73d9710fa1960f1b1896` |
| `train.cases` | `878f8dd0224bfdf65c8a1844ced9bf85c5889d86a8ce2c82983031999a132d2c` |
| `test.cases` | `be7c5138e054da7bc60575178ca1eea52b33301860cb198c05c50fa542c44ae4` |
| Fitted `preferences.cfta` | `7125c76953d6783bf0c9a6dc35f0020747c70209e2a68a82a8ee0670f352837f` |
| `indexed-ranks.json` | `77db18a0e3156e4c414165a16ee2e54477f273a230d0844fa5efda85f3b10c63` |

## All held-out ranks

Sample indices are zero-based indices in the original 200-module sample.
Rows retain evaluation order. Both `warp` modules remain separate.

| Sample index | Package group | Base rank | Learned rank |
| ---: | --- | ---: | ---: |
| 21 | cpphs | 1 | 1 |
| 45 | listlike | 1 | 1 |
| 15 | lsp-test | 28 | 23 |
| 132 | selective | 2 | 3 |
| 182 | cabal | 2 | 2 |
| 4 | cmdargs | 18 | 21 |
| 174 | unix | 4 | 4 |
| 110 | filepattern | 1 | 1 |
| 20 | ghc-exactprint | 2 | 2 |
| 23 | asn1-types | 1 | 1 |
| 121 | storable-record | 1 | 1 |
| 25 | case-insensitive | 6 | 20 |
| 108 | hie-bios | 46 | 40 |
| 152 | hsyaml | 1 | 1 |
| 54 | hunit | 5 | 5 |
| 175 | diff | 1 | 1 |
| 90 | microaeson | 1 | 1 |
| 92 | hegg | 4 | 3 |
| 165 | warp | 7 | 7 |
| 40 | network-byte-order | 3 | 3 |
| 76 | clay | 24 | 24 |
| 146 | indexed-traversable | 1 | 2 |
| 139 | tasty-discover | 6 | 9 |
| 196 | polyparse | 1 | 1 |
| 59 | fgl | 2 | 2 |
| 44 | contra-tracer | 13 | 14 |
| 69 | smallcheck | 1 | 1 |
| 150 | hslogger | 1 | 1 |
| 79 | language-c | 1 | 1 |
| 66 | numinstances | 2 | 2 |
| 112 | filepath | 1 | 1 |
| 53 | rest-rewrite | 13 | 13 |
| 173 | th-lift-instances | 22 | 18 |
| 164 | streaming-commons | 1 | 2 |
| 11 | http | 6 | 6 |
| 158 | foldl | 1 | 1 |
| 134 | warp | 8 | 8 |

## Origin and adaptation boundary

The corpus scorer and parent-position context come from
[PR 194](https://github.com/TharkunAB/cfta/pull/194). The log-linear fitting
machinery comes from [PR 196](https://github.com/TharkunAB/cfta/pull/196).
This extension fits shared parent-position-token corrections with the corpus
score as an offset. Each supplied pool has its own normalizer.

[PHOG](https://proceedings.mlr.press/v48/bielik16.html) learns functions that
navigate syntax trees to select context. This extension keeps its context
features fixed. [ExplainFuzz](https://arxiv.org/html/2604.06559v1) compiles and
learns grammar-aware probabilistic circuits for conditioned test generation.
This extension uses neither that circuit construction nor its test-generation
workflow. It is a CFTA application of conditional fitting, not a reproduction
of either paper or its evaluation.
