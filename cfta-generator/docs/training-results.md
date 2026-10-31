# Inspect training results

Training a valid-term generator can return finite weights before the
optimizer reaches its gradient tolerance. It can also drop corpus terms
that the automaton rejects or that exceed the size bound. A caller needs
both facts before it accepts a fitted generator or compares training runs.

The weighted-automaton study exposed two such early stops among 15 raw
corpus fits. A separate context-selection experiment compared 33 candidate
fits through `distill`, which returned weights without a stop reason. These
experiments motivated reporting in the existing training API. They do not
establish better hole suggestions or a new fitting algorithm.

## APIs

For the contextual model API, use
`Data.CFTA.Sized.Prefix.Model.trainWithReport`. It takes the same arguments
as `Model.train` and returns the model with its `DistillReport`. Queries and
sampling still use plain terms and tokens. The report's weight keys carry
the context labels used during fitting.

```haskell
import qualified Data.CFTA.Sized.Prefix.Model as Model
import Data.CFTA.Sized.Prefix.Parents (Reach (..))
import Data.CFTA.Sized.Prefix.Train

case Model.trainWithReport (Reach 1 True) automaton bound corpus of
    Left problem -> print problem
    Right (model, report) -> do
        let fitted = distillFit report
        print (distillRetained report, distillDropped report)
        print (fitStepCount fitted, fitStopReason fitted)
        print (stepGradientNorm $ fitFinalStep fitted)
        print (Model.bestTerms 5 model [])
```

`Data.CFTA.Sized.Prefix.Train.fitWithReport` takes a step limit followed by
the same arguments as `fit`. It returns `Either TrainingError (FitReport
symbol)`. The report contains `fitFinalStep`, `fitStepCount`, and
`fitStopReason`. The final step contains the weights, objective, and gradient
norm. The initial point counts as one step.

`distillWithReport` takes the same arguments as `distill`. It returns a
`DistillReport` with `distillFit`, `distillRetained`, and `distillDropped`.
Each corpus occurrence counts once, including duplicates. A term that is
both oversized and rejected counts as one dropped term. The objective and
defaults remain the same: two uniform pseudo-terms, L2 precision `1e-3`, and
at most 2000 steps. The report does not include pseudo-terms in its corpus
counts.

The wrapper calculates the corpus counts before optimization. It does not
retain the original corpus to calculate the dropped count after fitting.

The existing `fit` remains a lazy stream. The existing `distill` keeps its
return type, defaults, filtering, and weights. `Model.train` also keeps its
behavior. Both forms use the same optimizer. The new reporting functions add
validation; they do not change the legacy stream's behavior.

## Stop reasons and numerical limits

| Reason | Meaning |
| --- | --- |
| `GradientTolerance` | The gradient norm caused a stop below `1e-9`. |
| `ObjectiveTolerance` | The objective change caused a stop below the existing relative threshold `1e-13`. The final gradient can still exceed its tolerance. |
| `LineSearchFailed` | Backtracking found no accepted step before its rate fell below `1e-12`. |
| `StepLimit` | The supplied step budget was spent before another stop was known. |

At the step limit, reporting does not evaluate the next point or start
another line search to find out whether fitting would stop. A gradient or
objective stop already known at the last step takes precedence over the
limit. The limit counts returned steps. A line search can evaluate several
trial points within one step.

The reporting functions reject a nonpositive limit, a negative or nonfinite
precision, negative or nonfinite counts, and nonfinite initial weights.
They also reject a step with a nonfinite weight, objective, or gradient norm.
An unsupported training route and an empty retained corpus have separate
errors. `UnsupportedTrainingLanguage` includes the existing limits on
determinization and intersections; it does not distinguish their causes.
`Model.trainWithReport` also rejects context labelling of constrained
automata. It reports `UnrepresentableWeights` when the fitted log-weights
cannot produce finite positive sampling potentials. This is a conversion
failure, separate from a nonfinite optimizer step.

The low-level caller must supply feasible counts for its oracle. The report
does not prove that arbitrary count maps describe accepted terms. A finite
report does not certify an optimum or statistical accuracy. Partition
evaluation and optimization use `Double`. These functions do not add
log-domain arithmetic or support for further constraint classes.

Structural enumeration and ranks do not change. The weights passed to the
sampling API determine its distribution. Inspecting a training report does
not change that distribution.
