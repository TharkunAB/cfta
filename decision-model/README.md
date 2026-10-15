# decision-model

A decision model gives a score to each option of a question. This Haskell
library has the interface of a decision model, and combinators for its
questions.

## API

```haskell
data Question = Question {questionState, questionText :: Text, questionOptions :: [Option]}
newtype DecisionModel = DecisionModel {scoreOptions :: Question -> IO (Either String [Double])}
scoreOptions (chunked 250 (bothOrders model)) question
ranked (questionOptions question) scores                       -- the options, the highest score first
```

- `Decision`: the types, `fixedModel` (a model without I/O, for tests),
  `chunked` (a long question in parts, each with the option "none"),
  `bothOrders` (the mean of the scores in the order of the options and in the
  reverse order), and `ranked`.

The scores of a model depend on the order of the options. `bothOrders`
removes most of this bias. Put it inside `chunked`, so that each part has the
same options in the two orders.

## License

The library has the BSD-3-Clause license (see `LICENSE`). It contains no
model and no model output.

## Tests

```sh
cabal test --test-options='+RTS -M2G -RTS'
```
