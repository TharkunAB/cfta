# decision-model

A decision model gives a score to each option of a question. This Haskell
library asks a model that runs on a server, over HTTP. It does not use an
external client program.

## API

```haskell
data Question = Question {questionName, questionState, questionText :: Text, questionOptions :: [Option]}
newtype DecisionModel = DecisionModel {scoreOptions :: Question -> IO (Either String [Double])}
Ollama.withOllama Ollama.defaultOllama $ \model -> scoreOptions (chunked 250 (bothOrders model)) (question state text options)
model <- OpenAI.openAI (OpenAI.defaultOpenAI "gemma4:e2b")   -- a chat model, from its log probabilities
ranked (questionOptions q) scores                              -- the options, the highest score first
```

- `Decision`: the types, `question` (a question with the name `q0`),
  `fixedModel` (a model without I/O, for tests),
  `chunked` (a long question in parts, each with the option "none"),
  `bothOrders` (the mean of the scores in the order of the options and in the
  reverse order), and `ranked`.
- `Decision.Ollama`: Ollama's decision API, `POST /v1/systemone`, for a model
  with the capability "decision", such as Nimble v3. `unload` unloads the
  model, and `withOllama` unloads it at the end of an action.
- `Decision.OpenAI`: the chat API of a server that is compatible with OpenAI,
  `POST /v1/chat/completions`. The options get the labels A to T, and the
  score of an option is the probability of its label as the first token.

All failures are values (`Left`): no connection, a status that is not a
success, a bad reply, a missing score, and two options with the same name.

Ollama's decision API shows the name of a question to the model, so the name
changes the scores.

The scores of a model depend on the order of the options. `bothOrders`
removes most of this bias. Put it inside `chunked`, so that each part has the
same options in the two orders.

The default temperature is 0. Then the same requests after a load of the
model get the same scores. The scores of a request change a little with the
requests before it, because the server keeps parts of earlier prompts. On
Ollama, `ollamaKeepAlive = "0"` loads the model for each request, and the
scores then do not depend on earlier requests.

## Ollama

The decision API needs Ollama 0.40.4 or later for Nimble v3.

```sh
ollama pull nimble-v3:9b-q4_K_M
ollama serve      # if the Ollama service does not run
```

The server keeps a model loaded for the time of `ollamaKeepAlive` (default
`5m`) after a request. `withOllama` unloads the model at the end. A request
can have at most 255 options and 64 KiB. The model asks a longer question in
parts. For long descriptions, use `chunked` with fewer options.

## License

The library has the BSD-3-Clause license (see `LICENSE`). It contains no
model and no model output. A model is a separate download, under its own
license. Nimble v3 (Bespoke Labs) has the license CC BY-NC 4.0: noncommercial
use only.

## Tests

```sh
cabal test --test-options='+RTS -M2G -RTS'
DECISION_MODEL_LIVE=1 cabal test --test-options='+RTS -M2G -RTS'               # Nimble v3 on the local Ollama
DECISION_MODEL_OPENAI=gemma4:e2b cabal test --test-options='+RTS -M2G -RTS'    # a chat model on Ollama's OpenAI API
```

The tests with a server unload the model at the end.
