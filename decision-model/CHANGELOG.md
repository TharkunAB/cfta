# Changelog

## 0.1.0.0 - Unreleased

Initial version.

- `Decision`: `Option`, `Question` and `DecisionModel`, the interface between
  a program that asks a question and a model that scores its options.
  `fixedModel` is a model without I/O, for tests. `chunked` asks a long
  question in parts of equal size, each with the option "none". `bothOrders`
  gives the mean of the scores in the order of the options and in the reverse
  order. `ranked` puts items in the order of their scores.
- `Decision.Ollama`: a model on Ollama's decision API (`POST /v1/systemone`),
  such as Nimble v3, through http-client. `unload` unloads the model, and
  `withOllama` unloads it at the end of an action.
- `Decision.OpenAI`: a model from the log probabilities of a chat model on a
  server with an API that is compatible with OpenAI
  (`POST /v1/chat/completions`).
