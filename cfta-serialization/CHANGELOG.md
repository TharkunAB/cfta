# Changelog

## 0.1.0.0 - Unreleased

- Add `Data.CFTA.Serialization.Text`: a readable text format, version 1, for
  graphs (`graph 1;`). A parsed value is equal to the printed value, and
  printing it again gives the same text.
- Add `printCheckpoint` and `parseCheckpoint`: the text form `checkpoint 1;`
  of a `Checkpoint`. It holds the query route and its version, the size
  bound, and the sized rank of the next term, then the text of `printGraph`
  for the graph.
- Add `printSamplingCheckpoint` and `parseSamplingCheckpoint`: the text form
  `sampling 1;` of a `SamplingCheckpoint`. It holds the query, the weights of
  the sizes, the pseudorandom generator and its version, the seed, and the
  number of draws, then the text of `printGraph` for the graph.
