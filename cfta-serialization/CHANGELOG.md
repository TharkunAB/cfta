# Changelog

## 0.1.0.0 - Unreleased

- Add `Data.CFTA.Serialization.Text`: a readable text format, version 2, for
  graphs (`graph 2;`), source documents (`document 2;`), and languages
  (`language 2;`). A parsed value is equal to the printed value, and printing
  it again gives the same text.
- Add `printUpdate` and `parseUpdate`: the text form `update 1;` of a
  `Language.Update`, one statement for each operation.
- Add `printCheckpoint` and `parseCheckpoint`: the text form `checkpoint 1;`
  of a `Checkpoint`. It holds the query route and its version, the size
  bound, and the sized rank of the next term, then the text of `printGraph`
  for the graph.
