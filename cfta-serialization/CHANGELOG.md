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
- Add `printDocument`, `parseDocument`, `printLanguage`, and `parseLanguage`:
  the text forms `document 1;` and `language 1;` of source documents and of
  languages with named exclusions.
- Add `printUpdate` and `parseUpdate`: the text form `update 1;` of a
  `Language.Update`, one statement for each operation.
- Add doc comments: a `///` line documents the next header, state,
  production, fact, or exclusion. `printGraphNotesWith`,
  `printDocumentNotesWith`, `printLanguageNotesWith`, and their parsers keep
  the comments beside the value, in `Notes`. The other readers drop them.
  `showCodec` gives the state labels of `Show` and `Read`.
- Add the text forms of named predicates, `predicate(NAME, [TERM, ...])`, and
  of named sorts, `named(NAME, [SORT, ...])`.
- Add named holes to templates: `_x` is the hole with the name `x`. A template
  quotes a symbol whose name starts with `_`.
- Add sorts of states: `state Pos : Int {` in a graph, a document, or a
  language. `Notes` keeps them in `noteSorts`.
- Add `printSignature`, `parseSignature`, and their codec variants: the text
  form `signature 1;` of a `SortedSignature`, one statement for each sort,
  root, value sort, and function.
