# Changelog

## 0.1.0.0 - Unreleased

- Add `Data.CFTA.Serialization.Text`: a readable text format, version 1, for
  graphs (`graph 1;`). A parsed value is equal to the printed value, and
  printing it again gives the same text.
- Add doc comments: a `///` line documents the next header or state.
  `printGraphNotesWith` and `parseGraphNotesWith` keep the comments beside the
  value, in `Notes`. The other readers drop them. `showCodec` gives the state
  labels of `Show` and `Read`.
- Add sorts of states: `state Pos : Int {`. `Notes` keeps them in `noteSorts`.
- Add the text forms of checkpoints: `printCheckpoint` and `parseCheckpoint`
  for `checkpoint 1;`, and `printSamplingCheckpoint` and
  `parseSamplingCheckpoint` for `sampling 1;`, each with a `With` variant for
  a `StateCodec`. A `checkpoint 1;` file holds the query route and its
  version, the size bound, and the sized rank of the next term
  (`next size 5 rank 1;`). A `sampling 1;` file holds the query, the weights
  of the sizes, the pseudorandom generator and its version, the seed, and the
  number of draws. Each then holds its exclusions, `exclude root TEMPLATE;`
  and `exclude anywhere TEMPLATE;`, and the text of `printGraph` for the
  graph. Neither has doc comments or sorts.
- Add `printDocument`, `parseDocument`, `printLanguage`, and `parseLanguage`:
  the text forms `document 1;` and `language 1;` of source documents and of
  languages with named exclusions. A doc comment can also document a
  production, a fact, or an exclusion, and a state of a document or a language
  can have a sort. `printDocumentNotesWith`, `printLanguageNotesWith`, and
  their parsers keep them in `Notes`.
- Add `printUpdate` and `parseUpdate`: the text form `update 1;` of a
  `Language.Update`, one statement for each operation.
