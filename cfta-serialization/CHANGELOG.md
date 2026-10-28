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
