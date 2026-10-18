# Changelog

## 0.1.0.0 - Unreleased

- Add `Data.CFTA.Serialization.Text`: a readable text format, version 2, for
  graphs (`graph 2;`), source documents (`document 2;`), and languages
  (`language 2;`). A parsed value is equal to the printed value, and printing
  it again gives the same text.
- Add `parseGraphQuote` and `graphQuoteNames`: graph quotes, the graph format
  without its first line, with `$name` for a Haskell symbol or constraint.
