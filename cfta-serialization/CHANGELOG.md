# Changelog

## 0.1.0.0 - Unreleased

- Add `Data.CFTA.Serialization.Text`: a readable text format, version 1, for
  graphs (`graph 1;`). A parsed value is equal to the printed value, and
  printing it again gives the same text.
- Add `printDocument`, `parseDocument`, `printLanguage`, and `parseLanguage`:
  the text forms `document 1;` and `language 1;` of source documents and of
  languages with named exclusions.
