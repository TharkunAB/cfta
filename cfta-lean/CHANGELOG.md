# Changelog

## 0.1.0.0 - Unreleased

- Replace the local synthesis oracle with an LTA `Entailment` solver that
  sends proof obligations to Kimina's HTTP API.
- Check the implication and its negation in one batch. Preserve `Unknown`
  when neither proof succeeds or the response is invalid.
- Translate integer and Boolean formulas with scoped names, fresh bindings,
  ambient assumptions, and first-order uninterpreted functions.
- Add `fallback` to try Kimina after Z3 returns `Unknown` or reaches its
  time limit.
- Update the existing Lean tests to check the solver and LTA integration.
  Live tests use `CFTA_KIMINA_URL`.
