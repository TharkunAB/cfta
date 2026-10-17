# Validation

Validated at 2026-10-17 10:08 CEST.

- `numeric-projection-direct-1.log`: successful intermediate row arithmetic core, exit 0, zero bytes.
- `numeric-projection-direct-2.log`: complete production source, exit 0, zero bytes.
- `numeric-projection-canonical-1.log`: canonical target, exit 0, 1241 jobs.
- `numeric-projection-direct-3.log`: final production replay against the final growth dependency, exit 0, zero bytes.
- `numeric-projection-public-2.log`: 32 complete imported signature and axiom pairs against that final dependency, exit 0, no diagnostics.
- `numeric-projection-kernels-2.log`: three imported arithmetic integration pairs against that final dependency, exit 0, no diagnostics.

The first canonical invocation used the growth dependency's successful partial build.
That dependency then appended actual Head, ReadAll, and Union endpoints.
Its pure growth APIs did not change.
The final direct and imported checks ran after the dependency's final canonical build.
The current production source has not changed since direct attempt 2.
All earlier raw checks and exact attempted sources remain preserved.

All public and integration probes enable full explicit signatures, proofs, universes, deep terms, and pp.maxSteps 10000000.
Their axioms are propext and Quot.sound, or none.
The canonical log replays the inherited InternedFreshOrdinaryClosedCompletion.lean:24 unused-variable warning.
The new production strict logs are empty.
