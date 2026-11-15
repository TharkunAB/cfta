# Tuple-nil dependent-index repair

Status: UNCOMPILED. No proof credit.

Dependent ledger elimination replaces the captured caller and own cache with the surviving scopeOriginal and scopeBefore indices. The proof now uses those indices after each constructor case. The constructor pattern binders remain unchanged.

The full component header and probes are byte-exact. Every origin, current scope, ancestor ledger, snapshot, preparation equation, task-work bound, forecast, runtime result, and native endpoint remains unchanged. No premise or visibility change was added. The original failed append and compiler log remain unchanged.
