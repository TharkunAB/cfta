# Actual selected preparation and captured-root separation

Status: UNCOMPILED. Root alone compiles the candidate.

Append APPEND.lean.txt after the full resource owner. Keep the old owner as an exact prefix. Append PROBES.lean.txt in that same file because the two names remain private. All required APIs are already imported by the owner. No visibility change or new ledger is needed.

The entry helper derives the captured root identity and actual native readback from Entry.enter. It uses actual getValue_root and representative_root to retain uv. The main helper decomposes the completed SelectedPreparation.run, uses the original packet_restart_ne selection law, and returns captured=uv, captured!=held, the literal entry equation, the decoded readback, and the actual SelectedValue.run equation. All original supplied entry/native fuels remain exact.

The original selection caller/cache and the later preparation caller/cache stay separate. The decoded and prepared native values stay separate. No future entry, native lookup, compatibility, model, resource, or output-preservation law is assumed. preparedReady is the genuine current resource precondition before the observed preparation call; its whole-worker source producer remains the existing actual real-prefix resource theorem.

APPLICABILITY-FINDING.md records why an ordinary prepared parent cannot discharge the old d681 ordinary-entry hypothesis in general. It also identifies the existing exact selection exclusion law, so no duplicate selected-flag predicate or framework is introduced. Original d681, full906, and real5493 statements remain unchanged.
