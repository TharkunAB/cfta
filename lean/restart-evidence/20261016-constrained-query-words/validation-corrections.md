# Final probe correction

The frozen scan-ranges-kernels-1.log contains one unused-variable warning.
The existential witness binder `actual` is not used in its predicate.
The component validation note incorrectly states that this log has no warning.
The production theorem and the existential witness proof are valid.

The final probe is scan-ranges-kernels-final.lean. It changes only that
binder to `_actual`. Its final log is scan-ranges-kernels-final-1.log.
Both axiom and full-signature pairs pass without errors, warnings, or
placeholders. The aggregate verifier uses this final probe and log.
The earlier frozen source, log, validation note, and manifest retain their
bytes. No production source changes or new canonical build is needed.
