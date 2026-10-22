# H9 FULL reader — independent source review (2026-10-22 01:18:40 CEST)
CLEAR for source-only preparation. I read all 103 lines of each reader and the complete point diff.
The retained predecessor is byte-identical to the accepted H8 reader. Four literal naming substitutions reconstruct the entire H9 file and exact patch.
Only the comment, namespace, theorem name and artifact prefix change. No assertion or parser control flow changes.
The reader requires explicit selected source/printer/raw/owned receipt paths and an exact source SHA.
It requires the complete source bytes plus the exact 14-line diagnostic suffix, closed module, and exact one-per-line check/print/axiom directives.
The options remain seven pp settings, one linter setting and two diagnostic limits after the module. The legacy all_eight_printer_settings flag is retained.
It rejects raw diagnostics, sorry, omissions and pretty-print failures, then verifies the owned zero-exit receipt and exact printer/log/input correlation.
Private declarations are parsed from the actual source; unsupported private declaration lines fail closed. All actual helpers and four private/dagger markers are forbidden in TYPE only.
The unique complete declaration boundary and byte-identical checked/printed TYPE are mandatory; private proof-body references remain allowed.
Actual reported axioms are normalized and must be a subset of propext, Classical.choice and Quot.sound. Equality to all three is reported, not assumed.
The complete TYPE pair, BODY and axiom output are retained with byte counts/hashes; preexisting output files are rejected.
Actual source, receipt, metrics and TYPE acceptance remain later gates. This preparation does not verify an unfinished or future proof.
I authored the H7 predecessor tooling, independently reviewed by arity. This is a disclosed adaptation review; I executed no reader/checker/proof/runtime/Git/network action.
