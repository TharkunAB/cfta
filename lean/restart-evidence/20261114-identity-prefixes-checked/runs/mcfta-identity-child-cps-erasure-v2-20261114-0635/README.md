# Exact child CPS transport, second frozen candidate

Status: UNCOMPILED. This candidate preserves all eight theorem headers and all other proof bodies from the first frozen CPS draft. It adds one line, `unfold consumeSelected`, before that lemma's case analysis.

Root's actual receipt diagnostics showed why a hidden done or advance call cannot be replaced by case analysis before its enclosing definition is exposed. The consumeSelected proof has the same structure. This follow-up applies that source-based correction. No compiler result is claimed for either CPS draft.

The first frozen CPS directory and the earlier map module remain unchanged. The eight theorem bodies cover tuple recursion, selected preparation, shallow dispatch, receipt consumption, captured finalization, native-height eager recursion, common preparation, and the eager preparation specialization. They preserve shared complete and stopped results, receipt lists, endpoints, output order, and multiplicity. They add no worker, callback, datatype, or runtime parameter.

`candidate.patch` adds the complete second candidate. `proof-body-followup.patch` changes the first candidate by one proof-body line. `headers.json` checks all eight exact unchanged headers. `source-pins.json` retains the first candidate's source pins. GNU patch forward and inverse replay of the one-line follow-up reproduces both versions exactly with zero fuzz.

The dependency is the earlier five-map module after its scan and receipt proof-body repairs. That repaired candidate is frozen separately in /tmp/mcfta-identity-result-erasure-proof-repairs-20261114-0633. No compiler, live edit, Haskell edit, Git operation, or message board write ran here.
