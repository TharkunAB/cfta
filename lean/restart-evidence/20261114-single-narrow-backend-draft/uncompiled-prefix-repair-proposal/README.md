# Prefix language and checkpoint proof reductions

Status: UNCOMPILED. Root owns compilation and live edits.
The proposals change four proof-body reduction lists in two modules.
All theorem statements, hypotheses, imports and operations remain unchanged.

The actual check8 diagnostics show the configured runPrefix wrapper remaining
opaque in PrefixLanguage.retained_action and all three checkpoint prefixRun proofs.
Reading, checking and preparation receipts therefore do not rewrite the hidden body.
Each candidate adds runPrefixWithNarrow to the existing simp-only list.

The native branch inside that body calls prepareWithNarrow. The existing prepared
or preparedAt receipt names the old configured prepare wrapper. Three lists also
use the reverse direction of prepare_configured_eq. This folds that exact helper
call back to prepare before applying the original receipt. No native result is
invented or assumed. The configured equation already has an rfl proof.

The checkpoint parked branch does not enter preparation. Its reduction list adds
only runPrefixWithNarrow. It does not add an unused preparation-folding rule.

The remaining proof steps stay exact. This includes raw action cases, native
encoding, actual adapter and recordTypes observations, and both final rfl steps.
Root must check these candidates with the compiler and strict warnings.

Source checks prove that reversing the four substitutions recovers every old
byte. All five private/public theorem headers have exact hash comparisons.
Both GNU zero-context patches replay with --batch --fuzz=0 and no offsets.
These checks are source evidence only. No compiler or probe ran here.
No live file, Haskell file or statement changed.

before/ preserves the exact inputs. candidate/ contains the proposals.
patches/ contains the exact deltas. report.json records their hashes and replays.
source-pins.json pins the input modules, actual Action/SelectedStep definitions,
imported completion/packet modules and complete Root diagnostic log.
diagnostic-excerpts.txt retains the relevant original errors.
