from pathlib import Path
import re
h=Path(__file__).resolve().parent
old=Path('/tmp/mcfta-native-original-captured-fixture')
s=(old/'original-kernels.lean').read_text().replace('import MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows','import MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows\nimport MicroCFTA.SourceCurrentNativeOriginalObservedTerminals').replace('OriginalCapturedMuFixture','OriginalCapturedTerminalFixture').replace('actual_initial_capture','actual_initial_terminal')
s=s.replace('# An initial shared Mu retains its original source callback','# An initial shared Mu retains its original source terminals')
s=s.replace('Its actual unfold row retains one original source publication and callback.','Its actual unfold row retains one original source publication and callback.\nThe same stored and observed rows retain their source terminal suffixes.')
s=s.replace('event.allocated raw rawAfter row) ∧','event.allocated raw rawAfter row ∧\n          SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter row) ∧')
s=s.replace('event.allocated raw rawAfter original) ∧','event.allocated raw rawAfter original ∧\n              SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter original) ∧')
s=s.replace('event.allocated raw rawAfter storedRow)', 'event.allocated raw rawAfter storedRow ∧\n        SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter storedRow)')
s=s.replace('''  · obtain ⟨prior,observed⟩ := capturedInitial
    obtain''','''  · obtain ⟨prior,observed⟩ := capturedInitial
    have enriched := SourceCurrentNativeOriginalObservedTerminals.of_observed expression empty
      before.native.machine.heap entry.key entry stored depth ordinary current.native.machine.heap observed
    obtain''')
s=s.replace('storedRows,everyUnfold⟩ := observed','storedRows,everyUnfold⟩ := enriched')
s=s.replace('⟨original,inside,symbol,guard,arity,calls,rawRow,source⟩','⟨original,inside,symbol,guard,arity,calls,rawRow,source,terminal⟩')
s=s.replace('arity,actualCalls,rawRow,source⟩','arity,actualCalls,rawRow,source,terminal⟩')
s=s.replace('An actual initial Mu capture retains its original source and changed unfold child calls.','An actual initial Mu capture retains the same original source terminal and changed unfold calls.')
(h/'terminal-kernels.lean').write_text(s)
for a,b in [('original-kernels-run-check.py','terminal-kernels-run-check.py'),('original-kernels-capped-worker.py','terminal-kernels-capped-worker.py')]:
 t=(old/a).read_text().replace('original-kernels','terminal-kernels').replace('ORIGINAL_KERNELS','TERMINAL_KERNELS');(h/b).write_text(t)
