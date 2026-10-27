from pathlib import Path
out=Path('/tmp/mcfta-recursive-history-resources-20261027/invocation-admission-draft')
p=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationInvocationReceipts.lean');s=p.read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationHeadAdmission','import MicroCFTA.SourcePruningEnumerationCallbackAdmission',1)
s=s.replace('''# Full head receipts on actual recursive sibling paths

The original resource schedule supplies each native head and callback.
Each suffix starts at the actual post-hook caller and full memo state.
Every observed hook input retains its own stable completed head receipt.''','''# Original callback admission on actual recursive sibling paths

Each invocation retains its full existing completed head receipt.
Its callback admission uses that same cache, caller and full memos.
Each suffix starts at the actual post-hook native endpoint.''',1)
s=s.replace('local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead','local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead\nlocal notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil',1)
s=s.replace('/-- Original admission supplies full receipts for every actual invoked recursive hook. -/','/-- Original admission supplies each actual invoked hook and its callback reservation. -/',1)
s=s.replace('theorem alternatives_finite_invocation_receipts','theorem alternatives_finite_invocation_admissions',1)
s=s.replace('''          fragment reached saved after returnedInventory returnedMemos := by''','''          fragment reached saved after returnedInventory returnedMemos ∧
        SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver returnedInventory
          reached returnedMemos metadata after uv fragment recursiveFuel
          (afterHead headSeed inherited) (massCeil headSeed capturedMass inherited) := by''',1)
s=s.replace('''        _headFits, _headKnown, shape, completedReceipt⟩ :=''', '''        _headFits, _headKnown, shape, completedReceipt, callbackAdmission⟩ :=''',1)
s=s.replace('''SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_with_receipt''','''SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_with_callback_admission''',1)
s=s.replace('''                  completedReceipt fragment reached saved after same⟩''','''                  completedReceipt fragment reached saved after same,
                  callbackAdmission fragment reached saved after same⟩''')
s=s.replace('''                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate⟩ := tailAt tail''','''                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate, admission⟩ := tailAt tail''')
s=s.replace('''                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead, certificate⟩''','''                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead,
                  certificate, admission⟩''')
assert s.count('head_finite_complete_resources_with_callback_admission')==1
assert s.count('callbackAdmission fragment reached saved after same')==2
assert s.count('certificate, admission⟩')==4
(out/'SourcePruningEnumerationInvocationAdmission.lean').write_text(s)
(out/'revisions/001-initial.lean').write_text(s)
