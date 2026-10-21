# Initial draft generator only. Later repairs are retained in numbered snapshots.
from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');here=Path(__file__).resolve().parent
text=(root/'SourceCurrentOuterParentHistory.lean').read_text()
text=text[text.index('namespace MicroCFTA.'):]
text=re.sub(r'/--.*?-/', '',text,flags=re.S)
text=text.replace('SourceCurrentOuterParentHistory','SourceCurrentOuterSupportedParentHistory')
text=re.sub(r'\bWritten\b','SupportedWritten',text);text=re.sub(r'\bOrigins\b','SupportedOrigins',text)
text=text.replace('local notation "NativeGood"', '''local notation "Support" => SourceCurrentMergePositivePosition.Support
local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeGood"''',1)
text=text.replace('variable {width : Nat}', '''variable {width : Nat}

private abbrev Entry (before : Caller width) : Prop :=
  Support before.merge ∧ UnionNormal before.checked.native.machine.heap ∧
    GuardHeap Plain before.checked.native.machine.heap''',1)
text=text.replace('''    NativeGood before ∧ SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo ∧
    (SourceEquality''','''    NativeGood before ∧ SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo ∧
    Support memo ∧ UnionNormal before.native.machine.heap ∧ GuardHeap Plain before.native.machine.heap ∧
    (SourceEquality''',1)
# Record a triple only at the actual entry of this writer.
text=text.replace('''(ready : EdgeReady before request) (origins : SupportedOrigins before) :
    SupportedOrigins after ∧ after.edgeResults''','''(ready : EdgeReady before request) (origins : SupportedOrigins before) (entry : Entry before) :
    SupportedOrigins after ∧ after.edgeResults''',1)
text=text.replace('''memo,observed,good.checked,good.stored,
      fun _''','''memo,observed,good.checked,good.stored,entry.1,entry.2.1,entry.2.2,
      fun _''',1)
# Public cold/warm interface has no private Entry predicate in its type.
text=text.replace('''(ready : EdgeReady before request) (origins : SupportedOrigins before) :
    SupportedOrigins after ∧ SupportedWritten''','''(ready : EdgeReady before request) (origins : SupportedOrigins before)
    (support : Support before.merge) (normal : UnionNormal before.checked.native.machine.heap)
    (guards : GuardHeap Plain before.checked.native.machine.heap) :
    SupportedOrigins after ∧ SupportedWritten''',1)
text=text.replace('''  have initial := begin_good request good ready
  have prior := begin_origins request origins''','''  have initial := begin_good request good ready
  have prior := begin_origins request origins
  have entry : Entry (beginEdge request before).2.2 := by
    have components := beginEdge_components request before
    exact ⟨components.2.1 ▸ support, components.1 ▸ normal, components.1 ▸ guards⟩''',1)
text=text.replace('rw [started] at initial prior','rw [started] at initial prior entry',1)
text=text.replace('edge_body body initial (initial.edges.checked _ _ found).1 prior','edge_body body initial (initial.edges.checked _ _ found).1 prior entry',1)
# All six completed phases carry the same entry laws in private proof bookkeeping.
text=text.replace('→ SupportedOrigins before → SupportedOrigins after','→ Entry before → SupportedOrigins before → SupportedOrigins after')
text=text.replace('''    Good (width := width) before → NodeReady before request → SupportedOrigins before → SupportedOrigins after''','''    Good (width := width) before → NodeReady before request → Entry before → SupportedOrigins before → SupportedOrigins after''')
# One actual-prefix adapter reuses the three independent preservation producers.
needle='''private def NodeAt (fuel : Nat)'''
entry='''private theorem entry_reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (entry : Entry (caller first)) :
    Entry (caller last) :=
  ⟨SourceCurrentOuterMergePositionSupport.reached actual good inputs entry.1,
    SourceCurrentOuterUnionNormalHistory.reached actual entry.2.1,
    SourceCurrentOuterGuardHeapReturns.reached Plain actual good inputs entry.2.2⟩

'''
text=text.replace(needle,entry+needle,1)
text=text.replace('ready available origins\n','ready available entry origins\n')
text=text.replace('ready resident origins\n','ready resident entry origins\n')
text=text.replace('request before value after actual good ready origins\n','request before value after actual good ready entry origins\n')
# Actual earlier-child and earlier-row receipts supply the next entry laws.
text=text.replace(')).1 first child.1 child.2 origins',')).1 first child.1 child.2 (by exact entry) origins')
text=text.replace('''remaining.2.1 remaining.2.2 current''','''remaining.2.1 remaining.2.2
            (entry_reached (.snoc (.refl _) (.walk_tail first)) good ⟨ready,available⟩ entry) current''',1)
text=text.replace('''good ready available origins
    have descendantsAt''','''good ready available entry origins
    have descendantsAt''',1)
text=text.replace('childrenAt first start.1 start.2.1 start.2.2 origins','childrenAt first start.1 start.2.1 start.2.2 (by exact entry) origins')
text=text.replace('''(edge_call first good ⟨ready,resident _ List.mem_cons_self⟩ origins).1''','''(edge_call first good ⟨ready,resident _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1''')
text=text.replace('''childrenDone child.1 child.2.1 child.2.2 current''','''childrenDone child.1 child.2.1 child.2.2
            (entry_reached (.snoc (.refl _) (.rows_edge first)) good ⟨ready,resident⟩ entry) current''')
text=text.replace('''remaining.2.1 remaining.2.2 next''','''remaining.2.1 remaining.2.2
            (entry_reached (.snoc (.refl _) (.rows_tail first childrenDone)) good ⟨ready,resident⟩ entry) next''')
text=text.replace('''first good ready.1 resident origins''','''first good ready.1 resident entry origins''')
text=text.replace('''bodyAt body current.1 current.2 prior''','''bodyAt body current.1 current.2
          (entry_reached (.snoc (.refl _) (.node_evaluate started)) good ready entry) prior''')
# Private completed-node and step wrappers.
text=text.replace('''(ready : NodeReady before request) (origins : SupportedOrigins before) :
    SupportedOrigins after := (all_done fuel).1 actual good ready origins''','''(ready : NodeReady before request) (entry : Entry before) (origins : SupportedOrigins before) :
    SupportedOrigins after := (all_done fuel).1 actual good ready entry origins''')
text=text.replace('''(inputs : Inputs first) (origins : SupportedOrigins (caller first)) :
    SupportedOrigins (caller last) := by''','''(inputs : Inputs first) (entry : Entry (caller first)) (origins : SupportedOrigins (caller first)) :
    SupportedOrigins (caller last) := by''',1)
text=text.replace('''(edge_call actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins).1''','''(edge_call actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1''')
text=text.replace('''(edge_call edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins).1''','''(edge_call edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1''')
text=text.replace('''children child.1 child.2.1 child.2.2 current''','''children child.1 child.2.1 child.2.2
      (entry_reached (.snoc (.refl _) (.rows_edge edge)) good inputs entry) current''')
text=text.replace('''node_done actual child.1 child.2 origins''','''node_done actual child.1 child.2 (by exact entry) origins''')
# Public reached interface keeps the three laws explicit.
text=text.replace('''(inputs : Inputs first) (origins : SupportedOrigins (caller first)) :
    SupportedOrigins (caller last) := by''','''(inputs : Inputs first) (origins : SupportedOrigins (caller first))
    (support : Support (caller first).merge) (normal : UnionNormal (caller first).checked.native.machine.heap)
    (guards : GuardHeap Plain (caller first).checked.native.machine.heap) :
    SupportedOrigins (caller last) := by''',1)
text=text.replace('''exact step_origins last current.1 current.2 ih''','''exact step_origins last current.1 current.2
      (entry_reached earlier good inputs ⟨support,normal,guards⟩) ih''')
header='''import MicroCFTA.SourceCurrentOuterMergePositionSupport
import MicroCFTA.SourceCurrentOuterParentHistory
import MicroCFTA.SourceCurrentOuterUnionNormalHistory
import MicroCFTA.SourceCurrentOuterGuardHeapReturns
import MicroCFTA.SourceCurrentOuterOwnerSelection
import MicroCFTA.SourceCurrentParentGuardHeapReturns
import MicroCFTA.SourceCurrentUnionNormalScan

/-!
# Support and causal heap facts at the same historical Parent writer

Cold publication records three entry laws with its exact Parent execution.
Warm hits recover that certificate for the same complete captured request.
Actual outer prefixes need no future root return. Internal failures are outside
this contract. GuardHeap Plain records Mu profile equality, not plainness of
all stored guards.
-/
'''
text=re.sub(r'\n\n\n+', '\n\n',text)
(here/'SourceCurrentOuterSupportedParentHistory.lean').write_text(header+text)
