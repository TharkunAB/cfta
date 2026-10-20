from pathlib import Path
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
h=Path(__file__).resolve().parent
header='''import MicroCFTA.SourceCurrentNativeTracePrefixBind
import MicroCFTA.SourceCurrentNativeEdgeWriterRetention

/-!
# Actual returned writers through unfinished native prefixes

A reached state retains the historical bodies of its returned cells.
An enclosing compiler owner can still be evaluating. The conclusion does
not assign a completed-trace History to that reached state.
-/
namespace MicroCFTA.SourceCurrentNativePrefixWriterMaps
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (effects fields_before_bind)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
'''
parts=[header]
for family,old in [('Node','SourceCurrentNativeWriterReadyRetention'),('Edge','SourceCurrentNativeEdgeWriterRetention')]:
 s=(root/(old+'.lean')).read_text()
 start=s.index('private theorem later ')
 end=s.index('/-- The existing actual causal history') if family=='Node' else s.index('private theorem history_recorded')
 s=s[start:end].rstrip()
 s=s.replace('    (value : A),','    (final : Control A),') if False else s
 s=s.replace('(before after : Checked width) (value : A),','(before after : Checked width) (final : Control A),')
 s=s.replace('Trace fuel control before (.code (.pure value)) after → Recorded after.native','Trace fuel control before final after → Recorded after.native')
 s=s.replace('intro A control before after value clean good fields known trace','intro A control before after final clean good fields known trace')
 # Recursive calls carry the exact arbitrary remaining control.
 s=s.replace('_ after value ', '_ after final ').replace('middle after value ', 'middle after final ')
 # Generalize both protected-body splits. Each source file has exactly two.
 needle='obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest'
 while needle in s:
  start=s.index(needle)
  fieldstart=s.index('have bodyFields :=',start)
  knownstart=s.index('have bodyKnown :=',fieldstart)
  split=s[start:fieldstart]
  bodyFields=s[fieldstart:knownstart]
  # Source body control and protected continuation are the next two lines.
  lines=split.splitlines()
  ctrl=lines[1].strip()
  # ctrl line contains control then continuation, e.g (.code (compileNode actual)) (fun result => ...)
  if 'compileNode' in ctrl:
   control='(.code (compileNode actual))'; continuation='(fun result => .finishNode handle result (continuation result))'; clean='(compileNode_bodyCode actual)'
  else:
   control='(.edgeBody actual .pure)'; continuation='(fun result => .finishEdge handle result (continuation result))'; clean='(by intro value; trivial)'
  indent=' '* (len(s[:start].split('\n')[-1]))
  # Original indentation is included before start in the source string.
  # Body-field block is placed before both cases.
  bf=bodyFields.rstrip()
  bf=bf[:bf.rfind('\n')] if False else bf
  repl=bf+'\n'+indent+f'rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases rest\n'+indent+'    '+control+' '+continuation+'\n'+indent+'    ⟨running,before.operations⟩ after final tail with\n'+indent+'  ⟨innerRest,bodyTrace,_nonpure,_same⟩ |\n'+indent+'  ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩\n'+indent+'· exact ih rest (by omega) '+control+' _ after innerRest '+clean+'\n'+indent+'    next.1 bodyFields runningKnown bodyTrace\n'+indent+'· '
  # Need indent original completed-arm block to keep it inside second branch.
  # Determine the end: next code-constructor branch, or end of preserves.
  # All split blocks terminate immediately before another '| edge' branch or at EOF.
  nextbranch=s.find('\n        | edge request continuation =>',knownstart)
  blockend=nextbranch if nextbranch!=-1 else len(s)
  block=s[knownstart:blockend]
  # Completed body IH now uses an actual pure control, not the final result variable.
  block=block.replace('_ current result ', '_ current (.code (.pure result)) ')
  # Exact zero-step protected suffix is a valid prefix stop before finish.
  marker='cases frameTrace with\n'
  pos=block.index(marker)+len(marker)
  restlines=block[pos:]
  consindent=restlines[:len(restlines)-len(restlines.lstrip())]
  block=block[:pos]+consindent+'| refl => exact bodyKnown\n'+block[pos:]
  # Starting bodyKnown is already preceded by branch bullet; subsequent lines gain two spaces.
  blocklines=block.splitlines()
  indented=blocklines[0]+'\n'+'\n'.join('  '+line if line else '' for line in blocklines[1:])
  s=s[:start]+repl+indented+s[blockend:]
 s=s.replace('SourceCurrentNativeWriterReadyRetention.trace_retained','SourceCurrentNativeWriterReadyRetention.trace_retained')
 parts.append('\nnamespace '+family+'\nlocal notation "Written" => '+old+'.Written\n'+s+'\nend '+family+'\n')
parts.append('''
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual clean prefix derives both returned-writer maps at its same reached native state. -/
theorem prefix {A : Type} (control : Control A) (before after : Checked width)
    (final : Control A) (fuel : Nat)
    (clean : Clean control) (good : Good before) (fields : Fields control before)
    (history : History before) (actual : Trace fuel control before final after) :
    (∀ handle request result, after.native.nodes.cells handle = some ⟨request,.returned result⟩ →
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle request result after.native) ∧
    (∀ handle request result, after.native.edges.cells handle = some ⟨request,.returned result⟩ →
      SourceCurrentNativeEdgeWriterRetention.Written (width := width) handle request result after.native) ∧
    Retained before.native after.native := by
  have nodes : Node.Recorded before.native := SourceCurrentNativeWriterReadyRetention.writers history
  have edges : Edge.Recorded before.native := SourceCurrentNativeEdgeWriterRetention.edge_writers history
  exact ⟨Node.preserves fuel control before after final clean good fields nodes actual,
    Edge.preserves fuel control before after final clean good fields edges actual,
    SourceCurrentNativeWriterReadyRetention.trace_retained actual good.native.shape⟩

end MicroCFTA.SourceCurrentNativePrefixWriterMaps
''')
(h/'SourceCurrentNativePrefixWriterMaps.lean').write_text(''.join(parts))
