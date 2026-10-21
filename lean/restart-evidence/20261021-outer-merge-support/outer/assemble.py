# This script produced the initial direct-1 draft. Later checked repairs are retained in the final source and numbered snapshots.
from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
here=Path(__file__).resolve().parent
namespace='MicroCFTA.SourceCurrentOuterMergePositionSupport'
names=['Target','Lower','Parent','Outer']
parts=[]
for name in names:
 old='SourceCurrent'+name+'MergeHistory'
 text=(root/(old+'.lean')).read_text()
 text=text[text.index('namespace MicroCFTA.'):]
 text=re.sub(r'/--.*?-/', '',text,flags=re.S)
 for component in names:
  text=text.replace('SourceCurrent'+component+'MergeHistory','SourceCurrentOuterMergePositionSupport')
 text=text.replace('open SourceCurrentMergePositiveRowOrigins (Raw)','open SourceCurrentMergePositivePosition (Support)')
 text=text.replace('local notation "Raw" => SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear\n  (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula))','open SourceCurrentMergePositivePosition (Support)')
 text=text.replace('local notation "Raw" => SourceCurrentMergePositiveRowOrigins.Raw','open SourceCurrentMergePositivePosition (Support)')
 text=text.replace('Raw literalClear top','Support')
 text=re.sub(r'\bRaw\b','Support',text)
 text=re.sub(r'\braw\b','support',text)
 for word in ['initial','head','tail','edge','first']:
  text=text.replace(word+'Raw',word+'Support')
 text=re.sub(r'private theorem empty_raw.*?cases found\n\n','',text,flags=re.S)
 text=re.sub(r'\bempty_raw\b','SourceCurrentMergePositivePosition.support_empty',text)
 def privacy(m):
  head=m.group(1)
  return ('theorem ' if (name=='Parent' and head=='parent') or (name=='Outer' and head in ['reached','initial_reached']) else 'private theorem ')+head
 text=re.sub(r'(?m)^theorem (\w+)',privacy,text)
 if name=='Target':
  text=text.replace('open Cache InternedConstructorTemplates InternedProbeProvenance','open Cache InternedConstructorTemplates InternedProbeProvenance\nopen SourceCurrentAllocatedNativeEffects (physical)')
  text=text.replace('''  have merged := SourceCurrentAllocatedTargetWorkerSound.merge_sound
    m s projected middle memo result after saved mergeDone
''','')
  start=text.index('  cases merged with')
  stop=text.index('\nprivate theorem target_leaf_memo',start)
  text=text[:start]+'''  cases called : SourceCurrentAllocatedMergeWorker.call literalClear m s projected (physical middle) memo with
  | failed =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
  | done output final current =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
      exact (SourceCurrentMergePositivePosition.allocated literalClear called currentSemantic currentCosts
        currentStored support currentAvailable).2.2.1
''' +text[stop:]
 text=re.sub(r'\n\n\n+', '\n\n',text)
 parts.append(text)
header='''import MicroCFTA.SourceCurrentOuterMergeHistory
import MicroCFTA.SourceCurrentMergePositivePosition

/-!
# Positive-position Merge support at actual outer prefixes

The proof follows successful lower calls and actual unfinished outer phases.
It does not cover an internal failed Parent or failed Merge return.
The current table law does not supply the law at a historical writer entry.
-/
'''
text=header+'\n'.join(parts)
text=text.replace('theorem parent [','/-- A completed literal Parent call preserves its initial Merge support law. -/\ntheorem parent [')
text=text.replace('theorem reached {','/-- Every actual outer prefix preserves its initial Merge support law. -/\ntheorem reached {')
text=text.replace('theorem initial_reached {','/-- An outer prefix from empty Merge tables derives the support law without a future return. -/\ntheorem initial_reached {')
(here/'SourceCurrentOuterMergePositionSupport.lean').write_text(text)
