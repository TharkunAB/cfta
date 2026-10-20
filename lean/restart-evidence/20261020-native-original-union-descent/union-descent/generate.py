from pathlib import Path
p=Path(__file__).resolve().parent
base=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
source=(base/'SourceCurrentNativeOriginalObservedResume.lean').read_text()
source=source.replace('import MicroCFTA.SourceCurrentNativeOriginalObservedTerminals\nimport MicroCFTA.SourceCurrentNativeOriginalBinderResume', 'import MicroCFTA.SourceCurrentNativeOriginalObservedResume')
a=source.index('/-!'); b=source.index('namespace ',a)
source=source[:a]+'''/-!
# Correlated source-union descent for original observed rows

The same source row supplies its terminal call and union-only descent.
The enclosing publication and callback stay fixed across all rows.
Each terminal retains its node call or selected binder writer.
-/
'''+source[b:]
source=source.replace('namespace MicroCFTA.SourceCurrentNativeOriginalObservedResume','namespace MicroCFTA.SourceCurrentNativeOriginalUnionDescent').replace('end MicroCFTA.SourceCurrentNativeOriginalObservedResume','end MicroCFTA.SourceCurrentNativeOriginalUnionDescent')
source=source.replace('open InternedNestedConstruction (Syntax request finish)','open InternedNestedConstruction (Syntax Outcome work request finish)')
source=source.replace('open InternedFreshOrdinaryFacts (callback)','open InternedFreshOrdinaryFacts (callback buildMany_verified)')
source=source.replace('open SourceCurrentNativeOriginalObservedTerminals (Terminal)','open SourceCurrentNativeOriginalObservedResume (SyntaxBound)')
a=source.index('/-- This bound uses');b=source.index('local notation ',a)
inductive='''/-- A terminal follows only exact indexed members of original source unions. -/
inductive UnionDescent {Symbol Guard : Type} : Syntax Symbol Guard → Syntax Symbol Guard → Prop where
  /-- The selected terminal is the current source expression. -/
  | refl (expression : Syntax Symbol Guard) : UnionDescent expression expression
  /-- The same indexed source member retains its terminal descent. -/
  | member {members : List (Syntax Symbol Guard)} {expression terminal : Syntax Symbol Guard} {index : Nat}
      (selected : members[index]? = some expression) (nested : UnionDescent expression terminal) :
      UnionDescent (Syntax.union members) terminal

variable {Symbol Guard : Type}

'''
joint=(base/'SourceCurrentSourceRowTerminalSuffix.lean').read_text()
a2=joint.index('theorem terminal_source');b2=joint.index('\nend MicroCFTA.',a2)
joint=joint[a2:b2].replace('theorem terminal_source','private theorem terminal_suffix',1)
joint=joint.replace('SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧\n', 'SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧\n      UnionDescent expression terminalExpression ∧\n',1)
joint=joint.replace('SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧\n', 'SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧\n        UnionDescent currentExpression terminalExpression ∧\n',1)
joint=joint.replace('state,.capture found inside,?_,', 'state,.capture found inside,.refl _,?_,')
joint=joint.replace('stop,.node built made canonical call same,?_,', 'stop,.node built made canonical call same,.refl _,?_,')
joint=joint.replace('terminalSource,nonunion,terminalContext,terminalReached,terminalBound,terminalGrowth,terminalIssued⟩', 'terminalSource,terminalDescent,nonunion,terminalContext,terminalReached,terminalBound,terminalGrowth,terminalIssued⟩',1)
joint=joint.replace('terminalSource,nonunion,terminalContext,terminalReached,Nat.le_trans terminalBound memberBound,', 'terminalSource,.member syntaxSelected terminalDescent,nonunion,terminalContext,terminalReached,Nat.le_trans terminalBound memberBound,')
joint=joint.replace('.binder depthDone ordinaryDone requested present returned inside,?_,currentContext,currentReached,', '.binder depthDone ordinaryDone requested present returned inside,.refl _,?_,currentContext,currentReached,')
original=(base/'SourceCurrentNativeOriginalRowTerminals.lean').read_text()
a3=original.index('private theorem source_done');b3=original.index('/-- An original source row',a3)
source_done=original[a3:b3]
a3=original.index('theorem terminal [');b3=original.index('\nend MicroCFTA.',a3)
terminal=original[a3:b3].replace('theorem terminal [','private theorem terminal_original [',1)
terminal=terminal.replace('sizeOf terminalExpression ≤ sizeOf expression ∧', 'SyntaxBound terminalExpression expression ∧\n      UnionDescent expression terminalExpression ∧',1)
terminal=terminal.replace('terminalSource,nonunion,terminalContext,terminalReached,bound,growth,issued⟩', 'terminalSource,descent,nonunion,terminalContext,terminalReached,bound,growth,issued⟩',1)
terminal=terminal.replace('SourceCurrentSourceRowTerminalSuffix.terminal_source context reached source', 'terminal_suffix context reached source')
terminal=terminal.replace('terminalSource,source_done terminalSource,kind,nonunion,terminalContext,terminalReached,bound,growth,issued⟩', 'terminalSource,source_done terminalSource,kind,nonunion,terminalContext,terminalReached,bound,descent,growth,issued⟩')
source=source[:a]+inductive+joint+'\n\n'+source_done+terminal+'\n\n'+source[b:]
source=source.replace('SyntaxBound terminalExpression event.expression ∧\n', 'SyntaxBound terminalExpression event.expression ∧\n      UnionDescent event.expression terminalExpression ∧\n')
source=source.replace('(row : EdgeValue Symbol Guard) (terminal : Terminal original event.expression rawAfter row) :', '''(callbackReached : Reached original [] event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated)
    (row : EdgeValue Symbol Guard)
    (source : SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated raw rawAfter row) :''')
source=source.replace('source,done,kind,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued⟩ := terminal', '''terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued⟩ :=
    terminal_original context callbackReached source''',1)
source=source.replace('source,done,kind,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,?_', 'terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued,?_',1)
source=source.replace('  · cases source with\n', '  · cases terminalSource with\n',1)
source=source.replace('terminalBefore terminalRaw terminalAfter row source suffix suffixIssued⟩','terminalBefore terminalRaw terminalAfter row terminalSource suffix suffixIssued⟩',1)
source=source.replace('''    callbackReached,rows,unfolds⟩ :=
    SourceCurrentNativeOriginalObservedTerminals.of_observed original empty sourceHeap
      key entry body depth ordinary current observed''','''    callbackReached,rows,unfolds⟩ := observed''',1)
source=source.replace('obtain ⟨rawRow,source,terminal⟩ := rows row inside','obtain ⟨rawRow,source⟩ := rows row inside',1)
source=source.replace('event raw rawAfter context built filtered growth issued row terminal','event raw rawAfter context built filtered growth issued callbackReached row source',1)
source=source.replace('obtain ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source,terminal⟩ := anchors row literal','obtain ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source⟩ := anchors row literal',1)
source=source.replace('event raw rawAfter context built filtered growth issued originalRow terminal','event raw rawAfter context built filtered growth issued callbackReached originalRow source',1)
(p/'SourceCurrentNativeOriginalUnionDescent.lean').write_text(source)
print({'lines':len(source.splitlines()),'oldTerminalConsumers':source.count('SourceCurrentNativeOriginalObservedTerminals.of_observed'),'newDescentConjuncts':source.count('UnionDescent event.expression terminalExpression')})
