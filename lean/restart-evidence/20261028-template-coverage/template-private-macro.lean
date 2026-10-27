import MicroCFTA.SourcePruningTemplates
local macro "oldStructuralProgram" : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.MicroCFTA.SourcePruningTemplates 0) ++
    `MicroCFTA.SourcePruningTemplates.structuralProgram))
local macro "oldMatchChildren" : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.MicroCFTA.SourcePruningPartialMatch 0) ++
    `MicroCFTA.SourcePruningPartialMatch.matchChildren))
#check oldStructuralProgram
#check oldMatchChildren
