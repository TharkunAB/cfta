def hookOutputs : HookResult Output Reason width → List Output
  | .complete outputs _ _ => outputs
  | .stopped outputs _ _ => outputs

/-- Retain outputs from complete and stopped alternative scans. -/
def foldOutputs : FoldResult Output Reason width → List Output
  | .complete _ outputs _ _ => outputs
  | .stopped _ outputs _ => outputs
