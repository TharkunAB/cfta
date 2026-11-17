# Proof binder alpha names

The first frozen definitions bd092931 are retained unchanged. The assembled declarations use TARGET-DEFINITIONS-ALPHA.lean.txt. Only three unused forall proof binder names change from heldScope to _heldScope. The arguments, order, proposition, declaration names and runtime are unchanged. This avoids the strict unused-variable lint for a proof argument that is consumed by the theorem but not referenced in the target proposition. Do not claim byte identity for this alpha spelling.
