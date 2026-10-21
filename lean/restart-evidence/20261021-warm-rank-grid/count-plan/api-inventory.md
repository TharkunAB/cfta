Actual installed Lean version: leanprover/lean4:v4.34.1, from lean/lean-toolchain.
List.flatMap_nil / List.flatMap_cons: Init/Data/List/Basic.lean688–690.
List.length_append: Init/Data/List/Basic.lean631–634.
List.zipIdx_nil / List.zipIdx_cons: Init/Data/List/Basic.lean2149–2150; zipIdx has an explicit optional start index.
List.length_map: Init/Data/List/Lemmas.lean1081–1084.
List.length_filter_le (p : α → Bool) (l : List α): Init/Data/List/Lemmas.lean1272–1281.
List.mem_eraseDups [BEq α] [LawfulBEq α]: Init/Data/List/Lemmas.lean3762–3764.
List.Nodup.length_le_of_subset {l₁ l₂} (h₁ : l₁.Nodup) (hsub : l₁ ⊆ l₂): Init/Data/List/Perm.lean487–488.
SymbolicDriver.eraseDups_nodup [BEq Value] [LawfulBEq Value] (values): SymbolicSelection.lean23–35; already imported transitively and used in the current count proof.
InternedValueMass.edge_children: InternedValueMass.lean53–55.
Use literal local list induction instead of a new sum/zip framework; length_flatMap exists but is unnecessary for the selected route.
All cited source files and exact ranges are snapshotted in source-index.json. No compiler command was used to discover these names.
