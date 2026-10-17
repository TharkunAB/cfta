# Reviewed current preparation declarations

Source SHA256: 24534bc63167c1ef51074234e81e3a2193f04eac1799726f6bbe7a749759c916

```lean
40: inductive Execution (budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
57: inductive Reads : {budget : Nat} → {records : List Record} → {values results : List (Value Symbol Guard)} →
76: structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
81:   actual : Execution budget records values before.checked before.fourth outcome kept results after saved
83:   reads : Reads actual memos final
85:   frame : Frame formulas solver inventory after
87:   fits : Fits (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
90:   post : Post formulas solver inventory before (advance before after saved before.merge) final
92:   originals : Values after.native.machine.heap values
94:   available : Values after.native.machine.heap results
96:   length : results.length = values.length
98:   selected : kept.Sublist records
100:   domains : outcome = none → ∀ record ∈ kept, ∀ path ∈ record.paths,
103:   rejected : SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values (records.map Record.paths) outcome
105:   language : ∀ ambient symbol terms,
112:   ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget source reaches values
115:   run : ∀ g s r p h n, fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ g →
125: theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
```
