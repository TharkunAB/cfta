# Uncapped editor APIs

## SourceCurrentEditFrame

SHA256: 3b8047ec8c0a22806af4ae2da7d65f9ce597ced4ad64659abbb34419ce33c793

```lean
52: theorem node (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
73: theorem edge (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
96: theorem head (profile : Profile) (frame : Frame formulas solver inventory before.checked)
```

## SourceCurrentEditScans

SHA256: 5ee85c4aec8319a85ee032957d13b3326c95c6df2fe6e25737ae1eb005334f3e

```lean
41: def editFuel (level : Nat) : Nat := 2 * level + 2
44: def NodeComplete (formulas : SourceGuards.Formulas FullSyntax.Formula)
72: theorem children
146: theorem rows
```

## SourceCurrentEditNumeric

SHA256: 7b42a98ece0e2025b028eedfbdd8a9cc604d967e43ea0b3a2936190890b44248

```lean
143: theorem node_complete (level : Nat)
```

## SourceCurrentEditListNumeric

SHA256: 1510f2b692ae2f6d537e19e062582675d0af75306886fb4588739937dd981f4d

```lean
35: noncomputable def finalProfile (record : SourceEqualityClassOrder.Record) (count : Nat)
42: noncomputable def Reserved (bits : Nat) (record : SourceEqualityClassOrder.Record) (count : Nat)
49: noncomputable def fuel (record : SourceEqualityClassOrder.Record) (count : Nat)
57: theorem complete
117: theorem compiled
```
