# Live fixed support for callback normalization

Checked on 2026-10-17 in Europe/Stockholm.
Production: `SourceCurrentNativeNormalizationInputs.lean`.
SHA256: `fdc8f1c7bb408770dc17a25e5fd16c2201da4ddf8f9e51a4ef971960ac21840b`.

The module derives support and freshness facts for actual full source builds.
It labels fixed free names separately from varying input slots.
`instantiated` commutes this support with each assignment of varying references.
`actual_free` identifies that support with the free names of the actual raw result.
`fixed_origin` traces each surviving fixed name to an actual fixed captured record.
`callback_fixed` retains a live fixed name distinct from the supplied callback argument.
`ordinary_fresh_fixed` uses an actual completed Depth callback to exclude its chosen ordinary name from live fixed support.
`reserved_fresh_fixed` uses actual source availability and a missing node key to exclude the new interned identity from fixed support.
The missing-key premise is explicit. An existing warm identity need not be fresh.
The theorems admit arbitrary available fixed captures, including open Mu values.
They require no desired comparison result, output-origin law, Cap, or whole-input closure.

Direct attempt 2 passes with an empty strict log.
The canonical build passes 278 jobs. Public group 1 checks and prints all eight public declarations and their axioms.
Kernel group 5 checks two initial source constructions with no caller premises.
The first construction discards a fixed capture that equals the chosen ordinary name, but retains a varying input.
It proves that the chosen name is absent from live fixed support.
The second construction builds an open raw Mu from empty, then runs actual Depth and ordinary callbacks beside that captured Mu.
It proves that the fixed name 7 survives, the chosen ordinary name is fresh, and an actual missing-key reservation supplies a fresh interned name.
All final checks use Lean 4.34.1, all eight explicit probe options, and effective limits 4 GiB/4 GiB/swap 0.
The final axiom reports contain only propext, Classical.choice, and Quot.sound, or no axioms.
All failed sources and raw logs remain. Kernel attempt 3 failed before Lean because the sandbox could not access the user bus.

The main simultaneous comparison remains open.
A nested smart binder with an unused local argument can return a root union that still contains an outer varying bare reference.
That varying slot remains live, so the existing LiveInputReplay input-agreement premise does not hold.
Free-name and deep-name observations do not prove equality of the retained ordered record alternatives.
The new freshness facts permit fresh labels for nested ordinary and reserved arguments. They do not derive that missing record relation.
RootErasure and RecordErasure can compare actual erased results once stripped alternatives agree, but this module does not assume or produce that agreement.
The remaining producer must derive the normalized alternative relation together with the corresponding causal law for each actual older Mu winner.
It must establish the fresh candidate law before publication, then use the previously produced law for a keep-first hit.
No theorem here equates a warm Mu body with its ordinary probe or exchanges the original callback inputs after normalization.
No Haskell defect or whole-library completion is claimed.
