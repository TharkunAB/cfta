from pathlib import Path
p=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationParkedTwoResources.lean')
s=p.read_text().replace('import MicroCFTA.SourcePruningEnumerationTwoExpansionForecast','import MicroCFTA.SourcePruningEnumerationFiniteContract').replace('import MicroCFTA.SourcePruningEnumerationRunOneResources\n','')
s=s.replace('# A parked first expansion followed by the actual depth-one driver','# A parked first expansion followed by the remaining finite driver')
s=s.replace('actual depth-one restart','actual smaller-depth restart').replace('remaining recursive step','remaining recursive steps')
s=s.replace('parked_two_complete_resources','parked_finite_complete_resources').replace('actual parked depth-two outcome','actual parked finite-depth outcome')
s=s.replace('(solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)', '''(solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)''')
s=s.replace('(prefixFuel uv : Nat) (checked : Cached) (seed : Seed)', '(prefixFuel uv : Nat) (checked : Cached) (seed : Seed) (ceiling : Nat)')
s=s.replace('(reserved : SourcePruningEnumerationTwoExpansionForecast.Reserved bits seed before.core)', '''(initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits (recursiveFuel + 1) seed ceiling)''')
s=s.replace('(bound + extra) 2\n', '(bound + extra) (recursiveFuel + 1)\n')
s=s.replace('(SourcePruningEnumerationTwoExpansionForecast.final seed before.core)', '(SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling)')
s=s.replace('have growth := SourcePruningEnumerationTwoExpansionForecast.final_ge seed before.core','have growth := SourcePruningEnumerationFiniteReservation.final_ge (recursiveFuel + 1) seed ceiling')
a=s.index('  · let parkedSeed :=')
b=s.index('    intro extra\n',a)
s=s[:a]+'''  · let start := SourcePruningEnumerationExpansionAdmission.narrowSeed seed
    let parkedSeed := SourcePruningEnumerationRecursiveReservation.afterHead start ceiling
    let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
    have narrowGrowth := SourcePruningEnumerationFiniteReservation.narrowSeed_ge seed
    have headGrowth := SourcePruningEnumerationRecursiveReservation.afterHead_ge start ceiling
    have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
    have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
      fun key edge resident => headGrowth.2 (narrowGrowth.2 (known key edge resident))
    have boundedMass : SourcePruningEnumerationPrefixAdmission.suspendedBound checked.core ≤ parkedMass :=
      Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
      selectionMembers selectionLength boundedMass reserved.first.2
    have growth := SourcePruningEnumerationFiniteReservation.first_le_final recursiveFuel seed ceiling
    refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources.mono growth.1 growth.2⟩
'''+s[b:]
s=s.replace('(prefixFuel + resumeFuel + extra) 1 metadata', '(prefixFuel + resumeFuel + extra) recursiveFuel metadata')
Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationFiniteParkedResources.lean').write_text(s)
