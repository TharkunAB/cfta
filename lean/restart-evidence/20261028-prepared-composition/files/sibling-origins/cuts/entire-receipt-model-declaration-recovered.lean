theorem receipt_finite_complete_resources_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked) (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : match (generalizing := false) receipt with
      | .complete _ _ _ after => SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
      match (generalizing := false) receipt with
      | .complete fragment actual saved afterCache =>
          actual = reached ∧ saved = final.query ∧
          ∃ (recorded : Bool × Metadata Typing) (callbackCore : Core),
            Packet formulas solver next actual final metadata afterCache ∧
            FragmentBound afterCache.core.counter fragment ∧
            (Packet formulas solver next actual final recorded.2 (EnumerationExpandableIndex.frame callbackCore afterCache) ∧
            RenderStable afterCache.core callbackCore ∧ Frame afterCache.core callbackCore ∧
            recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
            recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
            (∀ extra,
              Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) afterCache.core recorded callbackCore ∧
              ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) afterCache.core) =
                [.ok (recorded, callbackCore)] ∧
              ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
                continueWith recur graph templates stop order (fuel + extra) metadata uv fragment actual final.query afterCache =
                  if recorded.1 then .complete [] actual final.query
                  else recur recorded.2 actual final.query (EnumerationExpandableIndex.frame callbackCore afterCache)
                    (SourcePruningEnumerationRestart.decision stop order recorded.2
                      (EnumerationExpandableIndex.frame callbackCore afterCache))) ∧
            (∀ extra, continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual final.query afterCache = outcome) ∧
            OutcomeResources formulas solver actual
              (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
            (∀ (language : NodeLanguage Symbol)
              (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
              Satisfies language meaning assignment (EnumerationExpandableIndex.frame callbackCore afterCache).core ↔
                Satisfies language meaning assignment afterCache.core) ∧
            ∀ (language : NodeLanguage Symbol)
              (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
              Satisfies language meaning assignment afterCache.core →
              Fragments.fill assignment fragment = assignment uv →
              (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
              SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
              (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
                SourcePruningTemplates.ProgramEncoding program) →
              Satisfies language meaning assignment (EnumerationExpandableIndex.frame callbackCore afterCache).core ∧
                recorded.1 = false ∧
                (∀ group ∈ recorded.2.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
                ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                    (fuel + extra) recursiveFuel recorded.2 actual final.query
                    (EnumerationExpandableIndex.frame callbackCore afterCache)
                    (SourcePruningEnumerationRestart.decision stop order recorded.2
                      (EnumerationExpandableIndex.frame callbackCore afterCache)) = outcome
      | _ => True