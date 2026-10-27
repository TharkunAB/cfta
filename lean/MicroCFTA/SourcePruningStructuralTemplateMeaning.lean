import MicroCFTA.SourcePruningTemplates

/-!
# Original template meaning for encoded complete programs

Specftacular.Utils.mapp inserts the fixed singleton arrow marker.
Specftacular.Rewriting.rawTemplate uses that marker in application patterns.
The public signature guard excludes type constructors with the app/4 shape.
The predicate below records the complete program syntax at program positions.
It does not assert that an arbitrary native packet has this syntax.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language Template
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- Complete programs use annotated constants and the source application marker. -/
inductive ProgramEncoding : Language.Term Symbol → Prop where
  /-- A constant has one annotation child. -/
  | constant (symbol : Symbol) (annotation : Language.Term Symbol) :
      ProgramEncoding (.node symbol [annotation])
  /-- An application has the fixed arrow marker and two complete program children. -/
  | app (annotation function argument : Language.Term Symbol) :
      ProgramEncoding function → ProgramEncoding argument →
      ProgramEncoding (.node ("app", FullSyntax.Formula.top)
        [annotation, .node ("(->)", FullSyntax.Formula.top) [], function, argument])

-- This macro names the actual private helper in the imported source module.
local macro "sourceProgram" : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.MicroCFTA.SourcePruningTemplates 0) ++
    `MicroCFTA.SourcePruningTemplates.structuralProgram))

-- The tactic macro gives simp an identifier, not a function-valued term.
local macro "simp_source_program" " at " hypothesis:ident : tactic => do
  let helper := Lean.mkIdent ((Lean.Name.num `_private.MicroCFTA.SourcePruningTemplates 0) ++
    `MicroCFTA.SourcePruningTemplates.structuralProgram)
  `(tactic| simp [$helper:ident] at $hypothesis:ident)

local macro "unfold_source_program" " at " hypothesis:ident : tactic => do
  let helper := Lean.mkIdent ((Lean.Name.num `_private.MicroCFTA.SourcePruningTemplates 0) ++
    `MicroCFTA.SourcePruningTemplates.structuralProgram)
  `(tactic| simp only [$helper:ident] at $hypothesis:ident)

private theorem node_matches_inv (expected actual : Symbol)
    (patterns : List (Template.Pattern Symbol)) (terms : List (Language.Term Symbol))
    (matched : Template.Matches (.node expected patterns) (.node actual terms)) :
    expected = actual ∧ Language.All₂ Template.Matches patterns terms := by
  cases matched with
  | node _ _ _ found aligned children =>
      simp only [Template.childTemplates] at aligned
      split at aligned
      next same =>
        unfold Template.exactChildren at aligned
        split at aligned
        next _ =>
          have partsSame : patterns = found := Option.some.inj aligned
          exact ⟨same, partsSame.symm ▸ children⟩
        next _ => cases aligned
      next _ => cases aligned

private theorem converted_children (function argument early : Template.Pattern Symbol)
    (converted : (do
      let nextFunction ← sourceProgram function
      let nextArgument ← sourceProgram argument
      pure (.node ("app", FullSyntax.Formula.top) [.hole, .hole, nextFunction, nextArgument])) = some early) :
    ∃ nextFunction nextArgument,
      early = .node ("app", FullSyntax.Formula.top) [.hole, .hole, nextFunction, nextArgument] ∧
      sourceProgram function = some nextFunction ∧ sourceProgram argument = some nextArgument := by
  change Option.bind (sourceProgram function) (fun nextFunction =>
    Option.bind (sourceProgram argument) (fun nextArgument =>
      some (.node ("app", FullSyntax.Formula.top) [.hole, .hole, nextFunction, nextArgument]))) =
        some early at converted
  obtain ⟨nextFunction, functionRun, argumentStep⟩ := Option.bind_eq_some_iff.mp converted
  obtain ⟨nextArgument, argumentRun, sameEarly⟩ := Option.bind_eq_some_iff.mp argumentStep
  exact ⟨nextFunction, nextArgument, (Option.some.inj sameEarly).symm, functionRun, argumentRun⟩

private theorem conversion_shape (original early : Template.Pattern Symbol)
    (converted : sourceProgram original = some early) :
    (original = .hole ∧ early = .hole) ∨
    (∃ symbol, original = .node symbol [.hole] ∧ early = .node symbol [.hole]) ∨
    ∃ marker function argument nextFunction nextArgument,
      original = .node ("app", FullSyntax.Formula.top) [.hole, marker, function, argument] ∧
      early = .node ("app", FullSyntax.Formula.top) [.hole, .hole, nextFunction, nextArgument] ∧
      (marker = .hole ∨ marker = .node ("(->)", FullSyntax.Formula.top) []) ∧
      sourceProgram function = some nextFunction ∧ sourceProgram argument = some nextArgument := by
  cases original with
  | hole =>
      cases Option.some.inj converted
      exact .inl ⟨rfl, rfl⟩
  | anyNode _ | anyPrefix _ | «prefix» _ _ => simp_source_program at converted
  | node symbol parts =>
      cases parts with
      | nil => simp_source_program at converted
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | hole =>
                  change some (.node symbol [.hole]) = some early at converted
                  cases Option.some.inj converted
                  exact .inr (.inl ⟨symbol, rfl, rfl⟩)
              | anyNode _ | node _ _ | anyPrefix _ | «prefix» _ _ =>
                  simp_source_program at converted
          | cons second rest =>
              cases rest with
              | nil => simp_source_program at converted
              | cons third rest =>
                  cases rest with
                  | nil => simp_source_program at converted
                  | cons fourth rest =>
                      cases rest with
                      | cons _ _ => simp_source_program at converted
                      | nil =>
                          cases first with
                          | anyNode _ | node _ _ | anyPrefix _ | «prefix» _ _ =>
                              simp_source_program at converted
                          | hole =>
                              by_cases same : symbol = ("app", FullSyntax.Formula.top)
                              · unfold_source_program at converted
                                rw [ite_eq_left same] at converted
                                subst symbol
                                cases second with
                                | hole =>
                                    change (do
                                      let nextFunction ← sourceProgram third
                                      let nextArgument ← sourceProgram fourth
                                      pure (.node ("app", FullSyntax.Formula.top)
                                        [.hole, .hole, nextFunction, nextArgument])) = some early at converted
                                    obtain ⟨nextFunction, nextArgument, rfl, functionRun, argumentRun⟩ :=
                                      converted_children third fourth early converted
                                    exact .inr (.inr ⟨.hole, third, fourth, nextFunction, nextArgument,
                                      rfl, rfl, .inl rfl, functionRun, argumentRun⟩)
                                | node arrow children =>
                                    cases children with
                                    | cons _ _ =>
                                        change none = some early at converted
                                        cases converted
                                    | nil =>
                                        by_cases arrowSame : arrow = ("(->)", FullSyntax.Formula.top)
                                        · subst arrow
                                          have arrowAccepted : decide ((("(->)", FullSyntax.Formula.top) : Symbol) =
                                              ("(->)", FullSyntax.Formula.top)) = true := decide_eq_true_iff.mpr rfl
                                          change (if decide ((("(->)", FullSyntax.Formula.top) : Symbol) =
                                              ("(->)", FullSyntax.Formula.top)) = true then do
                                            let nextFunction ← sourceProgram third
                                            let nextArgument ← sourceProgram fourth
                                            pure (.node ("app", FullSyntax.Formula.top)
                                              [.hole, .hole, nextFunction, nextArgument])
                                            else none) = some early at converted
                                          rw [ite_eq_left arrowAccepted] at converted
                                          obtain ⟨nextFunction, nextArgument, rfl, functionRun, argumentRun⟩ :=
                                            converted_children third fourth early converted
                                          exact .inr (.inr ⟨.node ("(->)", FullSyntax.Formula.top) [],
                                            third, fourth, nextFunction, nextArgument,
                                            rfl, rfl, .inr rfl, functionRun, argumentRun⟩)
                                        · have notAccepted : ¬decide (arrow = ("(->)", FullSyntax.Formula.top)) = true :=
                                            fun accepted => arrowSame (of_decide_eq_true accepted)
                                          change (if decide (arrow = ("(->)", FullSyntax.Formula.top)) = true then do
                                            let nextFunction ← sourceProgram third
                                            let nextArgument ← sourceProgram fourth
                                            pure (.node ("app", FullSyntax.Formula.top)
                                              [.hole, .hole, nextFunction, nextArgument])
                                            else none) = some early at converted
                                          rw [ite_eq_right notAccepted] at converted
                                          cases converted
                                | anyNode _ | anyPrefix _ | «prefix» _ _ =>
                                    change none = some early at converted
                                    cases converted
                              · unfold_source_program at converted
                                rw [ite_eq_right same] at converted
                                cases converted

private theorem structuralProgram_matches (full : Language.Term Symbol) (encoded : ProgramEncoding full) :
    ∀ original early, sourceProgram original = some early →
      Template.Matches early full → Template.Matches original full := by
  induction encoded with
  | constant symbol annotation =>
      intro original early converted matched
      rcases conversion_shape original early converted with ⟨rfl, rfl⟩ |
        ⟨wanted, rfl, rfl⟩ | ⟨marker, function, argument, nextFunction, nextArgument,
          rfl, rfl, _markerShape, _functionRun, _argumentRun⟩
      · exact matched
      · exact matched
      · have children := (node_matches_inv _ _ _ _ matched).2
        have impossible : (4 : Nat) = 1 := children.length_eq
        omega
  | app annotation function argument _functionEncoded _argumentEncoded functionIH argumentIH =>
      intro original early converted matched
      rcases conversion_shape original early converted with ⟨rfl, rfl⟩ |
        ⟨wanted, rfl, rfl⟩ | ⟨marker, originalFunction, originalArgument, nextFunction, nextArgument,
          rfl, rfl, markerShape, functionRun, argumentRun⟩
      · exact matched
      · exact matched
      · have children := (node_matches_inv _ _ _ _ matched).2
        cases children with
        | cons _ children =>
            cases children with
            | cons _ children =>
                cases children with
                | cons functionMatches children =>
                    cases children with
                    | cons argumentMatches _ =>
                        have markerMatches : Template.Matches marker
                            (.node ("(->)", FullSyntax.Formula.top) []) := by
                          rcases markerShape with rfl | rfl
                          · exact Template.hole_matches _
                          · exact .node _ _ _ [] (by simp [Template.childTemplates,
                              Template.exactChildren]) .nil
                        apply Template.Matches.node _ _ _ [.hole, marker, originalFunction, originalArgument]
                          (by simp [Template.childTemplates, Template.exactChildren])
                        exact .cons (Template.hole_matches annotation)
                          (.cons markerMatches
                            (.cons (functionIH _ _ functionRun functionMatches)
                              (.cons (argumentIH _ _ argumentRun argumentMatches) .nil)))

/-- A converted structural match is an original forbidden match on a source-encoded complete program. -/
theorem structuralTemplate_matches (original early : Template.Pattern Symbol) (full : Language.Term Symbol)
    (converted : structuralTemplate original = some early)
    (encoded : ProgramEncoding full) (matched : Template.Matches early full) :
    Template.Matches original full := by
  cases original with
  | hole | anyNode _ | anyPrefix _ | «prefix» _ _ => simp [structuralTemplate] at converted
  | node symbol parts =>
      cases parts with
      | nil => simp [structuralTemplate] at converted
      | cons first rest =>
          cases rest with
          | nil => simp [structuralTemplate] at converted
          | cons second rest =>
              cases rest with
              | nil => simp [structuralTemplate] at converted
              | cons third rest =>
                  cases rest with
                  | nil => simp [structuralTemplate] at converted
                  | cons fourth rest =>
                      cases rest with
                      | cons _ _ => simp [structuralTemplate] at converted
                      | nil =>
                          simp only [structuralTemplate] at converted
                          split at converted
                          · change sourceProgram (.node symbol [first, second, third, fourth]) =
                              some early at converted
                            exact structuralProgram_matches full encoded _ _ converted matched
                          · cases converted

end MicroCFTA.SourcePruningTemplates
