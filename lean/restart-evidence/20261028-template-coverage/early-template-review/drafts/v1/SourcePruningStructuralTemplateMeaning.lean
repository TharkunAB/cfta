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
  | constant (symbol : Symbol) (annotation : Language.Term Symbol) :
      ProgramEncoding (.node symbol [annotation])
  | app (annotation function argument : Language.Term Symbol) :
      ProgramEncoding function → ProgramEncoding argument →
      ProgramEncoding (.node ("app", FullSyntax.Formula.top)
        [annotation, .node ("(->)", FullSyntax.Formula.top) [], function, argument])

-- This notation names the existing source helper. It adds no evaluator.
local notation "sourceProgram" =>
  _private.MicroCFTA.SourcePruningTemplates.0.MicroCFTA.SourcePruningTemplates.structuralProgram

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
  | anyNode _ | anyPrefix _ | «prefix» _ _ => simp [sourceProgram] at converted
  | node symbol parts =>
      cases parts with
      | nil => simp [sourceProgram] at converted
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | hole =>
                  change some (.node symbol [.hole]) = some early at converted
                  cases Option.some.inj converted
                  exact .inr (.inl ⟨symbol, rfl, rfl⟩)
              | anyNode _ | node _ _ | anyPrefix _ | «prefix» _ _ =>
                  simp [sourceProgram] at converted
          | cons second rest =>
              cases rest with
              | nil => simp [sourceProgram] at converted
              | cons third rest =>
                  cases rest with
                  | nil => simp [sourceProgram] at converted
                  | cons fourth rest =>
                      cases rest with
                      | cons _ _ => simp [sourceProgram] at converted
                      | nil =>
                          cases first with
                          | anyNode _ | node _ _ | anyPrefix _ | «prefix» _ _ =>
                              simp [sourceProgram] at converted
                          | hole =>
                              simp only [sourceProgram] at converted
                              split at converted
                              next same =>
                                subst symbol
                                split at converted
                                next accepted =>
                                  have markerShape : second = .hole ∨
                                      second = .node ("(->)", FullSyntax.Formula.top) [] := by
                                    cases second with
                                    | hole => exact .inl rfl
                                    | node arrow children =>
                                        cases children with
                                        | nil =>
                                            have arrowSame : arrow = ("(->)", FullSyntax.Formula.top) :=
                                              of_decide_eq_true accepted
                                            subst arrow
                                            exact .inr rfl
                                        | cons _ _ => cases accepted
                                    | anyNode _ | anyPrefix _ | «prefix» _ _ => cases accepted
                                  simp only [Option.bind_eq_some_iff, Option.some.injEq] at converted
                                  obtain ⟨nextFunction, functionRun, nextArgument, argumentRun, sameEarly⟩ := converted
                                  cases sameEarly
                                  exact .inr (.inr ⟨second, third, fourth, nextFunction, nextArgument,
                                    rfl, rfl, markerShape, functionRun, argumentRun⟩)
                                next _ => cases converted
                              next _ => cases converted

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
                        apply Template.Matches.node _ _ _ _
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
                          · exact structuralProgram_matches full encoded _ _ converted matched
                          · cases converted

end MicroCFTA.SourcePruningTemplates
