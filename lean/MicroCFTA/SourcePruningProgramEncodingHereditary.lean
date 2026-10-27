import MicroCFTA.SourcePruningStructuralTemplateMeaning
import MicroCFTA.SourcePruningProgramSemantics

/-!
# Source encoding at inspected program positions

An original complete program supplies the encoding of each inspected program.
This law does not derive the root encoding from native acceptance.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language

/-- Every program position of an encoded original program has the source encoding. -/
theorem ProgramEncoding.at_program {whole program : Term Symbol}
    (encoded : ProgramEncoding whole) (position : ProgramAt whole program) :
    ProgramEncoding program := by
  induction encoded generalizing program with
  | constant symbol annotation => cases position
  | app annotation function argument functionEncoded argumentEncoded functionIH argumentIH =>
      have parentEncoded : ProgramEncoding (.node ("app", FullSyntax.Formula.top)
          [annotation, .node ("(->)", FullSyntax.Formula.top) [], function, argument]) :=
        .app annotation function argument functionEncoded argumentEncoded
      generalize same : Term.node ("app", FullSyntax.Formula.top)
        [annotation, .node ("(->)", FullSyntax.Formula.top) [], function, argument] = observedWhole at position
      cases position with
      | application => exact same ▸ parentEncoded
      | function _ _ otherFunction _ _ nested =>
          have childrenSame := (Term.node.inj same).2
          have tailSame := (List.cons.inj (List.cons.inj childrenSame).2).2
          have functionSame : function = otherFunction := (List.cons.inj tailSame).1
          exact functionIH (functionSame.symm ▸ nested)
      | argument _ _ _ otherArgument _ nested =>
          have childrenSame := (Term.node.inj same).2
          have tailSame := (List.cons.inj (List.cons.inj childrenSame).2).2
          have argumentSame : argument = otherArgument :=
            (List.cons.inj (List.cons.inj tailSame).2).1
          exact argumentIH (argumentSame.symm ▸ nested)
      | filter =>
          have impossible : (4 : Nat) = 2 := congrArg List.length (Term.node.inj same).2
          omega

end MicroCFTA.SourcePruningTemplates
