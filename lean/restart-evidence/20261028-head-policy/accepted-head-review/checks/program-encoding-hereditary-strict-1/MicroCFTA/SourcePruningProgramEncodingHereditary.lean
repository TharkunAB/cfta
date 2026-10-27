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
      cases position with
      | application => exact .app annotation function argument functionEncoded argumentEncoded
      | function _ _ _ _ _ nested => exact functionIH _ nested
      | argument _ _ _ _ _ nested => exact argumentIH _ nested

end MicroCFTA.SourcePruningTemplates
