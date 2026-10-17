import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceCurrentHereditaryNativeScope

/-!
# Conditional finite-cap laws for actual native requests

Each law uses the complete captured request and its source bindings.
The result retains every common bound of the actual ordered operands.
These laws do not assert a producer or query completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeLaws
open InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCap (Cap Edge)
variable {Symbol Guard : Type}

/-- A returned node retains every common cap of its complete original operands. -/
def NodeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop :=
  ∀ depth, Bindings annotation source request.domain.key → Cap annotation depth request.left →
    Cap annotation depth request.right → Cap annotation depth result

/-- A returned row retains every common cap of its complete original rows. -/
def EdgeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  ∀ depth, Bindings annotation source request.domain.key → Edge annotation depth request.left →
    Edge annotation depth request.right → Edge annotation depth result

end MicroCFTA.SourceCurrentConstrainedCapNativeLaws
