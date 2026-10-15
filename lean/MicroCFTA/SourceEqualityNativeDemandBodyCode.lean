import MicroCFTA.SourceEqualityNativeDemandContinuation
import MicroCFTA.SourceRecursiveIntersectionBodyCode

/-!
# Checked source bodies contain no explicit completion frame

Only the native driver adds node and edge finish instructions. Actual edge
prefixes emit source sentinel or child code without such frames. This fact
supports running-cell retention through actual completed source bodies.
-/
namespace MicroCFTA.SourceEqualityNativeDemandBodyCode
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A source control has no explicit driver completion frame in its continuation. -/
def Clean : Control Output → Prop
  | .code body => BodyCode body
  | .edgeBody _ next => ∀ value, BodyCode (next value)

/-- The source sentinel contains only its physical constructor instruction. -/
theorem sentinel_bodyCode (left : EdgeValue Symbol Guard) :
    BodyCode (SourceEqualityNativeCheckedCode.sentinel left) := by intro value; trivial

/-- Accepted child code contains only source requests and its final constructor instruction. -/
theorem children_bodyCode (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    BodyCode (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  apply bodyCode_bind
  · exact bodyCode_walk _ _ (fun _ _ => by intro value; trivial)
  · intro values value
    trivial

/-- Every actual yielded checked prefix preserves a clean source continuation. -/
theorem body_clean (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state after : State width) (rest : Control Output)
    (one : body request next state = .yielded rest after) (clean : ∀ value, BodyCode (next value)) : Clean rest := by
  unfold body at one
  split at one
  · cases one
    exact bodyCode_bind _ _ (sentinel_bodyCode _) clean
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          exact bodyCode_bind _ _ (sentinel_bodyCode _) clean
        · cases one
          exact bodyCode_bind _ _ (sentinel_bodyCode _) clean
        · cases one
          exact bodyCode_bind _ _ (children_bodyCode _ _) clean

end MicroCFTA.SourceEqualityNativeDemandBodyCode
