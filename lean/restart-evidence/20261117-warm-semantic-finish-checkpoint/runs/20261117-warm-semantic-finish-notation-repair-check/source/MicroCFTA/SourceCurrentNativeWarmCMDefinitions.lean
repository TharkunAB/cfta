import MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry

namespace MicroCFTA.SourceCurrentNativeWarmCMDefinitions
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
set_option autoImplicit false

/- Note [Fixed warm history result predicates]
Each mixed qualifier keeps the actual warm start and full history count.
The closed and ordered row scopes match the existing cold predicates.
These definitions add no initial semantic law or source admission.
-/

def Qualified
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) : Prop :=
  ClosedQualified entry.identity request ∨
    SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary request

def NodeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  (ClosedQualified entry.identity request → Profile entry.identity value) ∧
    (SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary request →
      Profile entry.identity value)

def EdgeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  (∀ pair ∈ request.left.children.zip request.right.children,
    Qualified (width := width) rootRequest start wholeCount entry body depth ordinary
      ⟨request.domain, pair.1, pair.2⟩) →
    ∀ child ∈ row.children, Profile entry.identity child

end MicroCFTA.SourceCurrentNativeWarmCMDefinitions

#check MicroCFTA.SourceCurrentNativeWarmCMDefinitions.Qualified
#check MicroCFTA.SourceCurrentNativeWarmCMDefinitions.NodeResult
#check MicroCFTA.SourceCurrentNativeWarmCMDefinitions.EdgeResult
