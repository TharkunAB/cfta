import MicroCFTA.SourceEqualityPartialSource

/-!
# Actual reached word-check plans for bounded recursive reduction

Plans follow successful source prefixes and actual returned warm states.
They contain no language law or completed recursive graph. A child plan
uses the actual descended payload. A row supplies its child plan only after
its local native prefix and physical payload combination complete.
-/
namespace MicroCFTA.SourceEqualityPartialChecks
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An indexed plan advances the tail only after the actual earlier child call completes. -/
def Walk (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop)
    (payload : SourceEqualityPrecheck.Constraint) : Nat → List (Value Symbol Guard) → NativeState width Symbol Guard → Prop
  | _, [], _ => True
  | index, value :: values, before =>
      check (SourceEqualityDescend.descend payload index) value before ∧
        ∀ result middle, call (SourceEqualityDescend.descend payload index) value before = .done (.ok result) middle →
          Walk call check payload (index + 1) values middle

/-- Actual contradiction skips recursive checks; live payloads start at child index zero. -/
def Children (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop)
    (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Prop :=
  match payload with
  | none => True
  | some records => Walk call check (some records) 0 values before

/-- Each row plan retains actual native checks, completed local payload calls, and successful returned tail scopes. -/
def Rows (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) : List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop
  | [], _ => True
  | edge :: edges, before =>
      SourceEqualityPCSNativeEdge.Ranges edge inherited before ∧
      (∀ narrowed middle, SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before = .done (.ok narrowed) middle →
        ∀ own, SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint = .ok own →
        ∀ payload, SourceEqualityInheritedPayload.combine inherited own = .ok payload →
          Children call check payload narrowed.children middle) ∧
      ∀ result middle, SourceEqualityInheritedEdgeWorker.run call g e p h c n edge inherited before = .done (.ok result) middle →
        Rows call check g e p h c n inherited edges middle

/-- A traversal plan decreases only at actual recursive node entries and checks every reached native row prefix. -/
def Checked (g e p h c n : Nat) : Nat → SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop
  | 0, _, _, _ => True
  | fuel + 1, inherited, value, before =>
      match value with
      | .node _ edges _ _ => Rows (SourceEqualityPartialWorker.run g e p h c n fuel) (Checked g e p h c n fuel) g e p h c n inherited edges before
      | _ => True

/-- The reached recursive plan supplies the existing local row range interface at exactly the actual returned states. -/
theorem rows_ranges {width : Nat}
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width}
    {check g e p h c n inherited edges before}
    (plan : Rows call check g e p h c n inherited edges before) :
    SourceEqualityInheritedRows.Ranges call g e p h c n inherited edges before := by
  induction edges generalizing before with
  | nil => trivial
  | cons edge edges ih => exact ⟨plan.1, fun result middle actual => ih (plan.2.2 result middle actual)⟩

end MicroCFTA.SourceEqualityPartialChecks
