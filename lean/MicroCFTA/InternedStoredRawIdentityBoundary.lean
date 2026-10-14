import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Identity substitution can clean up an open raw Mu

The actual closed source root contains an unused raw inner binder.
Stored substitution rebuilds that open inner record with a smart binder.
Replacing the outer reference with itself therefore changes physical node
identity. This refutes an unqualified physical identity-substitution law.
The example does not claim a language change.
-/
namespace MicroCFTA.InternedStoredRawIdentityBoundary
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax)

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-- The raw inner binder retains no local occurrence but captures the outer argument. -/
def expression : Syntax Nat Unit :=
  .binder true (.binder false (.node [.mk 0 () [.var 1]]))

/-- Observe actual closed construction and identity substitution into its open stored body. -/
def observation : Option (Bool × Bool × Nat × Nat × Bool) :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .done root@(.mu entry body _ _) state =>
      match InternedFreshOrdinaryStoredSubstitution.execute body
          (fun name => if name = .interned entry.identity then some (.reference name) else none) state with
      | .done rebuilt _ => some (root.free.isEmpty, body.referenceOf == rebuilt.referenceOf,
          body.depth, rebuilt.depth, body.free == rebuilt.free)
      | .pending .. => none
  | _ => none

set_option cbv.maxSteps 100000000 in
/-- Actual identity substitution changes physical identity and removes one raw binder while retaining free names. -/
theorem observed : observation = some (true, false, 1, 0, true) := by cbv

end MicroCFTA.InternedStoredRawIdentityBoundary
