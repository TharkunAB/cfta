import MicroCFTA.SourceCurrentStoredMuRetainedAlignment

/-!
# Recorded row calls at later heaps

A later reader retains the same construction call and its complete output.
Only the three heap growth receipts change.
-/
namespace MicroCFTA.SourceCurrentStoredMuRetainedAlignment
open Cache InternedConstructorTemplates InternedProbeProvenance
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A later reader retains the same recorded row construction and every endpoint. -/
def RowCall.grows {expressions environment before outputs after reader index symbol guard children}
    (call : RowCall expressions environment before outputs after reader index symbol guard children)
    {later : State Symbol Guard} (growth : Grows reader later) :
    RowCall expressions environment before outputs after later index symbol guard children :=
  { call with
    current_growth := grows_trans call.current_growth growth
    middle_growth := grows_trans call.middle_growth growth
    next_growth := grows_trans call.next_growth growth }

end MicroCFTA.SourceCurrentStoredMuRetainedAlignment
