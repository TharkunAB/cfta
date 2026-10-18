import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentNativeMuIssuedHistory

/-!
# Actual cache-growth paths through stored reconstruction

Stored execution is an actual source call on encoded inputs. Its initial
ready data supplies the source Context and the complete publication path.
The path retains cache growth and issued names that History drops.
No observation relation or selected writer is assumed.
-/
namespace MicroCFTA.SourceCurrentStoredReconstructionPath
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuIssuedHistory (Path)

/-- Actual self filtering adds no Mu and retains all cache tables and issued names. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (value : Value Symbol Guard) (before : State Symbol Guard) (valid : Valid before) :
    Nonempty (Path before (run (withoutSelfReference own value) before).2) :=
  ⟨.retain before _ (InternedStoredMuOrigins.filter_noNewMu own value before)
    (run_correct (withoutSelfReference own value) before valid).2
    (InternedConstructionProvenance.run_issued_extends (withoutSelfReference own value) before valid)⟩

/-- Every actual completed stored call derives its complete cache-growth publication path. -/
theorem actual [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (called : execute value environment before = .done result after) :
    Nonempty (Path before after) := by
  have context : Context before ((leaves value).map (input environment)) :=
    ⟨⟨ready.semantic.1.normal,inputs_available value environment before available replacements,
      ready.semantic.1.profiles,ready.semantic.1.freeNames⟩,ready.semantic.2⟩
  have path := SourceCurrentNativeMuIssuedHistory.build_path (encode (leaves value) [] value)
    _ before context
  change Nonempty (Path before (execute value environment before).state) at path
  simpa only [called,Outcome.state] using path

/-- Initial ready data constructs the exact stored call and retains its full cache-growth path. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (replacements : Replacements before environment) :
    ∃ result after, execute value environment before = .done result after ∧
      Keeps before after ∧ Available after result ∧ Nonempty (Path before after) := by
  obtain ⟨result,after,called,kept,output,_history⟩ :=
    SourceCurrentStoredReconstruction.execute value environment before ready available replacements
  exact ⟨result,after,called,kept,output,actual value environment before ready available replacements result after called⟩

end MicroCFTA.SourceCurrentStoredReconstructionPath
