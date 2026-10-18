import MicroCFTA.SourceCurrentStoredProfileFunction
set_option linter.all true
namespace MicroCFTA.StoredProfileFunctionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile Equivalent)
open SourceEqualityRequiredCache (Ready Keeps)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private theorem unpack (outcome : Outcome Nat Bool (Value Nat Bool)) (success : done outcome = true) :
    outcome = .done (val outcome) outcome.state := by
  cases outcome <;> simp_all [done,val,Outcome.state]
private def source (ordinaryCase : Bool) : Syntax Nat Bool :=
  if ordinaryCase then .binder false (.binder false (.union [.node [.mk 7 false [.var 0]],.var 1]))
  else .binder false (.binder false (.binder false (.union [.var 1,.var 2])))
private def built (ordinaryCase : Bool) := build (source ordinaryCase) [] empty
private def root (ordinaryCase : Bool) := val (built ordinaryCase)
private def reader (ordinaryCase : Bool) := (built ordinaryCase).state
private def target (ordinaryCase : Bool) := match root ordinaryCase with | .mu _ body _ _ => body | _ => .empty
private def outerName (ordinaryCase : Bool) : Reference :=
  match root ordinaryCase with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry (ordinaryCase : Bool) : Interned InternedBinderProtocol.NodeKey :=
  match target ordinaryCase with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ body _ _ => body | _ => .empty
private def depth (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def oldMarker : Reference := .uninterned 101
private def environment (ordinaryCase : Bool) : Environment Nat Bool :=
  fun name => if name = outerName ordinaryCase then some (if ordinaryCase then .empty else .reference oldMarker) else none
private def whole (ordinaryCase : Bool) := execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase)
private theorem built_done (ordinaryCase : Bool) :
    build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) := by
  exact unpack (built ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem ready (ordinaryCase : Bool) : Ready (reader ordinaryCase) :=
  SourceEqualityRequiredCache.constructed (source ordinaryCase) (root ordinaryCase) (reader ordinaryCase) (built_done ordinaryCase)
private theorem target_shape (ordinaryCase : Bool) :
    target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) := by
  cases ordinaryCase <;> cbv
private theorem target_available (ordinaryCase : Bool) : Available (reader ordinaryCase) (target ordinaryCase) := by
  have rootAvailable := (InternedFreshOrdinaryFacts.build_verified (source ordinaryCase) [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result (root ordinaryCase) (reader ordinaryCase) (built_done ordinaryCase)
  have selected : target ordinaryCase ∈ InternedProbeProvenance.children (root ordinaryCase) := by
    cases ordinaryCase <;> cbv <;> exact List.mem_cons_self
  exact rootAvailable.children _ selected
private theorem replacements (ordinaryCase : Bool) : Replacements (reader ordinaryCase) (environment ordinaryCase) := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    cases ordinaryCase with
    | false => exact InternedNestedProvenance.ordinary_available _ 101
    | true => exact empty_available _
  · cases found
private theorem whole_done (ordinaryCase : Bool) :
    execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) = .done (val (whole ordinaryCase)) (whole ordinaryCase).state :=
  unpack (whole ordinaryCase) (by cases ordinaryCase <;> cbv)
private def assignment (ordinaryCase : Bool) : Reference → InternedRootProfile.Profile :=
  fun name => profile (((environment ordinaryCase) name).getD (.reference name))
private def changed (ordinaryCase : Bool) : Reference → InternedRootProfile.Profile :=
  fun name => if name = .interned (entry ordinaryCase).identity then none else assignment ordinaryCase name
private theorem ignored_local (ordinaryCase : Bool) :
    SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (assignment ordinaryCase) =
      SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (changed ordinaryCase) := by
  apply SourceCurrentStoredProfileFunction.congr (target ordinaryCase) (reader ordinaryCase)
    (ready ordinaryCase).semantic.1.normal.facts.coherent (target_available ordinaryCase)
  intro name member
  have different : name ≠ .interned (entry ordinaryCase).identity := by
    rw [target_shape,Value.free,List.mem_filter] at member
    exact of_decide_eq_true member.2
  simp only [changed,different,ite_false]
private theorem actual_profile (ordinaryCase : Bool) :
    Equivalent (profile (val (whole ordinaryCase)))
      (SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (assignment ordinaryCase)) :=
  SourceCurrentStoredProfileFunction.execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase)
    (ready ordinaryCase) (target_available ordinaryCase) (replacements ordinaryCase)
    (val (whole ordinaryCase)) (whole ordinaryCase).state (whole_done ordinaryCase)
private theorem nested_open :
    (target false).free ≠ [] ∧ (∃ entry inner depth ordinary, body false = .mu entry inner depth ordinary) := by
  constructor
  · cbv
  · exact ⟨_,_,_,_,by cbv⟩
private theorem closed_profile (ordinaryCase : Bool) :
    SourceCurrentStoredProfileFunction.denote (root ordinaryCase) (changed ordinaryCase) = profile (root ordinaryCase) :=
  SourceCurrentStoredProfileFunction.closed (root ordinaryCase) (changed ordinaryCase) (by cases ordinaryCase <;> cbv)

/-- Actual open nested Mu execution has its assigned profile and ignores the bound name. -/
theorem actual_nested :
    (∀ ordinaryCase : Bool,
      Ready (reader ordinaryCase) ∧ Available (reader ordinaryCase) (target ordinaryCase) ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) =
        .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      Equivalent (profile (val (whole ordinaryCase)))
        (SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (assignment ordinaryCase)) ∧
      SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (assignment ordinaryCase) =
        SourceCurrentStoredProfileFunction.denote (target ordinaryCase) (changed ordinaryCase) ∧
      SourceCurrentStoredProfileFunction.denote (root ordinaryCase) (changed ordinaryCase) = profile (root ordinaryCase)) ∧
    (target false).free ≠ [] ∧
    (∃ entry inner depth ordinary, body false = .mu entry inner depth ordinary) ∧
    SourceCurrentStoredProfileFunction.denote (target false) (assignment false) = some [oldMarker] ∧
    val (whole false) = .reference oldMarker ∧
    SourceCurrentStoredProfileFunction.denote (target true) (assignment true) = none := by
  refine ⟨fun ordinaryCase => ⟨ready ordinaryCase,target_available ordinaryCase,whole_done ordinaryCase,
    actual_profile ordinaryCase,ignored_local ordinaryCase,closed_profile ordinaryCase⟩,
    nested_open.1,nested_open.2,?_,?_,?_⟩
  all_goals cbv

end MicroCFTA.StoredProfileFunctionKernels
