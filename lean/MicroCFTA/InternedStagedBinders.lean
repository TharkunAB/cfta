import MicroCFTA.InternedRecordCoherence

/-!
# Generated binders with previously constructed captures

Programs construct finite dependencies before an ordinary template or Mu.
Capture slots can therefore contain recursively generated Mu records. They
cannot inspect or depend on a fresh enclosing recursive argument.
-/
namespace MicroCFTA.InternedStagedBinders
open InternedBinderProtocol InternedConstructorTemplates InternedRecordCoherence

mutual
/-- Source constructor syntax has one local argument and numbered immutable captures. -/
inductive Skeleton (Symbol Guard : Type) where
  | argument
  | capture (index : Nat)
  | node (edges : List (EdgeSkeleton Symbol Guard))
  | union (members : List (Skeleton Symbol Guard))

/-- Each edge has its original symbol, constraint, and ordered child syntax. -/
inductive EdgeSkeleton (Symbol Guard : Type) where
  | mk (symbol : Symbol) (constraint : Guard) (children : List (Skeleton Symbol Guard))
end

mutual
/-- Replace capture slots with the results of earlier dependency construction. -/
def instantiate (body : Skeleton Symbol Guard) (captures : List (Value Symbol Guard)) : Template Symbol Guard :=
  match body with
  | .argument => .argument
  | .capture index => .captured (captures[index]?.getD .empty)
  | .node edges => .node (instantiateEdges edges captures)
  | .union members => .union (instantiateMany members captures)
termination_by sizeOf body

/-- Preserve source order when inserting captures into child templates. -/
def instantiateMany (bodies : List (Skeleton Symbol Guard)) (captures : List (Value Symbol Guard)) :
    List (Template Symbol Guard) :=
  match bodies with
  | [] => []
  | first :: rest => instantiate first captures :: instantiateMany rest captures
termination_by sizeOf bodies

/-- Capture insertion retains all edge symbols and constraints. -/
def instantiateEdges (edges : List (EdgeSkeleton Symbol Guard)) (captures : List (Value Symbol Guard)) :
    List (EdgeTemplate Symbol Guard) :=
  match edges with
  | [] => []
  | .mk symbol constraint children :: rest =>
      .mk symbol constraint (instantiateMany children captures) :: instantiateEdges rest captures
termination_by sizeOf edges
end

/-- Build dependencies first, then use their results in an ordinary or recursive template. -/
inductive Program (Symbol Guard : Type) where
  | ordinary (dependencies : List (Program Symbol Guard)) (body : Skeleton Symbol Guard)
  | binder (dependencies : List (Program Symbol Guard)) (body : Skeleton Symbol Guard)

mutual
/-- Execute staged source construction through the actual separate cache operations. -/
def build [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) : Value Symbol Guard × InternedConstructorTemplates.State Symbol Guard :=
  match program with
  | .ordinary dependencies body =>
      let earlier := buildMany dependencies state
      run (compile (instantiate body earlier.1) .empty) earlier.2
  | .binder dependencies body =>
      let earlier := buildMany dependencies state
      createMu (instantiate body earlier.1) earlier.2
termination_by sizeOf program

/-- Execute each finite dependency once in source order. -/
def buildMany [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) :
    List (Value Symbol Guard) × InternedConstructorTemplates.State Symbol Guard :=
  match programs with
  | [] => ([], state)
  | first :: rest =>
      let head := build first state
      let tail := buildMany rest head.2
      (head.1 :: tail.1, tail.2)
termination_by sizeOf programs
end

mutual
/-- Generated nested dependencies preserve both supplies and all canonical tables. -/
theorem build_correct [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (build program state).2 ∧ Grows state (build program state).2 := by
  cases program with
  | ordinary dependencies body =>
      simp only [build]
      have earlier := buildMany_correct dependencies state valid
      have final := InternedConstructorTemplates.run_correct
        (compile (instantiate body (buildMany dependencies state).1) .empty) _ earlier.1
      exact ⟨final.1, grows_trans earlier.2 final.2⟩
  | binder dependencies body =>
      simp only [build]
      have earlier := buildMany_correct dependencies state valid
      have final := InternedConstructorTemplates.internMu_correct
        (instantiate body (buildMany dependencies state).1) _ earlier.1
      exact ⟨final.1, grows_trans earlier.2 final.2⟩
termination_by sizeOf program

/-- Dependency-list execution preserves the global cache state invariant. -/
theorem buildMany_correct [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (buildMany programs state).2 ∧ Grows state (buildMany programs state).2 := by
  cases programs with
  | nil => simpa only [buildMany] using And.intro valid (grows_refl state)
  | cons first rest =>
      simp only [buildMany]
      have head := build_correct first state valid
      have tail := buildMany_correct rest (build first state).2 head.1
      exact ⟨tail.1, grows_trans head.2 tail.2⟩
termination_by sizeOf programs
end

mutual
/-- Program syntax derives a concrete constructor trace for the complete nested result. -/
theorem build_constructed [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state) :
    Constructed (build program state).2 := by
  cases program with
  | ordinary dependencies body =>
      simp only [build]
      exact .ordinary (buildMany_constructed dependencies state built) _ _
  | binder dependencies body =>
      simp only [build]
      exact .binder (buildMany_constructed dependencies state built) _
termination_by sizeOf program

/-- Each dependency contributes its actual generated trace. -/
theorem buildMany_constructed [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state) :
    Constructed (buildMany programs state).2 := by
  cases programs with
  | nil => simpa only [buildMany] using built
  | cons first rest =>
      simp only [buildMany]
      exact buildMany_constructed rest _ (build_constructed first state built)
termination_by sizeOf programs
end

mutual
/-- The same nested program reuses every complete result and performs no further cache mutation. -/
theorem build_replay [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (build program before).2 after) : build program after = ((build program before).1, after) := by
  cases program with
  | ordinary dependencies body =>
      simp only [build] at growth ⊢
      let earlier := buildMany dependencies before
      have earlierValid := (buildMany_correct dependencies before valid).1
      have final := InternedConstructorTemplates.run_correct (compile (instantiate body earlier.1) .empty) earlier.2 earlierValid
      have deps := buildMany_replay dependencies before after valid (grows_trans final.2 growth)
      simp only [deps]
      exact compile_replay _ _ earlier.2 after earlierValid growth
  | binder dependencies body =>
      simp only [build] at growth ⊢
      let earlier := buildMany dependencies before
      have earlierValid := (buildMany_correct dependencies before valid).1
      have final := InternedConstructorTemplates.internMu_correct (instantiate body earlier.1) earlier.2 earlierValid
      have deps := buildMany_replay dependencies before after valid (grows_trans final.2 growth)
      simp only [deps]
      exact createMu_replay _ earlier.2 after earlierValid growth
termination_by sizeOf program

/-- Repeated dependency execution retains the same ordered records and final state. -/
theorem buildMany_replay [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (before after : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (buildMany programs before).2 after) :
    buildMany programs after = ((buildMany programs before).1, after) := by
  cases programs with
  | nil => simp only [buildMany]
  | cons first rest =>
      simp only [buildMany] at growth ⊢
      have head := build_correct first before valid
      have tail := buildMany_correct rest (build first before).2 head.1
      have firstReplay := build_replay first before after valid (grows_trans tail.2 growth)
      have restReplay := buildMany_replay rest (build first before).2 after head.1 growth
      simp only [firstReplay, restReplay]
termination_by sizeOf programs
end

/-- Empty-state nested construction derives complete canonical readback for both cache families. -/
theorem empty_build_correct [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard) :
    Coherent (build program empty).2 ∧ Covered [] (build program empty).2 :=
  constructed_correct (build_constructed program empty .empty)

/-- Each whole generated nested program has one stable identity and metadata record after its first execution. -/
theorem empty_build_stable [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (after : InternedConstructorTemplates.State Symbol Guard) (growth : Grows (build program empty).2 after) :
    build program after = ((build program empty).1, after) :=
  build_replay program empty after empty_valid growth

/-- All generated captured dependencies have complete payloads before an enclosing binder reserves its identity. -/
theorem dependencies_complete [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state) :
    Coherent (buildMany programs state).2 ∧ Covered [] (buildMany programs state).2 :=
  constructed_correct (buildMany_constructed programs state built)

/-- Staging leaves no Mu request inside the enclosing binder's generated body computation. -/
theorem body_pending_safe [DecidableEq (EdgeKey Symbol Guard)] (body : Skeleton Symbol Guard)
    (captures : List (Value Symbol Guard)) (argument : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (pending : MuKey NodeRef) :
    (run (compile (instantiate body captures) argument) state).2.nodeRecords (.mu pending) = state.nodeRecords (.mu pending) :=
  compile_preserves_mu (instantiate body captures) argument state pending

/-- The current source body filter also leaves the pending binder slot unchanged. -/
theorem normalized_body_pending_safe [DecidableEq (EdgeKey Symbol Guard)] (body : Skeleton Symbol Guard)
    (captures : List (Value Symbol Guard)) (name : Reference)
    (state : InternedConstructorTemplates.State Symbol Guard) (pending : MuKey NodeRef) :
    (run (compileBody (instantiate body captures) name) state).2.nodeRecords (.mu pending) = state.nodeRecords (.mu pending) :=
  compileBody_preserves_mu (instantiate body captures) name state pending

mutual
/-- The finite request family consists of the program and its recursively generated dependencies. -/
def family (program : Program Symbol Guard) : List (Program Symbol Guard) :=
  program :: match program with
    | .ordinary dependencies _ | .binder dependencies _ => familyMany dependencies
termination_by sizeOf program

/-- Dependency families retain the source evaluation order. -/
def familyMany (programs : List (Program Symbol Guard)) : List (Program Symbol Guard) :=
  match programs with
  | [] => []
  | first :: rest => family first ++ familyMany rest
termination_by sizeOf programs
end

mutual
/-- Retain the actual complete results of the program and each dependency execution. -/
def records [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) : List (Value Symbol Guard) :=
  (build program state).1 :: match program with
    | .ordinary dependencies _ | .binder dependencies _ => recordsMany dependencies state
termination_by sizeOf program

/-- Read each dependency's results at the exact state where the source executes it. -/
def recordsMany [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) : List (Value Symbol Guard) :=
  match programs with
  | [] => []
  | first :: rest => records first state ++ recordsMany rest (build first state).2
termination_by sizeOf programs
end

mutual
/-- Each syntax occurrence contributes exactly one result to the finite trace inventory. -/
theorem records_length [DecidableEq (EdgeKey Symbol Guard)] (program : Program Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) : (records program state).length = (family program).length := by
  cases program with
  | ordinary dependencies body =>
      simp only [records, family, List.length_cons]
      rw [recordsMany_length dependencies state]
  | binder dependencies body =>
      simp only [records, family, List.length_cons]
      rw [recordsMany_length dependencies state]
termination_by sizeOf program

/-- The dependency trace length is the actual finite syntax-family length. -/
theorem recordsMany_length [DecidableEq (EdgeKey Symbol Guard)] (programs : List (Program Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) :
    (recordsMany programs state).length = (familyMany programs).length := by
  cases programs with
  | nil => simp [recordsMany, familyMany]
  | cons first rest =>
      simp only [recordsMany, familyMany, List.length_append]
      rw [records_length first state, recordsMany_length rest (build first state).2]
termination_by sizeOf programs
end

mutual
/-- The root execution already fixes every generated dependency's later complete result. -/
theorem family_replay [DecidableEq (EdgeKey Symbol Guard)] (root requested : Program Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (build root before).2 after) (member : requested ∈ family root) :
    ∃ value ∈ records root before, build requested after = (value, after) := by
  cases root with
  | ordinary dependencies body =>
      simp only [family, List.mem_cons] at member
      rcases member with same | nested
      · subst requested
        exact ⟨_, by simp only [records, List.mem_cons, true_or], build_replay _ _ _ valid growth⟩
      · have earlier := buildMany_correct dependencies before valid
        have final := InternedConstructorTemplates.run_correct
          (compile (instantiate body (buildMany dependencies before).1) .empty) _ earlier.1
        have later : Grows (buildMany dependencies before).2 after :=
          grows_trans final.2 (by simpa only [build] using growth)
        obtain ⟨value, recorded, result⟩ := familyMany_replay dependencies requested before after valid later nested
        exact ⟨value, by simp only [records, List.mem_cons]; exact Or.inr recorded, result⟩
  | binder dependencies body =>
      simp only [family, List.mem_cons] at member
      rcases member with same | nested
      · subst requested
        exact ⟨_, by simp only [records, List.mem_cons, true_or], build_replay _ _ _ valid growth⟩
      · have earlier := buildMany_correct dependencies before valid
        have final := InternedConstructorTemplates.internMu_correct
          (instantiate body (buildMany dependencies before).1) _ earlier.1
        have later : Grows (buildMany dependencies before).2 after :=
          grows_trans final.2 (by simpa only [build, InternedConstructorTemplates.createMu] using growth)
        obtain ⟨value, recorded, result⟩ := familyMany_replay dependencies requested before after valid later nested
        exact ⟨value, by simp only [records, List.mem_cons]; exact Or.inr recorded, result⟩
termination_by sizeOf root

/-- Every dependency-family member reuses its earlier result after the full list completes. -/
theorem familyMany_replay [DecidableEq (EdgeKey Symbol Guard)]
    (programs : List (Program Symbol Guard)) (requested : Program Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (buildMany programs before).2 after) (member : requested ∈ familyMany programs) :
    ∃ value ∈ recordsMany programs before, build requested after = (value, after) := by
  cases programs with
  | nil => simp only [familyMany, List.not_mem_nil] at member
  | cons first rest =>
      simp only [familyMany, List.mem_append] at member
      have head := build_correct first before valid
      have tail := buildMany_correct rest (build first before).2 head.1
      have later : Grows (buildMany rest (build first before).2).2 after := by
        simpa only [buildMany] using growth
      rcases member with firstMember | restMember
      · obtain ⟨value, recorded, result⟩ := family_replay first requested before after valid
          (grows_trans tail.2 later) firstMember
        exact ⟨value, by simp only [recordsMany, List.mem_append]; exact Or.inl recorded, result⟩
      · obtain ⟨value, recorded, result⟩ := familyMany_replay rest requested (build first before).2 after head.1 later restMember
        exact ⟨value, by simp only [recordsMany, List.mem_append]; exact Or.inr recorded, result⟩
termination_by sizeOf programs
end

/-- Syntax alone gives a fixed finite identity image for all staged nested requests after one root execution. -/
theorem finite_identity_image [DecidableEq (EdgeKey Symbol Guard)] (root requested : Program Symbol Guard)
    (after : InternedConstructorTemplates.State Symbol Guard) (growth : Grows (build root empty).2 after)
    (member : requested ∈ family root) :
    (build requested after).1.referenceOf ∈ (records root empty).map Value.referenceOf ∧
      (build requested after).2 = after ∧ (records root empty).length = (family root).length := by
  obtain ⟨value, recorded, repeated⟩ := family_replay root requested empty after empty_valid growth member
  rw [repeated]
  exact ⟨List.mem_map.mpr ⟨value, recorded, rfl⟩, rfl, records_length root empty⟩

/-- An executable nested example constructs an inner recursive node and captures it in an outer recursive node. -/
def twoBinders : Program Nat Unit :=
  .binder [.binder [] (.node [.mk 0 () [.argument]])]
    (.node [.mk 1 () [.argument, .capture 0]])

/-- Kernel evaluation checks the generated nested result and both allocation counters. -/
theorem twoBinders_metadata :
    (build twoBinders empty).1.depth = 2 ∧ (build twoBinders empty).1.free = [] ∧
      (build twoBinders empty).2.edges.next = 6 ∧ (build twoBinders empty).2.nodes.next = 8 := by
  cbv

end MicroCFTA.InternedStagedBinders
