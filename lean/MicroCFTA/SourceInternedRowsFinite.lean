import MicroCFTA.SourceInternedRows
import MicroCFTA.Cache

/-!
# Completion of the interned row walk

A finite closed exposure domain gives a finite traversal, including cycles
and repeated pending references. A completed map stores the exact first
exposed row at each identity. Native exposure must itself complete and keep
the immutable snapshot contract.
-/
namespace MicroCFTA.SourceInternedRows

/-- Every exposed nonempty dependency stays inside the finite heap domain. -/
def ClosedDomain (heap : Heap Symbol Constraint) (domain : List Nat) : Prop :=
  ∀ identity ∈ domain, ∀ child ∈ successors heap identity, child ∈ domain

/-- Empty references need no identity-domain entry. -/
def PendingDomain (domain : List Nat) (pending : List Ref) : Prop :=
  ∀ identity, some identity ∈ pending → identity ∈ domain

/-- A finite closed heap admits a completed source worklist execution. -/
theorem collect_finite (heap : Heap Symbol Constraint) (domain : List Nat)
    (closed : ClosedDomain heap domain) (seen : List Nat) (pending : List Ref)
    (supported : PendingDomain domain pending) :
    ∃ fuel result, collect heap fuel seen pending = some result := by
  have all : ∀ budget, ∀ available : List Nat, available.length = budget →
      ∀ seen pending, (∀ identity ∈ domain, identity ∉ seen → identity ∈ available) →
      PendingDomain domain pending → ∃ fuel result, collect heap fuel seen pending = some result := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
      intro available lengthEq seen pending fresh supported
      induction pending with
      | nil => exact ⟨1, seen, rfl⟩
      | cons node rest tail =>
        have restSupported : PendingDomain domain rest := fun identity member => supported identity (by simp [member])
        cases node with
        | none =>
          obtain ⟨fuel, result, done⟩ := tail restSupported
          exact ⟨fuel + 1, result, done⟩
        | some identity =>
          by_cases known : identity ∈ seen
          · obtain ⟨fuel, result, done⟩ := tail restSupported
            exact ⟨fuel + 1, result, by simpa [collect, known] using done⟩
          · have present := supported identity (by simp)
            have remaining := fresh identity present known
            have shorter : (available.erase identity).length < budget := by
              have removed := List.length_erase_of_mem remaining
              have positive := List.length_pos_of_mem remaining
              omega
            have nextFresh : ∀ next ∈ domain, next ∉ identity :: seen → next ∈ available.erase identity := by
              intro next member absent
              have different : next ≠ identity := by intro same; exact absent (by simp [same])
              exact (List.mem_erase_of_ne different).mpr (fresh next member (fun old => absent (by simp [old])))
            have nextSupported : PendingDomain domain (children heap identity ++ rest) := by
              intro next member
              rcases List.mem_append.mp member with child | later
              · exact closed identity present next ((mem_successors heap identity next).mpr child)
              · exact restSupported next later
            obtain ⟨fuel, result, done⟩ := ih _ shorter (available.erase identity) rfl
              (identity :: seen) (children heap identity ++ rest) nextFresh nextSupported
            exact ⟨fuel + 1, result, by simpa [collect, known] using done⟩
  exact all domain.length domain rfl seen pending (by intro identity member _; exact member) supported

/-- More fuel cannot change a completed source traversal or its discovery order. -/
theorem collect_stable (heap : Heap Symbol Constraint) (fuel : Nat) (seen : List Nat)
    (pending : List Ref) (result : List Nat) (done : collect heap fuel seen pending = some result)
    (larger : Nat) (enough : fuel ≤ larger) : collect heap larger seen pending = some result := by
  induction fuel generalizing larger seen pending with
  | zero => cases done
  | succ fuel ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      have enough : fuel ≤ larger := by omega
      cases pending with
      | nil => exact done
      | cons node rest =>
        cases node with
        | none => exact ih seen rest done larger enough
        | some identity =>
          by_cases known : identity ∈ seen
          · simpa [collect, known] using ih seen rest (by simpa [collect, known] using done) larger enough
          · simpa [collect, known] using ih (identity :: seen) (children heap identity ++ rest)
              (by simpa [collect, known] using done) larger enough

/-- The functional map stores each visited identity's exact snapshot row. -/
def stored (heap : Heap Symbol Constraint) (seen : List Nat) : Cache.Table Nat (List (Row Symbol Constraint)) :=
  fun identity => if identity ∈ seen then some (heap identity) else none

/-- Insertion stores the exposed row and leaves every other source map entry unchanged. -/
theorem stored_insert (heap : Heap Symbol Constraint) (seen : List Nat) (identity : Nat) :
    Cache.put (stored heap seen) identity (heap identity) = stored heap (identity :: seen) := by
  funext next
  by_cases same : next = identity <;> simp [Cache.put, stored, same]

/-- The actual map-valued worklist, including first-hit row retention. -/
def collectMap (heap : Heap Symbol Constraint) : Nat → Cache.Table Nat (List (Row Symbol Constraint)) →
    List Ref → Option (Cache.Table Nat (List (Row Symbol Constraint)))
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, none :: pending => collectMap heap fuel seen pending
  | fuel + 1, seen, some identity :: pending =>
      match seen identity with
      | some _ => collectMap heap fuel seen pending
      | none => collectMap heap fuel (Cache.put seen identity (heap identity)) (children heap identity ++ pending)

/-- The visited-key proof computes the exact source map, not just a reachability superset. -/
theorem collectMap_exact (heap : Heap Symbol Constraint) (fuel : Nat) (seen : List Nat) (pending : List Ref) :
    collectMap heap fuel (stored heap seen) pending = (collect heap fuel seen pending).map (stored heap) := by
  induction fuel generalizing seen pending with
  | zero => rfl
  | succ fuel ih =>
    cases pending with
    | nil => rfl
    | cons node rest =>
      cases node with
      | none => exact ih seen rest
      | some identity =>
        by_cases known : identity ∈ seen
        · simp [collectMap, collect, stored, known, ih]
        · have missing : stored heap seen identity = none := by simp [stored, known]
          simp only [collectMap, missing, collect, known, ↓reduceIte, stored_insert]
          exact ih (identity :: seen) (children heap identity ++ rest)

/-- A supported root has a stable completed row table after a finite traversal. -/
theorem toRows_finite (heap : Heap Symbol Constraint) (domain : List Nat) (closed : ClosedDomain heap domain)
    (root : Ref) (supported : ∀ identity, root = some identity → identity ∈ domain) :
    ∃ fuel table, ∀ larger, fuel ≤ larger → toRows heap larger root = some table := by
  cases root with
  | none => exact ⟨0, [(.empty, [])], fun _ _ => rfl⟩
  | some identity =>
    obtain ⟨fuel, visited, done⟩ := collect_finite heap domain closed [] [some identity]
      (by
        intro next member
        have same : next = identity := by simpa using member
        subst next
        exact supported identity rfl)
    exact ⟨fuel, table heap visited, fun larger enough => by
      simp [toRows, collect_stable heap fuel [] [some identity] visited done larger enough]⟩

end MicroCFTA.SourceInternedRows
