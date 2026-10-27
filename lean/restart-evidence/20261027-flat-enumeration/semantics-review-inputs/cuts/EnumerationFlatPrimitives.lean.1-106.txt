import MicroCFTA.EnumerationFlatState
import MicroCFTA.EnumerationCPSUnionFind

/-!
# Exact core results across the union-find representation change

Earlier lookup bounds remain explicit. Every related input supplies a stable
sufficient bound. Invalid raw slots stay errors rather than rejected branches.
-/

namespace MicroCFTA.EnumerationFlatState

open EnumerationResultRelation (Results)

variable {Symbol Guard : Type} {flat : State Symbol Guard}
  {earlier : EnumerationState.State Symbol Guard}

/-- A completed earlier lookup returns the same value and a related complete core state. -/
theorem representative_related (related : Related flat earlier)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    Results Related (representative uv flat) (EnumerationState.representative fuel uv earlier) := by
  rw [EnumerationCorrectness.representative_exact fuel uv earlier found completed]
  obtain ⟨sameRoot, _, retained⟩ := FlatUnionFind.findRoot_represents related.representatives completed
  change Results Related [.ok (FlatUnionFind.root flat.representatives uv, flat)]
    [.ok (found.representative, {earlier with representatives := found.forest})]
  rw [sameRoot]
  exact .cons (.ok _ (related_forests related related.valid retained)) .nil

/-- One sufficient representative bound and all its extensions preserve every result. -/
theorem representative_stable (related : Related flat earlier) (uv : Nat) :
    ∃ fuel, ∀ extra, Results Related (representative uv flat)
      (EnumerationState.representative (fuel + extra) uv earlier) := by
  obtain ⟨fuel, found, stable, _, _, _⟩ := FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra => representative_related related (stable extra)⟩

/-- A completed earlier union returns unit and retains every non-forest core field. -/
theorem unionVariables_related (related : Related flat earlier)
    (completed : UnionFind.union fuel fuel earlier.representatives left right = some output) :
    Results Related (unionVariables left right flat)
      (EnumerationState.unionVariables fuel left right earlier) := by
  rw [EnumerationCorrectness.union_exact fuel left right earlier output completed]
  exact .cons (.ok () (related_forests related
    (FlatUnionFind.union_valid related.valid left right)
    (FlatUnionFind.union_represents related.valid related.representatives completed))) .nil

/-- The actual one-bound earlier union agrees at every sufficient larger bound. -/
theorem unionVariables_stable (related : Related flat earlier) (left right : Nat) :
    ∃ fuel, ∀ extra, Results Related (unionVariables left right flat)
      (EnumerationState.unionVariables (fuel + extra) left right earlier) := by
  obtain ⟨fuel, output, stable, _, _⟩ :=
    FlatUnionFind.union_stable related.valid related.representatives left right
  exact ⟨fuel, fun extra => unionVariables_related related (stable extra)⟩

/-- Raw-slot reads preserve both successful values and invalid-slot errors. -/
theorem rawValue_related (related : Related flat earlier) (uv : Nat) :
    Results Related (rawValue uv flat) (EnumerationState.rawValue uv earlier) := by
  cases stored : flat.values[uv]? with
  | none =>
    have oldStored : earlier.values[uv]? = none := by rw [← related.values]; exact stored
    have oldRead : EnumerationState.rawValue uv earlier = [.error .invalidSlot] := by
      simp [EnumerationState.rawValue, oldStored, EnumerationState.failure, Bind.bind,
        Pure.pure, get, getThe, MonadStateOf.get, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk]
    rw [oldRead]
    simp only [rawValue, stored]
    exact .cons (.error EnumerationState.Error.invalidSlot) .nil
  | some value =>
    have oldStored : earlier.values[uv]? = some value := by rw [← related.values]; exact stored
    have oldRead : EnumerationState.rawValue uv earlier = [.ok (value, earlier)] := by
      simp [EnumerationState.rawValue, oldStored, Bind.bind, Pure.pure,
        get, getThe, MonadStateOf.get, StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk]
    rw [oldRead]
    simp only [rawValue, stored]
    exact .cons (.ok value related) .nil

/-- A raw-slot write retains the exact value array in both representations. -/
theorem setValue_related (related : Related flat earlier) (uv : Nat)
    (value : EnumerationState.UVarValue Symbol) :
    Results Related (setValue uv value flat) (EnumerationState.setValue uv value earlier) := by
  change Results Related
    [.ok ((), {flat with values := flat.values.set uv value})]
    [.ok ((), {earlier with values := earlier.values.set uv value})]
  exact .cons (.ok () ⟨related.valid, related.representatives, related.counter,
    congrArg (fun values => values.set uv value) related.values, related.obligations,
    related.recursionAncestry, related.expansionAncestry⟩) .nil

/-- The earlier conditional-compression CPS representative has the same related rows. -/
theorem representative_cps_related (related : Related flat earlier)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    Results Related
      (EnumerationCPSChecked.allResults (EnumerationCPSChecked.encode (representative uv)) flat)
      (EnumerationCPSChecked.allResults (EnumerationCPSUnionFind.representative fuel uv) earlier) := by
  rw [EnumerationCPSChecked.allResults_encode, EnumerationCPSUnionFind.representative_results]
  exact representative_related related completed

/-- The earlier conditional-compression CPS union has the same related rows. -/
theorem unionVariables_cps_related (related : Related flat earlier)
    (completed : UnionFind.union fuel fuel earlier.representatives left right = some output) :
    Results Related
      (EnumerationCPSChecked.allResults (EnumerationCPSChecked.encode (unionVariables left right)) flat)
      (EnumerationCPSChecked.allResults (EnumerationCPSUnionFind.unionVariables fuel left right) earlier) := by
  rw [EnumerationCPSChecked.allResults_encode, EnumerationCPSUnionFind.unionVariables_results]
  exact unionVariables_related related completed

end MicroCFTA.EnumerationFlatState
