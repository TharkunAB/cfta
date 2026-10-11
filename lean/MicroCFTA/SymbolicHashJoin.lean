import MicroCFTA.SymbolicProductRows

/-!
# Constructor-key hash join

The source groups the right rows by the complete constructor key. Each new
row is prepended to its key's bucket. Hash values choose storage locations;
key equality chooses the bucket. The proofs retain duplicate occurrences and
derive every matching pair. Runtime hash-table collision handling is the
typed map representation boundary.
-/
namespace MicroCFTA.SymbolicHashJoin

/-- Prepend one row to the bucket selected by its complete key. -/
def insert [DecidableEq Key] (key : Row → Key) (buckets : Key → List Row) (row : Row) : Key → List Row :=
  fun sought => if sought = key row then row :: buckets sought else buckets sought

/-- The source `fromListWith (++)` worker for singleton row values. -/
def build [DecidableEq Key] (key : Row → Key) (buckets : Key → List Row) : List Row → Key → List Row
  | [], sought => buckets sought
  | row :: rest, sought => build key (insert key buckets row) rest sought

/-- The complete key lookup has the exact reversed source bucket, including repetitions. -/
theorem build_exact [DecidableEq Key] (key : Row → Key) (buckets : Key → List Row)
    (rows : List Row) (sought : Key) :
    build key buckets rows sought = (rows.filter fun row => decide (sought = key row)).reverse ++ buckets sought := by
  induction rows generalizing buckets with
  | nil => rfl
  | cons row rest ih =>
    rw [build, ih]
    by_cases same : sought = key row <;> simp [insert, same, List.append_assoc]

/-- Probe the completed table for each left row. -/
def hashJoin [DecidableEq Key] (key : Row → Key) (join : Row → Row → Result)
    (left right : List Row) : List Result :=
  left.flatMap fun row => (build key (fun _ => []) right (key row)).map (join row)

/-- The executable table join is an ordered Cartesian loop over exactly the matching buckets. -/
theorem hashJoin_exact [DecidableEq Key] (key : Row → Key) (join : Row → Row → Result)
    (left right : List Row) :
    hashJoin key join left right =
      left.flatMap fun row => ((right.filter fun other => decide (key row = key other)).reverse).map (join row) := by
  simp [hashJoin, build_exact]

/-- Every equal-key pair is emitted, and every emitted pair has equal complete keys. -/
theorem hashJoin_member [DecidableEq Key] (key : Row → Key) (join : Row → Row → Result)
    (left right : List Row) (result : Result) :
    result ∈ hashJoin key join left right ↔
      ∃ first ∈ left, ∃ second ∈ right, key first = key second ∧ join first second = result := by
  simp only [hashJoin_exact, List.mem_flatMap, List.mem_map, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨first, firstMember, second, ⟨secondMember, same⟩, output⟩
    exact ⟨first, firstMember, second, secondMember, same, output⟩
  · rintro ⟨first, firstMember, second, secondMember, same, output⟩
    exact ⟨first, firstMember, second, ⟨secondMember, same⟩, output⟩

/-- Bucket construction never removes a repeated matching occurrence. -/
theorem bucket_length [DecidableEq Key] (key : Row → Key) (right : List Row) (sought : Key) :
    (build key (fun _ => []) right sought).length = (right.filter fun row => decide (sought = key row)).length := by
  simp [build_exact]

/-- The join emits one occurrence per matching right occurrence for each left occurrence. -/
theorem hashJoin_length [DecidableEq Key] (key : Row → Key) (join : Row → Row → Result)
    (left right : List Row) :
    (hashJoin key join left right).length =
      (left.map fun first => (right.filter fun second => decide (key first = key second)).length).sum := by
  simp [hashJoin, List.length_flatMap, bucket_length]

end MicroCFTA.SymbolicHashJoin
