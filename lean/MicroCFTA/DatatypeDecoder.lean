import MicroCFTA.SymbolRelabel
import MicroCFTA.Generic

/-!
# Hashed datatype constructor decoding

The source stores constructor entries by symbol hash. Each bucket retains
the full symbol and checks its equality. Insertion prepends the new entry,
as IntMap.fromListWith (<>) does. No hash injectivity assumption is needed.
-/
namespace MicroCFTA.DatatypeDecoder
open Language

/-- The source bucket lookup checks the complete symbol after selecting a hash. -/
def lookup [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (stored, value) :: rest => if key = stored then some value else lookup key rest

/-- A finite hash map is viewed through its bucket lookup. -/
abbrev Table (Key Value : Type) := Int → List (Key × Value)

/-- Insert one singleton bucket with the source new-before-old combination. -/
def insert (hash : Key → Int) (table : Table Key Value) (entry : Key × Value) : Table Key Value :=
  fun bucket => if bucket = hash entry.1 then entry :: table bucket else table bucket

/-- Read the selected hash bucket and then compare full symbols. -/
def find [DecidableEq Key] (hash : Key → Int) (table : Table Key Value) (key : Key) : Option Value :=
  lookup key (table (hash key))

/-- Hash collisions do not alter one insertion's exact key semantics. -/
theorem insert_find [DecidableEq Key] (hash : Key → Int) (table : Table Key Value)
    (entry : Key × Value) (key : Key) :
    find hash (insert hash table entry) key = if key = entry.1 then some entry.2 else find hash table key := by
  rcases entry with ⟨stored, value⟩
  by_cases same : key = stored
  · subst key
    simp [find, insert, lookup]
  · by_cases collision : hash key = hash stored <;> simp [find, insert, lookup, same, collision]

/-- Build the source table in transition-table order. -/
def build (hash : Key → Int) (entries : List (Key × Value)) : Table Key Value :=
  entries.foldl (insert hash) (fun _ => [])

/-- Direct key insertion provides the ordinary map lookup reference. -/
def directInsert [DecidableEq Key] (table : Key → Option Value) (entry : Key × Value) : Key → Option Value :=
  fun key => if key = entry.1 then some entry.2 else table key

/-- Build the direct map with the same last-entry precedence. -/
def direct [DecidableEq Key] (entries : List (Key × Value)) : Key → Option Value :=
  entries.foldl directInsert (fun _ => none)

/-- Every prefix of the hash-table fold has the same direct-key meaning. -/
theorem fold_find [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Value))
    (table : Table Key Value) :
    find hash (entries.foldl (insert hash) table) = entries.foldl directInsert (find hash table) := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih]
      congr 1
      funext key
      exact insert_find hash table entry key

/-- Optimized lookup equals ordinary map lookup for every hash function. -/
theorem find_exact [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Value)) (key : Key) :
    find hash (build hash entries) key = direct entries key := by
  exact congrFun (fold_find hash entries (fun _ => [])) key

/-- A coherent constructor table has one value for every repeated full label. -/
def Coherent (entries : List (Key × Value)) : Prop :=
  ∀ key left right, (key, left) ∈ entries → (key, right) ∈ entries → left = right

/-- Any stored direct-map answer came from the initial table or an inserted entry. -/
theorem direct_fold_member [DecidableEq Key] (entries : List (Key × Value))
    (table : Key → Option Value) (key : Key) (value : Value)
    (found : entries.foldl directInsert table key = some value) :
    table key = some value ∨ (key, value) ∈ entries := by
  induction entries generalizing table with
  | nil => exact Or.inl found
  | cons entry rest ih =>
      rcases ih (directInsert table entry) found with head | tail
      · rcases entry with ⟨stored, item⟩
        by_cases same : key = stored
        · have equal : item = value := by simpa [directInsert, same] using head
          subst stored
          subst item
          exact Or.inr (by simp)
        · exact Or.inl (by simpa [directInsert, same] using head)
      · exact Or.inr (by simp [tail])

/-- An inserted coherent label has the same constructor after every later insertion. -/
theorem direct_fold_preserves [DecidableEq Key] (entries : List (Key × Value))
    (table : Key → Option Value) (key : Key) (value : Value)
    (initial : table key = some value) (consistent : ∀ other, (key, other) ∈ entries → other = value) :
    entries.foldl directInsert table key = some value := by
  induction entries generalizing table with
  | nil => exact initial
  | cons entry rest ih =>
      apply ih
      · rcases entry with ⟨stored, item⟩
        by_cases same : key = stored
        · have equal := consistent item (by simp [same])
          simp [directInsert, same, equal]
        · simp [directInsert, same, initial]
      · intro other member
        exact consistent other (by simp [member])

/-- Every present coherent label decodes to its stored constructor. -/
theorem direct_member [DecidableEq Key] (entries : List (Key × Value)) (coherent : Coherent entries)
    (key : Key) (value : Value) (member : (key, value) ∈ entries) : direct entries key = some value := by
  have foldMember : ∀ table, entries.foldl directInsert table key = some value := by
    induction entries with
    | nil => simp at member
    | cons entry rest ih =>
        intro table
        rcases List.mem_cons.mp member with same | tail
        · subst entry
          exact direct_fold_preserves rest (directInsert table (key, value)) key value (by simp [directInsert])
            (fun other present => coherent key other value (by simp [present]) (by simp))
        · exact ih (fun key left right first second => coherent key left right (by simp [first]) (by simp [second]))
            tail (directInsert table entry)
  exact foldMember (fun _ => none)

/-- Optimized constructor lookup succeeds exactly on the coherent stored labels. -/
theorem find_iff [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Value))
    (coherent : Coherent entries) (key : Key) (value : Value) :
    find hash (build hash entries) key = some value ↔ (key, value) ∈ entries := by
  rw [find_exact]
  constructor
  · intro found
    rcases direct_fold_member entries (fun _ => none) key value found with impossible | member
    · cases impossible
    · exact member
  · exact direct_member entries coherent key value

/-- Traverse ordered children with an optional constructor restoration. -/
def restore (constructor : Key → Option Value) : Term Key → Option (Term Value)
  | .node key children => do
      let label ← constructor key
      let values ← restoreMany constructor children
      pure (.node label values)
where
  restoreMany (constructor : Key → Option Value) : List (Term Key) → Option (List (Term Value))
    | [] => some []
    | first :: rest => do
        let value ← restore constructor first
        let values ← restoreMany constructor rest
        pure (value :: values)

/-- Hash lookup changes no result of full-term constructor restoration. -/
theorem restore_exact [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Value)) (term : Term Key) :
    restore (find hash (build hash entries)) term = restore (direct entries) term := by
  have same : find hash (build hash entries) = direct entries := funext (find_exact hash entries)
  rw [same]

/-- The optimized datatype decoder differs only in the proved constructor lookup. -/
def decode [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Constructor))
    (codec : Term Constructor → Option Value) (term : Term Key) : Option Value :=
  (restore (find hash (build hash entries)) term).bind codec

/-- Even a partial or noninjective caller codec gets the exact same result. -/
theorem decode_exact [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Constructor))
    (codec : Term Constructor → Option Value) (term : Term Key) :
    decode hash entries codec term = (restore (direct entries) term).bind codec := by
  rw [decode, restore_exact]

/-- Independent syntax recognition records every constructor at every position. -/
inductive Restores (relation : Key → Constructor → Prop) : Term Key → Term Constructor → Prop where
  | node : relation key constructor → All₂ (Restores relation) children values →
      Restores relation (.node key children) (.node constructor values)

/-- Optional traversal agrees with independent pointwise constructor recognition. -/
theorem restore_iff (constructor : Key → Option Value) (term : Term Key) (value : Term Value) :
    restore constructor term = some value ↔ Restores (fun key value => constructor key = some value) term value := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ values, restore.restoreMany constructor terms = some values ↔
      All₂ (Restores (fun key value => constructor key = some value)) terms values)
    generalizing value with
  | node key children ih =>
      cases value with
      | node label values =>
          constructor
          · intro found
            cases chosen : constructor key with
            | none => simp [restore, chosen] at found
            | some symbol =>
                cases walked : restore.restoreMany constructor children with
                | none => simp [restore, chosen, walked] at found
                | some terms =>
                    have same : Term.node symbol terms = Term.node label values := by
                      simpa [restore, chosen, walked] using found
                    cases same
                    exact .node chosen ((ih values).mp walked)
          · intro recognized
            cases recognized with
            | node head tail => simp [restore, head, (ih values).mpr tail]
  | nil =>
      rename_i values
      constructor
      · intro found
        have same : values = [] := Option.some.inj found.symm
        subst values
        exact .nil
      · intro recognized
        cases recognized
        rfl
  | cons first rest ih ir =>
      rename_i values
      constructor
      · intro found
        cases head : restore constructor first with
        | none => simp [restore.restoreMany, head] at found
        | some value =>
            cases tail : restore.restoreMany constructor rest with
            | none => simp [restore.restoreMany, head, tail] at found
            | some terms =>
                have same : values = value :: terms := by simpa [restore.restoreMany, head, tail] using found.symm
                subst values
                exact .cons ((ih value).mp head) ((ir terms).mp tail)
      · intro recognized
        cases recognized with
        | cons head tail => simp [restore.restoreMany, (ih _).mpr head, (ir _).mpr tail]

/-- Pointwise equivalent constructor relations recognize exactly the same trees. -/
theorem restores_congr (first second : Key → Constructor → Prop)
    (same : ∀ key value, first key value ↔ second key value) (term : Term Key) (value : Term Constructor) :
    Restores first term value ↔ Restores second term value := by
  have transport : ∀ (left right : Key → Constructor → Prop), (∀ key value, left key value → right key value) →
      ∀ term value, Restores left term value → Restores right term value := by
    intro left right weaken term value recognized
    induction term using Term.rec
      (motive_2 := fun children => ∀ values, All₂ (Restores left) children values →
        All₂ (Restores right) children values) generalizing value with
    | node key children ih =>
        cases recognized with
        | node head tail => exact .node (weaken _ _ head) (ih _ tail)
    | nil =>
        rename_i values found
        cases found
        exact .nil
    | cons first rest ih ir =>
        rename_i values found
        cases found with
        | cons head tail => exact .cons (ih _ head) (ir _ tail)
  exact ⟨transport first second (fun key value => (same key value).mp) term value,
    transport second first (fun key value => (same key value).mpr) term value⟩

/-- Successful optimized restoration is exactly recognition by the stored constructor table. -/
theorem restore_table_iff [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Constructor))
    (coherent : Coherent entries) (term : Term Key) (value : Term Constructor) :
    restore (find hash (build hash entries)) term = some value ↔
      Restores (fun key constructor => (key, constructor) ∈ entries) term value :=
  (restore_iff _ term value).trans (restores_congr _ _ (find_iff hash entries coherent) term value)

/-- Every symbol of a constructor term belongs to the supplied datatype rows. -/
def InAlphabet (constructors : List Constructor) : Term Constructor → Prop
  | .node constructor children => constructor ∈ constructors ∧ ∀ child ∈ children, InAlphabet constructors child

/-- Unique labels on the actual constructor set make the stored table coherent. -/
theorem constructor_table_coherent (label : Constructor → Key) (constructors : List Constructor)
    (unique : ∀ left ∈ constructors, ∀ right ∈ constructors, label left = label right → left = right) :
    Coherent (constructors.map (fun constructor => (label constructor, constructor))) := by
  intro key left right first second
  simp only [List.mem_map, Prod.mk.injEq] at first second
  obtain ⟨a, ha, ka, rfl⟩ := first
  obtain ⟨b, hb, kb, rfl⟩ := second
  exact unique a ha b hb (ka.trans kb.symm)

/-- Relabelling an admitted constructor term retains every stored constructor match. -/
theorem labelled_recognized (label : Constructor → Key) (constructors : List Constructor)
    (term : Term Constructor) (admitted : InAlphabet constructors term) :
    Restores (fun key value => (key, value) ∈ constructors.map (fun value => (label value, value)))
      (SymbolRelabel.termMap label term) term := by
  induction term using Term.rec
    (motive_2 := fun children => (∀ child ∈ children, InAlphabet constructors child) →
      All₂ (Restores (fun key value => (key, value) ∈ constructors.map (fun value => (label value, value))))
        (children.map (SymbolRelabel.termMap label)) children) with
  | node symbol children ih =>
      simp only [InAlphabet] at admitted
      simp only [SymbolRelabel.termMap]
      apply Restores.node
      · exact List.mem_map.mpr ⟨symbol, admitted.1, rfl⟩
      · exact ih admitted.2
  | nil => exact .nil
  | cons first rest ih ir =>
      rename_i present
      exact .cons (ih (present first (by simp))) (ir (fun term member => present term (by simp [member])))

/-- Hashed decoding of an admitted relabelled term calls the original codec on exactly that term. -/
theorem decode_labelled [DecidableEq Key] (hash : Key → Int) (label : Constructor → Key)
    (constructors : List Constructor)
    (unique : ∀ left ∈ constructors, ∀ right ∈ constructors, label left = label right → left = right)
    (codec : Term Constructor → Option Value) (term : Term Constructor) (admitted : InAlphabet constructors term) :
    decode hash (constructors.map (fun value => (label value, value))) codec (SymbolRelabel.termMap label term) = codec term := by
  have restored := (restore_table_iff hash _ (constructor_table_coherent label constructors unique) _ term).mpr
    (labelled_recognized label constructors term admitted)
  simp [decode, restored]

/-- Every admitted term rank remains decodable through the optimized label table. -/
theorem ranked_total [DecidableEq Key] (hash : Key → Int) (label : Constructor → Key)
    (constructors : List Constructor)
    (unique : ∀ left ∈ constructors, ∀ right ∈ constructors, label left = label right → left = right)
    (index : DistinctRank.Index Accepted) (codec : Generic.Codec Accepted Value)
    (alphabet : ∀ term, Accepted term → InAlphabet constructors term) (rank : Fin index.count) :
    ∃ value, decode hash (constructors.map (fun value => (label value, value))) codec.decode
      (SymbolRelabel.termMap label (index.decode rank).val) = some value := by
  rw [decode_labelled hash label constructors unique codec.decode _ (alphabet _ (index.decode rank).property)]
  exact codec.total _ (index.decode rank).property

/-- A codec inverse makes distinct source term ranks give distinct decoded values. -/
theorem ranked_injective [DecidableEq Key] (hash : Key → Int) (label : Constructor → Key)
    (constructors : List Constructor)
    (unique : ∀ left ∈ constructors, ∀ right ∈ constructors, label left = label right → left = right)
    (index : DistinctRank.Index Accepted) (codec : Generic.Codec Accepted Value)
    (alphabet : ∀ term, Accepted term → InAlphabet constructors term)
    (first second : Fin index.count) (value : Value)
    (firstDecoded : decode hash (constructors.map (fun value => (label value, value))) codec.decode
      (SymbolRelabel.termMap label (index.decode first).val) = some value)
    (secondDecoded : decode hash (constructors.map (fun value => (label value, value))) codec.decode
      (SymbolRelabel.termMap label (index.decode second).val) = some value) : first = second := by
  rw [decode_labelled hash label constructors unique codec.decode _ (alphabet _ (index.decode first).property)] at firstDecoded
  rw [decode_labelled hash label constructors unique codec.decode _ (alphabet _ (index.decode second).property)] at secondDecoded
  exact Generic.codec_rank_injective index codec first second value firstDecoded secondDecoded

/-- Count the full-symbol comparisons in one source bucket lookup. -/
def comparisons [DecidableEq Key] (key : Key) : List (Key × Value) → Nat
  | [] => 0
  | (stored, _) :: rest => 1 + if key = stored then 0 else comparisons key rest

/-- Even when every hash collides, a lookup compares at most the bucket length. -/
theorem comparisons_bound [DecidableEq Key] (key : Key) (entries : List (Key × Value)) :
    comparisons key entries ≤ entries.length := by
  induction entries with
  | nil => simp [comparisons]
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      by_cases same : key = stored <;> simp [comparisons, same] <;> omega

/-- Each insertion increases any selected hash bucket by at most one entry. -/
theorem bucket_fold_bound (hash : Key → Int) (entries : List (Key × Value))
    (table : Table Key Value) (bucket : Int) :
    (entries.foldl (insert hash) table bucket).length ≤ (table bucket).length + entries.length := by
  induction entries generalizing table with
  | nil => simp
  | cons entry rest ih =>
      have tail := ih (insert hash table entry)
      have one : (insert hash table entry bucket).length ≤ (table bucket).length + 1 := by
        simp only [insert]
        split <;> simp <;> omega
      simp only [List.foldl_cons, List.length_cons]
      omega

/-- The collision-sensitive lookup cost is never more than the stored constructor count. -/
theorem lookup_cost_bound [DecidableEq Key] (hash : Key → Int) (entries : List (Key × Value)) (key : Key) :
    comparisons key (build hash entries (hash key)) ≤ entries.length := by
  have bucket := bucket_fold_bound hash entries (fun _ => []) (hash key)
  exact Nat.le_trans (comparisons_bound key _) (by simpa [build] using bucket)

/-- An absent symbol examines every colliding entry rather than accepting a hash match. -/
theorem absent_comparisons [DecidableEq Key] (key : Key) (entries : List (Key × Value))
    (absent : ∀ value, (key, value) ∉ entries) : comparisons key entries = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      have different : key ≠ stored := by intro same; exact absent value (by simp [same])
      have tail := ih (fun value member => absent value (by simp [member]))
      simp [comparisons, different, tail, Nat.add_comm]

example : find (fun _ : Nat => (0 : Int)) (build (fun _ => 0) [(1, 10), (2, 20), (1, 30)]) 2 = some 20 := by cbv
example : find (fun _ : Nat => (0 : Int)) (build (fun _ => 0) [(1, 10), (2, 20), (1, 30)]) 1 = some 30 := by cbv
example : decode (fun _ : Nat => (0 : Int)) [(1, 10), (2, 20)] some (.node 1 [.node 2 []]) =
    some (.node 10 [.node 20 []]) := by cbv

end MicroCFTA.DatatypeDecoder
