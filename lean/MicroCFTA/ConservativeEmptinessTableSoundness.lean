import MicroCFTA.ConservativeEmptinessTable
import MicroCFTA.ConservativeEmptinessRows

/-!
# Semantic soundness of actual finite emptiness tables

The table determines the finite carrier and all Boolean rounds. Stored rows
must retain their supplied source-shaped requirements. The semantic node type
must contain only certified inputs. In particular, raw source values do not
satisfy global physical-key readback without availability and closure proofs.
This module uses completed list-map rows. Native containers, lazy row demands,
source edge exposure, projection, and intersection remain separate transfers.
-/
namespace MicroCFTA.ConservativeEmptinessTableSoundness
open Language EqualityReduction ConservativeEmptinessExplore

variable {Node Symbol : Type}

/-- Every stored first-lookup row list is the exact row list supplied for its key. -/
def StoredSupply (table : Table) (supply : Int → Rows) : Prop :=
  ∀ key rows, lookup key table = some rows → rows = supply key

/-- Actual exploration preserves exact supplied rows at every stored key. -/
theorem explore_stored (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item)
    (stored : StoredSupply seen supply) : StoredSupply (explore supply budget seen pending) supply := by
  rw [explore.eq_def]
  cases pending with
  | nil => exact stored
  | cons first rest =>
      cases first with
      | empty => exact explore_stored supply budget seen rest stored
      | resident key closed =>
          by_cases skipped : skip budget seen key closed = true
          · simpa only [skipped, ↓reduceIte] using explore_stored supply budget seen rest stored
          · simp only [skipped, Bool.false_eq_true, ↓reduceIte]
            apply explore_stored supply (budget - 1) ((key, supply key) :: seen) ((supply key).flatten ++ rest)
            intro queried rows found
            by_cases same : queried = key
            · subst queried
              simpa only [lookup, ↓reduceIte, Option.some.injEq] using found.symm
            · exact stored queried rows (by simpa only [lookup, same, ↓reduceIte] using found)
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have positive := (admitted budget seen key closed (Bool.eq_false_iff.mpr skipped)).1
    omega

/-- Empty-start exploration derives every stored row receipt without a supplied table invariant. -/
theorem entered_rows (supply : Int → Rows) (budget : Nat) (pending : List Item) :
    StoredSupply (explore supply budget [] pending) supply :=
  explore_stored supply budget [] pending (by intro key rows impossible; cases impossible)

/-- Encode original source-shaped rows without changing row or requirement order. -/
def rowSupply (ops : Operations Node Symbol) (encode : Node → Item) (exposed : Int → List (ConservativeEmptinessRows.Row Node))
    (key : Int) : Rows :=
  (exposed key).map (fun row => (ConservativeEmptinessRows.requirements ops row).map encode)

/-- Actual stored rows classify to exactly the semantic source-shaped rows on the derived carrier. -/
theorem rows_agree (table : Table) (ops : Operations Node Symbol) (encode : Node → Item)
    (exposed : Int → List (ConservativeEmptinessRows.Row Node)) (stored : StoredSupply table (rowSupply ops encode exposed)) :
    ConservativeEmptinessTable.rows table = ConservativeEmptinessRows.graphRows ops (fun node => ConservativeEmptinessTable.classify table (encode node)) (fun state => exposed state.val) := by
  funext state
  cases found : lookup state.val table with
  | none => exact False.elim ((lookup_none_iff state.val table).mp found state.property)
  | some original =>
      have actual := stored state.val original found
      simp only [ConservativeEmptinessTable.rows, found, Option.getD_some, actual, rowSupply, ConservativeEmptinessRows.graphRows,
        List.map_map, Function.comp_def]

/-- Certified physical readback transfers an accepted original query into its actual classified requirement. -/
theorem query_accepted (table : Table) (ops : Operations Node Symbol) (laws : ConservativeEmptinessRows.PrimitiveLaws ops)
    (encode : Node → Item) (read : ConservativeEmptinessTable.Key table → Node)
    (readback : ConservativeEmptinessRows.Readback ops read (fun node => ConservativeEmptinessTable.classify table (encode node)))
    (query : Node) (term : Term Symbol) (accepted : ops.meaning query term) :
    ConservativeEmptiness.AcceptsRequirement (fun state => ops.meaning (read state))
      (ConservativeEmptinessTable.classify table (encode query)) term := by
  have identity := readback query
  cases classified : ConservativeEmptinessTable.classify table (encode query) with
  | empty =>
      simp only [classified] at identity
      exact laws.empty term (identity ▸ accepted)
  | outside => trivial
  | inside state =>
      simp only [classified] at identity
      simpa only [identity, ConservativeEmptiness.AcceptsRequirement] using accepted

/-- Literal table emptiness is sound from primitive semantics, certified readback, and local row exposure. -/
theorem provablyEmpty_sound (table : Table) (ops : Operations Node Symbol) (laws : ConservativeEmptinessRows.PrimitiveLaws ops)
    (encode : Node → Item) (exposed : Int → List (ConservativeEmptinessRows.Row Node))
    (stored : StoredSupply table (rowSupply ops encode exposed)) (read : ConservativeEmptinessTable.Key table → Node)
    (readback : ConservativeEmptinessRows.Readback ops read (fun node => ConservativeEmptinessTable.classify table (encode node)))
    (exposure : ConservativeEmptinessRows.Exposure ops read (fun state => exposed state.val)) (query : Node)
    (empty : ConservativeEmptinessTable.provablyEmpty table (encode query) = true) : ∀ term, ¬ops.meaning query term := by
  have finite : ConservativeEmptiness.provablyEmpty (ConservativeEmptinessTable.states table) (ConservativeEmptinessTable.rows table)
      (ConservativeEmptinessTable.classify table (encode query)) = true := by
    rwa [← ConservativeEmptinessTable.provablyEmpty_agrees]
  rw [rows_agree table ops encode exposed stored] at finite
  have excludes := ConservativeEmptinessRows.provablyEmpty_sound (ConservativeEmptinessTable.states table) (ConservativeEmptinessTable.states_complete table) ops laws read _ readback
    (fun state => exposed state.val) exposure _ finite
  intro term accepted
  exact excludes term (query_accepted table ops laws encode read readback query term accepted)

/-- Empty-start exploration derives the stored-row premise of literal table soundness. -/
theorem explored_sound (ops : Operations Node Symbol) (laws : ConservativeEmptinessRows.PrimitiveLaws ops)
    (encode : Node → Item) (exposed : Int → List (ConservativeEmptinessRows.Row Node)) (budget : Nat) (pending : List Item)
    (read : ConservativeEmptinessTable.Key (explore (rowSupply ops encode exposed) budget [] pending) → Node)
    (readback : ConservativeEmptinessRows.Readback ops read
      (fun node => ConservativeEmptinessTable.classify (explore (rowSupply ops encode exposed) budget [] pending) (encode node)))
    (exposure : ConservativeEmptinessRows.Exposure ops read (fun state => exposed state.val)) (query : Node)
    (empty : ConservativeEmptinessTable.provablyEmpty (explore (rowSupply ops encode exposed) budget [] pending) (encode query) = true) :
    ∀ term, ¬ops.meaning query term :=
  provablyEmpty_sound _ ops laws encode exposed (entered_rows _ budget pending) read readback exposure query empty

/-- The exploration budget also bounds equality-stop checks after the completed rows are available. -/
theorem explored_grow_complete (supply : Int → Rows) (budget : Nat) (pending : List Item) :
    let table := explore supply budget [] pending
    ConservativeEmptinessTable.grow table (budget + 1) (fun _ => false) = some (ConservativeEmptinessTable.possible table) := by
  dsimp only
  apply ConservativeEmptinessTable.grow_rounds_complete _ budget 0
  simpa only [List.length_nil, Nat.zero_add] using length_le supply budget [] pending

end MicroCFTA.ConservativeEmptinessTableSoundness
