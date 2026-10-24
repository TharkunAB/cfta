from pathlib import Path
import hashlib, json

area = Path('/tmp/mcfta-pruning-enumeration-native-index-20261025')
owner = Path(str(area) + '-proposal')
assert json.loads((area / 'body-gate.json').read_text())['status'] == 'ACCEPTED_BEFORE_ANY_BODY_OR_ACTIVATION'
def fragment(name):
    return (owner / name).read_text().rstrip('\n')
def local(name, body, indent=2):
    return ' ' * indent + fragment(name) + ' := by\n' + body
parts = [fragment('context.lean.txt') + '\n\n']
parts.append(fragment('instance-header.lean.txt') + ''' := {
  pure := fun value => [value]
  bind := fun values continuation => values.flatMap continuation
}

''')
parts.append('/-- Classify the actual decoded node without replacing a missing handle. -/\n')
parts.append(fragment('candidate-header.lean.txt') + ''' :=
  match value with
  | .unenumerated node scs =>
      match node with
      | none => some false
      | some handle =>
          (lookupNode heap handle).map fun decodedValue =>
            !(MergedOrdinaryHeight.recursiveBoundary decodedValue && scs.isEmpty)
  | .enumerated _ | .eliminated => some false

''')
parts.append('/-- Count each occurrence at its current read-only representative. -/\n')
parts.append(fragment('count-header.lean.txt') + ''' :=
  match scs with
  | [] => some waiting
  | sc :: rest =>
      (SourceUnionFindRoot.root fuel forest sc.var).bind fun representative =>
        count fuel forest change rest (EnumerationWaitingIndex.bump change representative waiting)

''')
parts.append('/-- Update the raw slot and remove lost counts before adding gained counts. -/\n')
parts.append(fragment('write-header.lean.txt') + ''' :=
  (candidate heap value).bind fun flag =>
    (count fuel before.core.representatives (-1) lost before.waiting).bind fun removed =>
      (count fuel before.core.representatives 1 gained removed).bind fun saved =>
        some ⟨{before.core with values := before.core.values.set target value},
          fun other => if other = target then flag else before.expandable other, saved⟩

''')
parts.append('/-- Finite parent paths give one bound for every change and waiting map. -/\n')
parts.append(fragment('count-complete-header.lean.txt') + ''' := by
  induction scs with
  | nil => exact ⟨0, fun _ _ _ => rfl⟩
  | cons sc rest ih =>
    obtain ⟨tailFuel, tailRun⟩ := ih
    obtain ⟨size, path⟩ := paths sc.var
    obtain ⟨headFuel, headRun⟩ :=
      SourceUnionFindRoot.root_terminates forest sc.var (roots sc.var) size path
    refine ⟨headFuel + tailFuel, ?_⟩
    intro extra change waiting
''')
parts.append(local('local-root-run.lean.txt', '''      simpa only [Nat.add_assoc] using
        SourceUnionFindRoot.root_moreFuel headFuel (tailFuel + extra) forest sc.var (roots sc.var) headRun
''', 4))
parts.append('''    rw [count, rootRun, Option.bind_some]
    simpa only [EnumerationCanonicalWaiting.count, List.map_cons,
      EnumerationWaitingIndex.count, List.foldl_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tailRun (headFuel + extra) change (EnumerationWaitingIndex.bump change (roots sc.var) waiting)

''')
parts.append('/-- Derive native indexes at the same observed value-write and ancestry prefix. -/\n')
parts.append(fragment('gained-complete-header.lean.txt') + ''' := by
  obtain ⟨fuel, countRun⟩ := count_complete before.core.representatives roots paths incomingScs
''')
parts.append(local('local-inside.lean.txt', '''    exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)
'''))
parts.append(local('local-after-same.lean.txt', '''    change [.ok ((), {before.core with
      values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups
        else before.core.recursionAncestry other})] = [.ok ((), after)] at actualPrefix
    exact (Prod.mk.inj (Except.ok.inj (List.cons.inj actualPrefix).1)).2.symm
'''))
parts.append(local('local-grown-flags.lean.txt', '''    intro slot
    specialize flags slot
    generalize slotValueSame : ((before.core.values[slot]?).getD .eliminated) = slotValue at flags ⊢
    clear slotValueSame
    cases slotValue with
    | enumerated _ => exact flags
    | eliminated => exact flags
    | unenumerated node scs =>
      cases node with
      | none => exact flags
      | some oldHandle =>
        cases oldLookup : lookupNode heap oldHandle with
        | none =>
          simp only [candidate, oldLookup, Option.map_none] at flags
          cases flags
        | some oldValue =>
          simpa only [candidate, oldLookup,
            lookupNode_keeps heap nextHeap kept oldHandle oldValue oldLookup, Option.map_some] using flags
'''))
parts.append(local('local-written-flags.lean.txt', '''    intro slot
    by_cases same : slot = target
    · subst slot
      simp only [List.getElem?_set_self inside, Option.getD_some, candidate, decoded,
        Option.map_some, ↓reduceIte]
    · simpa only [List.getElem?_set_ne (Ne.symm same), if_neg same] using grownFlags slot
'''))
parts.append('''  refine ⟨fuel, ⟨{before.core with
    values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))},
    fun slot => if slot = target then
      !(MergedOrdinaryHeight.recursiveBoundary value && (incomingScs ++ oldScs).isEmpty)
      else before.expandable slot,
    EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting⟩,
    ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro extra
    simp only [write, candidate, decoded, Option.map_some,
      show count (fuel + extra) before.core.representatives (-1) [] before.waiting =
        some before.waiting from rfl,
      Option.bind_some, countRun extra 1 before.waiting]
  · simpa only [afterSame, List.length_set] using aligned
  · simpa only [afterSame] using paths
  · simpa only [afterSame] using
      SourcePruningEnumerationTerminal.gained_correct before.core.values target oldNode
        (some handle) incomingScs oldScs roots before.waiting stored counts
  · simpa only [afterSame] using writtenFlags

end MicroCFTA.SourcePruningEnumerationNativeIndex
''')
source = ''.join(parts)
for literal in json.loads((owner / 'contracts.json').read_text()).values():
    assert source.count(literal.rstrip('\n')) == 1
path = area / 'SourcePruningEnumerationNativeIndex.lean'
assert not path.exists()
path.write_text(source)
print(json.dumps(dict(lines=len(source.splitlines()), bytes=len(source.encode()),
    sha256=hashlib.sha256(source.encode()).hexdigest(), author='Root', gate='accepted before bodies')))
