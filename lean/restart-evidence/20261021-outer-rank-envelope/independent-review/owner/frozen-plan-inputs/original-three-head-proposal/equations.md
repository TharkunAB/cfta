# Exact numeric equations

Use `Seed = List Guard × Profile` and `Out = Nat × Nat × Seed` only as local notation. There is no new public datatype.
Write `P = SourceCurrentOuterInitialSchedule.parent`, `R = SourceCurrentOuterInitialSchedule.rebuild`, `J = SourceCurrentInitialSelectionForecast.cover`, and `M = SourceCurrentInitialSelectionForecast.maximum`.
Write `N budget s = SourceCurrentParentUniformEnvelope.fuel budget s.alphabet s.profile`.

For rank `r=(n,m)` and a literal seed `s`, define the ordered finite candidate list:

```text
K r s = filter (a<n OR (a=n AND b<m))
          (flatMap a∈range(n+1) (map b∈range(s.profile.mass+1) (a,b)))
I r s = map (a,b)∈K r s (C budget (a,b) s)
joinSeed s xs =
  (s.alphabet ++ flatMap (fun x => x.output.alphabet) xs,
   J (map (fun x => x.output.profile) xs) s.profile)
```

The bounds and filter prove that every recursive call has strict smaller rank. The seed argument can change at a later fold step. The recursive calls inside one `I r s` all use the same `s`.

```text
slot r (w,l,s) =
  let xs = I r s
  (w + 1 + M (map W xs), max l (M (map L xs)), joinSeed s xs)

walk r B s = foldl slot(r) (0,0,s) (range B)

row r (w,l,s) =
  let p = P budget s
  let t = walk r p.profile.mass p
  (w + 1 + t.W, max l (max (N budget s) t.L), R t.output)

rows r s = foldl row(r) (0,0,s) (range r.mass)

C budget r s =
  let t = rows r s
  (1 + t.W, t.L, R t.output)
```

`slot` and `row` ignore the value of the `range` index. The range length fixes the number of iterations. The Parent mass for a row is frozen before its child fold. Later slot masses change only the candidate image for that slot.
`C` is the well-founded fixpoint of these equations. The private body uses `K.attach` to supply the local recursive proof. The public stage statement expands the finite steps and uses the public `envelope` for their recursive outputs. It exposes no private helper.

# Work arithmetic

Let `A_j` be the row accumulator after `j` rows. Let `p_j=P budget A_j.output` and `B_j=p_j.profile.mass`. Let `S_jk` be the slot accumulator after `k` slots in that row.
Each row adds at least one. Each slot adds at least one. Hence `j ≤ A_j.W` and `k ≤ S_jk.W`.
For `j<m` and `k≤B_j`, `A_j.W + S_jk.W + 2 ≤ C.W`. The two units pay for the ordinary body and the selected row.
For `k<B_j` and a candidate `t∈I r S_jk.output`, the next slot contributes `1+t.W` or more. Thus `t.W+3+j+k ≤ C.W`.
These inequalities imply `0<C.W`, `m<C.W`, `j+1<C.W`, and `j+k+2<C.W` at a nonempty selected slot. They give the exact positive fuel needed at body, row, and walk tests.
At `m=0`, `C.W=1`; an ordinary body at fuel one enters `rows 0 []`, which succeeds. At `B_j=0`, the walk costs zero and `walk 0 []` succeeds.
No body step is charged by the actual worker for empty, union, or Mu values. The extra positive unit in `C` is a permitted overestimate for those cases. Other fault and closure obligations remain in their existing semantic components.

# Retention and lower fuel

Every seed join retains its baseline and each candidate output. `P` and `R` retain their input profile and alphabet.
Every row accumulator retains the earlier row seed. Every slot accumulator retains the earlier slot seed. A later accumulator therefore retains ALL earlier numeric peaks, not only the final selected candidate.
Each row contributes `N budget A_j.output` to the maximum. Each slot contributes every candidate `L`. Thus the final `L` bounds every numeric Parent fuel and every numeric recursive lower maximum.
These are finite arithmetic laws. Actual Parent reservations, all actual nested lower calls, and same-root physical Room coverage are separate unproved obligations.
