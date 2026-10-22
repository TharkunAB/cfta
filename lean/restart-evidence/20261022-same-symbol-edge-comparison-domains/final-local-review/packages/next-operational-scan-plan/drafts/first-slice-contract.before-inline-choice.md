# First proposed implementation slice

Working source: SourceCurrentOriginalRowClusterScan.lean. Import the existing H7 control; no H15 resource import is needed for this operational slice.
Supply Control, Outcome, step and execute exactly as described in proposed-control.md. Reuse H7.State and H7.Blocked.
One public operational theorem, comparison_lift, has these precise parameters: width and fuel; the existing required Symbol/EdgeKey equality instances; pivot, candidate and common : Edge; tail, inc and kept : List Edge; inner : H7.Control; before and after : H7.State width.
Its only observation premise is the actual H7.execute fuel inner before = H7.Outcome.done common after.
Its exact proposed conclusion is the following source-level expression. It is a contract, not an implemented declaration:

    ∃ used, 0 < used ∧ used ≤ fuel ∧
      Scan.execute used (.comparison pivot candidate tail inc kept inner) before =
        .yielded
          (if common.entry.identity = candidate.entry.identity then
             .scan pivot tail inc kept
           else if common.entry.identity = pivot.entry.identity then
             .cluster (candidate :: (inc.reverse ++ tail)) kept
           else .scan pivot tail (candidate :: inc) kept)
          after

No control-valued callback, assumed future comparison, source law or resource packet is a theorem parameter. The displayed branch expression must remain in the public type or use only a separately reviewed public definition; no private helper may leak into it.
The actual call observation will later come from H15 when proving cluster_complete. The first slice itself does not prove any scan completes from genuine input assumptions.
Target 120–180 rendered source lines; HARD STOP220 before further source or any compiler run, if implementation is later authorized. The proof module keeps default limits.
The definitions remain noncomputable because they invoke H7.step. No runtime execution, compilation or Haskell refinement is claimed by this plan.
