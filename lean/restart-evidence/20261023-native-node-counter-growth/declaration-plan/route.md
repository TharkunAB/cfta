The step bound follows the ten literal Code instructions in the current Native.step.
Pure, fail, enter, read and both finish instructions have unchanged physical node counters.
Work uses public Reservations.run_next and Nat.le_add_right, with no heap validity premise.
The optional binder first derives local growth from H34 maybeMu_mono at the same actual heap.
The constructed equation then specializes that bound in both done and pending cases.
Pending construction may allocate before it blocks. Its actual after heap must be retained.
Public node_step_machine and edge_step_machine give whole immediate machine equality for all memo observations.
Their public equality can rewrite the projected counter directly; no new lambda or lookup/demand equation is needed.
Execute uses fuel induction with code and state generalized. The zero case has the same input state.
The successor case derives local first from step_mono before the observed outcome split.
Only the yielded branch uses ih next after, on the predecessor fuel and the actual returned code/state.
Use Nat.le_trans to compose first with that exact IH result. Terminal branches retain first.
Resume dispatches on its supplied outcome. Yielded uses the earlier execute_mono; the other tags retain state.
No private helper, new definition, predicate, callback, successful-run premise or replacement state is planned.
All three public headers carry both equality instances explicitly. There is no global instance or omit directive.
The two have fragments attach literal := by with a newline after their exact type text.
The complete generated IH is review-only type metadata with one restricted call site; it is not an extra premise.
Use fully qualified Native.step, Native.execute and Outcome projection definitions in simplifier lists.
The conclusion is operational input-to-output node-counter growth only, for all four native outcome tags.
Fixed source-to-input order, resources, upper bounds, allocation Trace, Scan/H23 and full pass remain separate.
Root and an independent reviewer must accept the exact declarations before Root authors any body.
