# Covered cases

- Decision `none`, `some done`, and `some stuck` at every fuel.
- Exhausted expansion at zero fuel.
- Each pair of existing prefix constructors, with impossible pairs excluded by erased prefix equality.
- Parked candidates `none` and `some`; absent raw result; empty rows; singleton error or success; multiple rows.
- Every Right action shape, including the early empty action.
- Absent Right result; empty rows; singleton error or success; multiple rows.
- Both callback Booleans, both candidate shapes, and both ordinary-result shapes.
- Every actual preparation entry/failure state and optional fold through checked CPS transport.
- Both complete and stopped fold constructors through checked finish transport.

No case discards a duplicate row or output. Unsupported rows retain their erased failure observation.
