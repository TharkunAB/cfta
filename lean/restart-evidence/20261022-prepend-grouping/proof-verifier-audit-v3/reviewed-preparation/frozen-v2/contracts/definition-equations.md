# Proposed definition equations
These equations are declaration contracts only. No definition body is authorized or supplied.
1. `insertWith table entry query = if query = entry.1 then some (entry.2 ++ (table query).getD []) else table query`.
2. `fromRows key rows = rows.foldl (fun table row => insertWith table (key row, [row])) (fun _ => none)`.
3. `reverseTable table query = (table query).map List.reverse`.
The first equation uses the literal new-list-before-old-list combination. The reverse equation keeps `none` distinct from `some []`.
In particular, `reverseTable table query = none ↔ table query = none`, and `reverseTable table query = some bucket ↔ table query = some bucket.reverse` are consequences of equation3 and List.reverse_reverse. They are not additional proposed public declarations.
The one-step conjugacy is only for a singleton new list. General list insertion needs its new list reversed and is outside the selected API.
