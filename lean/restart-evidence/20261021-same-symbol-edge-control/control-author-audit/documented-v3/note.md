SOURCE-ONLY v3. Add documentation for public types, fields, constructors and operations.
All non-comment tokens, the first10 context lines and the exact public header remain unchanged.
No Lean job has run. Whole root and independent review must precede an ordinary check.
The earlier inline preparation stopped before writing a candidate: its raw header substring check included a final newline before the inline proof separator.
This preparation extracts the header at the actual proof separator. It does not weaken the required header byte comparison.
