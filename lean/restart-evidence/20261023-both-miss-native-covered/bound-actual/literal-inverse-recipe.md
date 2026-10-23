# Exact literal reconstruction and inverse
For each of the nine files, read predecessors/<name> and binding-values.json values in their recorded order.
For a token ending _JSON__, replace its whole single- or double-quoted literal with repr(json.dumps(value, ensure_ascii=False)).
For every other token, replace the literal token with str(value). Keep the enclosing expression unchanged.
The result must equal <name> byte-for-byte and match selected-scripts.json. No H26 token may remain in a selected script.
The inverse is recorded in inverse-diffs/<name>.patch. It is the exact unified diff from selected bytes to the complete retained predecessor.
The forward diff is in diffs/<name>.patch. Both diff directions reconstruct from the retained complete before/after files.
The verifier predecessor is the accepted314-line declaration overlay, not the274-line unresolved STOP version.
No program in this package was imported or executed. Actual proof commit binding remains outside these tools.
