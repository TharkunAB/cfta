# Pre-review proof-route order correction
Cut: 2026-10-22T07:05:14+02:00. The original frozen plan remains byte-identical.
inputOf uses getD .empty, so OriginalInput(source, inputOf value) alone does not establish the actual value codec.
First use literal row membership to select the ordinary-node case. Its complete codec then follows definitionally; only then use both payload readbacks.
If the optional helper is generic over Value, give it that actual complete-codec equality, exactly as the existing H11 private helper does. This fact is derived locally; no public premise is added.
The public prose contract, concrete Symbol/Guard scope, source budget and theorem claim are unchanged. The selected route differs only in these two logical staging details.
This is a static planning correction before an exact Lean header or body exists. No proof job, prepared tool or repository write occurred.
