The existing H17 module has 345 ordinary source lines. Its two private declarations and local strong-induction statement already count.
The candidate context sketch has 18 lines and the public signature sketch has 57; the latter adds only parent admission and five language lines to H17's public shape.
Estimated additions: 12–18 declaration/local-statement lines, 6–12 actual H19-call lines, 30–50 branch union reasoning lines, and 12–24 base/composition lines plus ordinary formatting.
Recommend 410–480 total ordinary lines, with hard500 only after explicit root review. These values are proposals, not current implementation authorization.
If a body cannot fit the approved total, preserve the stopped draft and request a concrete scope decision before adding helpers or splitting. Do not compress or export a framework to evade the stop.
Keep default declaration limits and all linters. No checker, compiler or proof body belongs to this package.
