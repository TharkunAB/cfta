[2026-11-14 17:11 CET]

UNCOMPILED proof-only repair of the exact first strict-check input.

Added the direct SourceRecursiveIntersectionDomainEquivalence import. It
defines SourceRecursiveIntersectionSchedule.entered_key, which was not in
the original import closure. Replaced exactly two deprecated if_pos uses
with ite_eq_left and two deprecated if_neg uses with ite_eq_right.
All three theorem headers are byte-identical. No other proof line changed.
The original/coupled full headers are exact copies and remain OPEN.

The failed instrumented check source was verified to start with the exact
frozen a17c candidate. Its log and original packet were not changed.
The actual reset equation and lower-fuel auxiliary step retain the exact
Empty/zero/reset behavior; the A hypothesis is still emptyDomain-only.
The dependent source M composition remains in a separate new directory.

No compilation, live write, Git write, board post, heavy job, or child ran.
