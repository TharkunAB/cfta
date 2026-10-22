# Additive V2 review status correction
Status: HOLD. The selected V2 verifier needs a reader-path repair before activation.
Root found the retained archived-reader path at line257. I missed it in the initial review.
That assertion names full-preparation/check-full-public.py, which refers to the old reader.
The selected metadata interface uses the new reader125. Both archived V2 and active V2 reader bytes must be pinned.
The earlier frozen CLEAR record remains historical. This erratum supersedes its activation status.
Root requested a separate V3. No prepared verifier or reader ran during this review.
