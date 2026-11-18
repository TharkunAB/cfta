Root-only sequence:

1. Review the frozen stage and both actual private receipts.
2. Copy and execute prepare-publication.py in Work58.
3. Review the new runtime inheritance selection and Source pins.
4. Run its check.py under the existing capped job runner.
5. Accept checked.json only after all five actual gates pass and pins stay exact.

Runtime: 20261118-source-worker-seeds-components-publication.
Strict order: SeedClosure, selected preparation, incoming resources, narrowing,
then dispatch resources. The full combined DAG has 2394 nodes. All five candidate
outputs are omitted from normal links. Seven fresh public axiom queries run once
against the freshly compiled namespace. A failed gate writes results.json and
receives no success receipt. The original private failures remain untouched.
