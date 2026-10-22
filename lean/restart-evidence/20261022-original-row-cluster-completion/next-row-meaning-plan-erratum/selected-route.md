# Proof route for later source authorization
1. Case analysis on the actual parent and literal row membership eliminates empty, reference, union and Mu parent cases. The surviving case is an ordinary node with the same stored edge list; its actual complete codec is then definitional.
2. Extract the OriginalInput witness and its complete codec. Apply public payload_readback to the witness and to the actual node with that node codec at the same input; equate the two records and transport Original to the actual parent (S03, S04).
3. Each row child is Original by the actual parent Original.node constructor and available by Available.children at the corresponding flatMap membership (S04, S05).
4. model.row_valid at the admitted actual parent uses rows_readback to select the literal row and the inputOf child map membership to prove child admission (S02, S08, S12).
5. Use coherent node_free and the actual parent closedness to get childFree(all row children) = []. childFree_member then excludes every Reference from each selected child.free, so each child.free = [] (S06, S07).
6. closed_readback at each Original available child derives semantic-view closedness. Original.codec gives the exact inputOf child codec (S04).
7. For each child and each ambient environment, original_meaning maps physical meaning to the copied lexical shape. copy_readback identifies that shape with the fixed view copy (S04, S09).
8. model.copy_exact at that same admitted closed child identifies the copied lexical meaning with inputLanguage inputModel.languages (inputOf child). The environment is internedEnv ambient (S02, S09).
9. Transport the pointwise child language equality through the ordered All₂ relation in both directions using the existing scoped membership lemma; no new generic relation framework is needed (S11).
10. Combine RowLanguage, forest_all and edgeMeaning_all to obtain the exact row-language equality. The symbol and guard remain unchanged (S01, S10).
Allowed private helper: at most original_of_readback, if the two-readback equality step needs factoring. If generic over Value, it must take the actual complete-codec equality as well as source facts, availability and OriginalInput. Derive that equality in the ordinary-node case; do not add a public premise.
No private helper is mandatory. Keep child admission, closedness and meaning as local facts in the public proof if that is shorter. Do not add another public declaration or predicate.
No implementation, body, exact Lean header, compiler activation or H17 acceptance follows from this plan.
