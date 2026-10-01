module

public import GradedNear

/-!
# The graded near lemma and the leaf-certificate checker (Palomar Solution)

The compared theorems (see `comparator.json`) are proved in the library:
* `GradedNear.graded_near_lemma`: `GradedNear/Statement.lean`, assembled in `GradedNear/Main.lean`;
* `GradedNear.response_lemma`: `GradedNear/Response.lean`;
* `GradedNear.graded_near_threshold`: `GradedNear/ZeroForm.lean`;
* `GradedNear.keptBound_single`, `GradedNear.keptBound_pair` and
  `GradedNear.single_zero_threshold`: `GradedNear/Entry.lean`;
* `GradedNear.Cert.near_row_of_bins`: `GradedNear/Cert/Bins.lean`;
* `GradedNear.Cert.checkLeaf_sound`, `GradedNear.Cert.checkLeaf_lt` and
  `GradedNear.Cert.certified`: `GradedNear/Cert/Sound.lean`, with the row relaxations in
  `GradedNear/Cert/Relax.lean`.
-/

@[expose] public section
