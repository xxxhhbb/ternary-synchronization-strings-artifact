# Supplementary Lean development

This is a source snapshot of the accompanying formal development. It is
supplementary to the mathematical proofs in the paper; it is not a
formalization of every result or every current parameter.

## Reproduction

Install Elan, then run from this directory:

```sh
lake exe cache get
lake build
lake env lean CheckScope.lean
```

Lake resolves dependencies from the committed manifest. The project pins
Lean `v4.32.2`, Mathlib `v4.32.2` and the exact dependency
commits in `lake-manifest.json`. Cache retrieval downloads public dependency
builds; the committed source contains no build cache.

## What is established, and what is a premise?

* `SynchronizationHeadline.lean` proves the earlier `5999/6000`
  synchronization conclusion for every requested length, with the existence
  of a ternary square-free outer stream supplied explicitly as a hypothesis
  (`ternary_synchronization_headline_of_thue`). It must not be cited as the
  current `2001/2002` theorem without qualification.
* `CurrentDeletionBallAnalytic.lean`, `CurrentIntervalEntropy.lean` and
  `CurrentNumerics.lean` specialize deletion-ball, conditional interval mass,
  and numerical local-lemma estimates to the current transparent constants.
* `CurrentSynchronizationLift.lean` proves the exact deterministic lift from
  equal adjacent intervals at deficit `1/1000` to the strict synchronization
  parameter `2001/2002`. Its headline theorem explicitly takes existence of
  the equal-block gap at every length as a premise. The file is not a
  stand-alone construction of those outputs.
* Other modules contain the finite-codeword, probability, witness-tree,
  counting and resampling developments imported by `FormalAudit.lean`.
  Their statements, including all parameters and hypotheses, define their
  scope. Earlier numerical specializations remain in the snapshot.
* This development does not formalize the `54/952` strengthening to gap
  `1/216`, all-length synchronization circles, the full extremal application,
  or the current near-linear Monte Carlo theorem. Those are proved in the
  manuscript, using the cited results and the separate finite verifiers.

`CheckScope.lean` prints the complete signatures and kernel axiom dependencies
of representative exported theorems. Explicit theorem hypotheses do not
appear in an axiom report; read the signatures as well. Mathlib's usual
foundational axioms and any compiler-backed finite decision dependencies
must not be confused with omitted theorem hypotheses.

Some finite proofs use `native_decide`. The historical headline and abundance
theorems report a compiler-backed native-decision dependency in addition to
the usual foundational axioms. The current interval-mass, numerical-closure
and conditional headline checks report only `propext`, `Classical.choice`
and `Quot.sound`. The generated native-decision dependency is not an
omitted premise; it identifies the compiler-backed trust used by those
finite computations.

The development is published so that readers can inspect and rebuild these
specific results. No claim of complete formal verification of the paper is
made.
