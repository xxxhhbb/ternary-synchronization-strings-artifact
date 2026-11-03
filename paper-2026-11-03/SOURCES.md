# Published inputs and exact data correspondence

The codewords remain attributed to their original authors. This repository
identifies the concrete data and supplementary checks used by the paper;
it does not replace the cited mathematical preservation results.

| Paper input | Primary version and location | Required statement / quantifiers | Data and additional checks |
| --- | --- | --- | --- |
| Transparent length-18 source | Ekhad--Zeilberger, JIS 1 (1998), Article 98.1.9, with the author correction of 12 June 2001; also the exact six-word example following Definition 1 in SDL16, PDF p. 2 | Every square-free outer word of every length; each occurrence independently chooses one of its letter's two blocks; every resulting concatenation is square-free, including across boundaries | `codebooks/brinkhuis_18_2.json`; exact equality with the SDL16 displayed example; finite local and recognition tests in `computational/base/verifiers/verify_transparent_brinkhuis.py` |
| Quantitative length-54 source | Sollami, Douglas and Liebmann, JIS 19 (2016), Article 16.6.7, Definition 1, Theorem 4 and displayed base-word list | The published special 54-Brinkhuis 952-triple and its occurrence-wise arbitrary-length preservation property; repeated occurrences are not forced to share a choice | `codebooks/brinkhuis_54_952_C0.txt`, C1, C2; 476 published base words plus reversals, then cyclic alphabet permutations; recognition, overlap, suffix-fiber, flank-capacity and arithmetic checks in `computational/` |
| Extremal square-free application | Mol and Rampersad, Contributions to Discrete Mathematics 16(1) (2021), 8-19, Section 3, Lemma 3.2 and Corollary 3.3 | For every square-free walk of length at least two in the specified twelve-vertex digraph, every occurrence-wise Q/R choice with the prescribed endpoint caps is extremal square-free | `codebooks/extremal_41_52_images.json` gives P,Q,R,S and all twelve variants; 41/52 are image lengths, caps have length 49; graph and allowed-walk theorem remain published inputs |

For the 54 family, C0 is the sorted 952-word set in the source theorem. C1
and C2 are obtained by adding 1 and 2 modulo 3 to each symbol. The original
canonical input in `computational/base/inputs/` is unchanged. Reversal is
applied to word order, not to alphabet names.

For the extremal source, a vertex is named by its alphabet permutation and
whether its image is reversed. Unreversed vertices use permuted P on the
left and S on the right. Reversed vertices use reversed-permuted S on the
left and P on the right, as in the published definition of delta. The JSON
does not turn arbitrary vertex sequences into allowed walks.

## Primary sources

* Ekhad--Zeilberger original: https://cs.uwaterloo.ca/journals/JIS/zeil.html
* Published correction: https://cs.uwaterloo.ca/journals/JIS/zeile.html
* Sollami--Douglas--Liebmann article:
  https://cs.uwaterloo.ca/journals/JIS/VOL19/Sollami/sollami3.pdf
* Mol--Rampersad published article:
  https://cdm.ucalgary.ca/article/download/69831/54760/215200

The fresh primary-data comparison recorded in `codebooks/published_identity.json`
extracts the 476 length-54 words from the SDL16 article, adjoins their reversals,
and compares sets exactly against the computational input. It also compares
the six length-18 words with that article's displayed example and the P/Q/R/S
base words with the Mol--Rampersad published article. Hashes identify the
public PDFs used for these data checks. A source PDF may be obtained by a
reader from its publisher; the articles themselves are not redistributed.

## Preservation versus finite checks

An enumeration over short outer words is only that finite check. It does not
by itself establish arbitrary-length preservation. Likewise, complete-block
recognition, capacities and local-lemma arithmetic do not by themselves prove
the manuscript's analytic reductions. The source theorems, analytic arguments
and finite verification modules have separate roles.

## Lean correspondence

See `lean/README.md` and `lean/CheckScope.lean` for exact signatures,
parameters, hypotheses and axiom dependencies. Historical formal results
and current conditional endgame lemmas are distinguished explicitly.
No formalization of the complete 1/216 quantitative theorem, all applications
or the current Monte Carlo theorem is asserted.
