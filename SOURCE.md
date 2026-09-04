# Source of the 54/952 codebook

The canonical input in `inputs/codewords_54_952.txt` comes from Theorem 4 of:

Michael Sollami, Craig C. Douglas, and Manfred Liebmann, "An Improved Lower
Bound on the Number of Ternary Squarefree Words," *Journal of Integer
Sequences* 19 (2016), Article 16.6.7.

Paper: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Sollami/sollami3.pdf>

The theorem displays 476 length-54 words and specifies that the remaining 476
are their reversals.  The distributed input adjoins those reversals, requires
952 distinct words, and sorts the result.

All verifiers consume this canonical plain-text file.  They check its format,
cardinality, reversal closure, and every finite codebook statistic used by the
paper.  The occurrence-wise square-free theorem itself remains an external
published mathematical input.
