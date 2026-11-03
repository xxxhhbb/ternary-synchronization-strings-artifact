# The 54-uniform Brinkhuis family

The codewords in `inputs/codewords_54_952.txt` are taken from Theorem 4 of:

Michael Sollami, Craig C. Douglas, and Manfred Liebmann,
[An Improved Lower Bound on the Number of Ternary Squarefree Words](https://cs.uwaterloo.ca/journals/JIS/VOL19/Sollami/sollami3.pdf),
*Journal of Integer Sequences* 19 (2016), Article 16.6.7.

The theorem gives 476 words of length 54 together with their reversals.
Adjoining the reversals yields 952 distinct words. The input file lists these
words in lexicographic order, one per line.

The cited theorem supplies the occurrence-wise square-free property used in
the paper. The verification programs check the additional finite codeword
properties and inequalities required for the synchronization bounds.
