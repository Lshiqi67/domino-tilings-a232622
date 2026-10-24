> **Unfinished research draft. The arguments remain subject to review; no solution of the conjecture is claimed. The manuscript needs refinement and correctness still requires Lean formalization and verification. No Lean verification has been completed. See [current status](../../STATUS.md).**

# References, checked content, and unresolved priority

All dates below are Beijing dates. The records originate from the October 24–25, 2026 topic screening and subsequent research. “Checked” refers only to the specified content, not to a claim that an entire work was audited.

| ID | Source | Checked content and limits | Date |
| --- | --- | --- | --- |
| REF001 | [OEIS A232622](https://oeis.org/A232622) | Problem, generating function, recurrence and initial values; conjecture labels remained | 2026-10-25 |
| REF002 | R. J. Mathar, *Paving rectangular regions with rectangular tiles: tatami and non-tatami tilings*, [arXiv:1311.6135](https://arxiv.org/pdf/1311.6135), 2013 | Definitions, Table 10, Conjecture 6, equation (26); later Table 12. Variable marks full width | 2026-10-25 |
| REF003 | R. J. Mathar, *Tilings of rectangular regions by rectangular tiles: Counts derived from transfer matrices*, [arXiv:1406.7788](https://arxiv.org/pdf/1406.7788), 2014 | Sections 2.1–2.3, equations (4)–(6): ordinary tilings, indecomposable blocks and transfer matrices. Variable there marks dominoes | 2026-10-25 |
| REF004 | R. P. Stanley, *Topics in Algebraic Combinatorics*, [author's lecture notes](https://math.mit.edu/~rstan/algcomb/algcomb.pdf), February 1, 2013 version | Chapter 7, Lemma 7.2, Burnside's lemma and its proof | 2026-10-25 |
| REF005 | D. Klarner and J. Pollack, *Domino tilings of rectangles with fixed width*, Discrete Mathematics 32 (1980), 45–52, [publisher DOI](https://doi.org/10.1016/0012-365X(80)90098-9) | Publisher indexing/abstract only: rationality and linear recurrences for ordinary fixed-width counts; full text returned 403, no theorem number verified | 2026-10-25 |
| REF006 | [OEIS A001835](https://oeis.org/A001835) | Ordinary three-row counts and references; our d_n is A001835(n+1), so offsets differ | 2026-10-25 |
| REF007 | M. Hujter and A. Kaszanyitzky, *Symmetries related to domino tilings on a chessboard*, [arXiv:1603.03298](https://arxiv.org/pdf/1603.03298), 2016 | Material inspected concerned Hamiltonian paths and a six-row ordinary recurrence; no direct proof of the present orbit formula obtained | 2026-10-25 |
| REF008 | [AlgebraicCombinatorics.Details.DominoTilings documentation](https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/Details/DominoTilings.html) | Three-row blocks and reflection definitions seen; project not compiled or dependency-audited, so not a verified formal certificate | 2026-10-25 |

## Variables and reusable ingredients

REF002 equation (26) is

$$\overline T(z,3)=\frac18\left(\frac1{1+z}+\frac1{1-z}\right)
+\frac{1+2z^2-z^6}{2(1-4z^4+z^8)}
+\frac{1-z^2}{4(1-4z^2+z^4)}.$$

The correct comparison is $\overline T(z,3)=A(z^2)$. A001's exact algebra check verified this identity. One must not identify the full-width variable z with the half-width variable x.

REF003 uses a domino-count variable in the three-row formulas. A 3 by 2n board contains 3n dominoes, so substituting z³=x gives

$$D(x)=\frac{1-x}{1-4x+x^2},\qquad
F(x)=3x+\frac{2x^2}{1-x},\qquad D=\frac1{1-F}.$$

REF003 retains orientation-distinguished tilings; it supplies ingredients, not the quotient count by itself. A001 derives these formulas afresh from local rules and then adds the symmetry analysis.

## Priority and open status

An OEIS conjecture label is a verified fact about the inspected page, not proof that no prior solution exists. Searches included A232622 proof, Mathar with Conjecture 6, and combinations of three-row tilings, Burnside and reflections. Citation tracing was incomplete. No first-proof claim is justified.

The local derivations were recorded as research drafts. No message was sent to OEIS, Mathar, or another person, and no publication was made. If an equivalent earlier proof is found, the appropriate description may be reproduction, exposition or an alternative proof.

The next literature step is to trace references and citing works for reflection/rotation classes, fault-free domino tilings and palindromic compositions, including results for general rectangles whose three-row specialization may imply the target formula.

## Later five-row comparison

REF002 Table 12 (PDF page 10) gives five-row orbit counts 5,33,329,3818,46878 for widths 2,4,6,8,10. A002 independently derives the same values. The table was used after the derivation, not in fitting a recurrence.

Further searches combining domino, incongruent, five rows, Mathar, Burnside, rectangle and reflection did not yield a directly checkable pre-existing proof. This remains a limited search and does not establish novelty of the odd-height theorem or the five-row expression.

## Dedicated public-status recheck, October 25

The user separately asked whether the problem had already been solved publicly. The object rechecked was the unrestricted A232622 count, not the tatami subclass.

- OEIS still labelled the generating function and Alcover's January 21, 2019 recurrence as conjectures. The site's global footer modification date is not an entry-specific modification date.
- Mathar's PDF page 9 still presents the target as Conjecture 6, equation (26). The adjacent Theorem 10, equation (25), concerns the subscript-zero tatami class and cannot be cited as a proof of the unrestricted total.
- The 2014 transfer paper and online formalization documentation were reopened. No compiled formal theorem establishing the target orbit generating function was obtained.
- Additional searches used the exact sequence and arXiv identifiers and the terms three, 3 by 2n, incongruent, inequivalent, Burnside and reflection. A result titled *Intersecting Domino Tilings* concerned an extremal pairwise-intersection question according to the [publisher abstract](https://www.tandfonline.com/doi/abs/10.1080/00150517.2010.12428111), not this counting conjecture.

Conclusion: no reliable evidence of a public complete solution was located in that search, but it was not established that the problem remains open throughout the literature. That status recheck did not rerun experiments, re-adjudicate the local proofs, or publish anything.

## Manuscript preparation checks

During Chinese-paper preparation, REF001–REF004 were reread at the cited locations. Only the four sources actually used in the paper's derivations were included in its bibliography. The two variable substitutions were kept explicit. The English edition retains these distinctions and dates; translation is not a new proof of priority.

## REF009: DeFord and general symmetry recurrences

Daryl DeFord, *Enumerating Distinct Chessboard Tilings*, Fibonacci Quarterly 52 (2014), no. 5, 102–116. [Journal PDF](https://www.fq.math.ca/Papers1/52-5/DeFord.pdf); [issue contents](https://www.fq.math.ca/52-5.html). The issue is dated December 2014; the linked manuscript bears April 20, 2015. Checked October 25, 2026 during the later review and again during English preparation.

Theorem 6.1 supplies a general recurrence framework for rectangle tilings modulo the four rectangle symmetries, with a two-row domino example in Section 6.2.1. General fixed-height rationality is therefore established background. The English article cites this source and concentrates on explicit boundary conditions and evaluations. No priority claim for the specific three-row proof, five-row expression or stabilizer refinements follows from the limited search.

The later review is preserved separately in checks/independent-review-2026-10-25. Its two wording/notation corrections and this citation have been incorporated in the English version.
