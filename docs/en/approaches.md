> **Unfinished research draft. The arguments remain subject to review; no solution of the conjecture is claimed. The manuscript needs refinement and correctness still requires Lean formalization and verification. No Lean verification has been completed. See [current status](../../STATUS.md).**

# Approaches and their relationships

Source: the October 25 T002 assessment and the user's request to preserve the approaches and continue. Earlier topic records and experiments remain historical evidence.

| ID | Method | Main obligation or risk | Status |
| --- | --- | --- | --- |
| I001 | Indecomposable blocks and Burnside | Prove exhaustive block classification, unique decomposition and symmetry action; then count ordinary and twisted palindromes | Complete derivation in A001; cross-checked by A002; external review pending |
| I002 | Half-rectangle profile matrix and Burnside | Retain midline-crossing dominoes and prove the state-path and completion bijections | Complete in A002, including odd-height and five-row results |
| I003 | Perfect matchings on a symmetry quotient | Correctly handle fixed edges, axis crossings, weights and boundary conditions | Reserve route; no quotient-graph model constructed |
| I004 | Recurrences for fixed tilings | Classify midline configurations by parity and close a finite auxiliary system | Implemented within A002 by the two-dimensional recurrence; no duplicate attempt created |

## I001

The early conditional scheme assumed that the blocks were C,A_k,B_k and that each was vertically reflection-invariant. A001 proves this from the complete column transition table. First returns to the empty state are either the width-two all-horizontal block or one of two alternating-state paths. Coordinate formulas prove vertical-axis reflection invariance and horizontal-axis interchange of A_k,B_k.

With $F=x+2x/(1-x)$,

$$D=\frac1{1-F},\qquad H=\frac1{1-x},\qquad
V=(1+F)D(x^2),\qquad R=(1+x)D(x^2).$$

The general derivation is complete; further sequence fitting is not needed.

## I002

A three-bit mask records rows crossed at a cut. A complete tiling starts at the empty state and returns after 2n columns. Symmetric counting scans only n columns but retains outgoing halves at the midline. Half-turn invariance further requires the outgoing row set to be invariant under row reversal. Treating that half as an ordinary closed rectangle would lose valid tilings.

A002 proves the local rule for general height, supplies inverse completion maps, and reduces height three to a two-dimensional recurrence. It does not assume A001's fixed-point formulas. The same construction supplies the general odd-height theorem and the explicit six-dimensional five-row certificate.

## Other usable ideas and sources

Cells as vertices and shared edges as adjacency turn tilings into perfect matchings of $P_3\square P_{2n}$. Planar matching or determinant methods may help at other heights, but a naive symmetry quotient can omit constraints. This route is not currently preferred.

A direct classification by the geometry of the midline might shorten the proof. A001 can provide a comparison target, but an independent derivation must start from the geometry.

Mathar's block and matrix formulas are documented in [references](references.md). Online formalization definitions offer possible future assistance, but no Lean project was compiled or audited here.

## Priorities and branching

The two routes and an article are now written. Next: independent review or genuinely executed formal verification, and broader literature tracing for three-row and five-row symmetry classes. Even heights and square boards require a new attempt because the central-axis behaviour or group changes. Routine revisions stay within the existing attempt; a substantively different method receives a separate identifier.
