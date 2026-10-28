> **Historical research notes (October 25, 2026). Statements below about pending formalization describe that stage. The current English v2.1 paper and M1–M11 verification are linked from [STATUS](../../STATUS.md); external review and bibliographic priority remain unresolved.**

# Precise statement and scope

## Source

[OEIS A232622](https://oeis.org/A232622), *Number of incongruent domino tilings of the 3 X (2n) board*, points to Richard J. Mathar, [arXiv:1311.6135](https://arxiv.org/pdf/1311.6135), Table 10, Conjecture 6, equation (26). The OEIS recurrence is attributed to a conjecture by Jean-François Alcover dated January 21, 2019.

The sources were checked on October 25, 2026 (Beijing time). OEIS retained the conjecture labels. No complete pre-existing proof was obtained in the searches recorded here, but the search was not exhaustive. Global open status and novelty are therefore not established; see [references](references.md).

## Original proposition

For each integer n >= 1, tile a 3 by 2n unit-cell rectangle completely with unlabelled dominoes, allowing both orientations. Dominoes do not overlap and leave no gaps. There is no tatami condition. Tilings related by a reflection or rotation preserving the rectangle are equivalent. Let a(n) count the equivalence classes, and put a(0)=1 for the empty tiling.

The target identity is

$$\sum_{n\ge0}a(n)x^n=
\frac{-1+3x+4x^2-10x^3+4x^5-x^6}
{(x-1)(x^2-4x+1)(x^4-4x^2+1)}.$$

Equivalently, for n >= 7,

$$a(n)=5a(n-1)-a(n-2)-19a(n-3)+19a(n-4)+a(n-5)-5a(n-6)+a(n-7),$$

with a(0),...,a(6) = 1,2,5,14,46,156,561. Equivalence follows by coefficient comparison, since the numerator has degree six and the denominator degree seven.

## Definitions

| Symbol | Meaning |
| --- | --- |
| (r,c) | Rows r=1,2,3 from top to bottom; columns c=1,...,2n from left to right |
| Tiling | A set of unordered adjacent cell pairs, not labelled or directed dominoes |
| h | Horizontal-axis reflection: (r,c) maps to (4-r,c) |
| v | Vertical-axis reflection: (r,c) maps to (r,2n+1-c) |
| rho=hv | Half-turn |
| G | {e,h,v,rho}, a Klein four-group; these nonempty rectangles are never square |
| d_n,h_n,v_n,r_n | Fixed-point counts for e,h,v,rho |
| D,H,V,R | Their ordinary generating functions in half-width |
| Fault | An internal vertical grid line crossed by no horizontal domino |
| Indecomposable block | A nonempty complete three-row tiling with no internal fault |
| C,A_k,B_k | The blocks classified in A001; widths 2,2k,2k |
| F | Block generating function; called B in the early topic record, renamed to avoid confusion with B_k |

All generating functions belong to the formal power-series ring Q[[x]]. The empty object is represented by the empty word and contributes 1 to each fixed-point count. For n=1, the fixed-point counts are (3,1,3,1) and the orbit count is 2. Faithfulness of the group action is not required for Burnside's lemma.

## Current scope and revisions

The original goal concerns all n >= 0, not a finite prefix or a restricted tiling class. The two routes now give full derivations, with local cross-checks; external review remains outstanding.

On October 25 the original problem was carried over from T002 without adding a tatami or cuttability assumption. The later extension studies exact stabilizers and asymptotics, and then m by 2n rectangles for every fixed positive odd m. The full group remains the four-element rectangle group; square-board eight-element symmetry cannot be silently substituted. The definitions of the extension are in A002.
