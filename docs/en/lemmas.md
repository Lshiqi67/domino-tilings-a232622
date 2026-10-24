> **Unfinished research draft. The arguments remain subject to review; no solution of the conjecture is claimed. The manuscript needs refinement and correctness still requires Lean formalization and verification. No Lean verification has been completed. See [current status](../../STATUS.md).**

# Shared lemmas and dependency register

Version: October 25, 2026, English edition of the v2 register. A001 proves L001–L006. A002 proves L007–L011 without assuming the block classification. Local method cross-checks and explicitly bounded computations have been performed; registration does not amount to independent certification.

| ID | Statement | Dependencies |
| --- | --- | --- |
| L001 | Complete column-state/path bijection | Adjacent-cell covering definition |
| L002 | Blocks are exactly C,A_k,B_k | L001 |
| L003 | Unique decomposition into a block word | Fault definition and L002 |
| L004 | Symmetry is letter involution, reversal, or their composite | L002–L003 |
| L005 | Four fixed-point generating functions | L003–L004 |
| L006 | Burnside average | Finite action and orbit–stabilizer formula |
| L007 | Half-rectangle bijections for vertical reflection and half-turn | General local covering rule |
| L008 | Odd-height horizontal-reflection count | Exclusion of middle-row overlapping images |
| L009 | Three-row parity formulas | L007–L008 and the two-dimensional recurrence |
| L010 | Exact three-row stabilizer classes | L008 and group operations |
| L011 | Odd-height matrix formula and rationality | L007–L008 and L006 |

## L001: state paths

For every integer w >= 0, three-row tilings of width w correspond bijectively to legal paths of length w from the empty row subset to itself. A transition p to q is legal exactly when p and q are disjoint and the remaining rows are empty, {1,2}, or {2,3}. Each legal column filling is unique. The empty path gives the empty tiling. See the complete table and inverse construction in [A001](blocks-proof.md).

## L002: block classification

A block is a nonempty complete three-row tiling with no internal uncrossed vertical grid line. The blocks are C (three horizontal dominoes in width two) and A_k,B_k for k >= 1. A_k has vertical dominoes in the first and last columns covering rows 1,2; row 3 is tiled on pairs (2j-1,2j), and the interiors of rows 1,2 on pairs (2j,2j+1). B_k is its horizontal-axis reflection. First-return paths prove exhaustiveness and distinctness; no ordinary counting formula is assumed.

## L003: unique decomposition

For every n >= 0, complete 3 by 2n tilings correspond to words of total weight n over C,A_k,B_k, where C has weight 1 and A_k,B_k have weight k. Cut at every fault; concatenation is inverse. The empty word represents the empty tiling.

## L004: the action on words

Let sigma fix C and exchange A_k,B_k. Then h acts letterwise by sigma, v reverses the word, and rho reverses and applies sigma. Every block is itself invariant under v, and reflection preserves faults. The coordinate argument applies to words with unequal block widths.

## L005: fixed-point series

With half-width variable x and $F=x+2x/(1-x)$,

$$D=\frac{1-x}{1-4x+x^2},\quad H=\frac1{1-x},\quad
V=(1+F)D(x^2),\quad R=(1+x)D(x^2).$$

The four classes are arbitrary words, words in C alone, palindromes, and words invariant under reversal combined with sigma. A central block may cross the geometric midline.

## L006: orbit average

For every n >= 0, $a(n)=(d_n+h_n+v_n+r_n)/4$. Each finite orbit contributes four to the sum of stabilizer sizes. Faithfulness is unnecessary, including the empty case.

## L007: half-rectangle completion

For any positive height m, let q_n(S) count partial m by n left halves with precisely the last-column rows S reserved as outgoing half-dominoes. At n=0 only the empty state has count one. Then

$$v_{m,n}=\sum_Sq_n(S),\qquad
r_{m,n}=\sum_{J(S)=S}q_n(S),$$

where J reverses row order. Reflect or rotate the internal left-hand dominoes and insert horizontal midline dominoes. Rotation requires and suffices for equality of the two unmatched row sets. Restriction gives the inverse.

These are fixed-point formulas for the named symmetries at any height. Even when the board is square they do not justify replacing its full group by the four-element subgroup.

## L008: odd-height horizontal reflection

For m=2k+1 and n >= 0, $h_{m,n}=t_k(2n)$, with $t_0(w)=1$. A vertical domino incident with the middle row would overlap its distinct reflected image. Hence the middle row is tiled horizontally in the unique way; an arbitrary complete top k-row tiling determines its reflected bottom half.

## L009: parity formulas

Let $d_0=1,d_1=3,d_j=4d_{j-1}-d_{j-2}$. For j >= 0,

$$r_{2j}=r_{2j+1}=d_j,\quad
v_{2j}=d_{j+1}-2d_j,\quad v_{2j+1}=d_{j+1},$$
$$a(2j)=\frac{d_{2j}+1+d_{j+1}-d_j}{4},\quad
a(2j+1)=\frac{d_{2j+1}+1+d_{j+1}+d_j}{4}.$$

The two-step matrix is $\left(\begin{smallmatrix}3&2\\1&1\end{smallmatrix}\right)$. L007 supplies the terminal-state sums. A002 does not use A001's blocks or the conjectured seventh-order recurrence.

## L010: exact stabilizers

For height three the numbers of orbits with stabilizers G, {e,h}, {e,v}, {e,rho}, {e} are respectively

$$1,\quad 0,\quad (v_n-1)/2,\quad (r_n-1)/2,\quad
(d_n-v_n-r_n+1)/4.$$

The unique h-fixed tiling has all symmetries, and every intersection of two nonidentity fixed sets is that singleton. Commutativity makes stabilizers constant on an orbit.

## L011: odd-height matrix formula

For m=2k+1 >= 1 and n >= 0, with T_m as in A002 and chi_m the indicator of row-reversal-fixed states,

$$a_m(n)=\tfrac14[
e_0^{\mathsf T}T_m^{2n}e_0+
e_0^{\mathsf T}T_k^{2n}e_0+
e_0^{\mathsf T}T_m^n(\boldsymbol1+\chi_m)].$$

For fixed m the generating function is rational. Height one and the empty object are included; every nonempty board here is nonsquare. The five-row specialization is R002.

## Actual verification and limits

The same assistant checked dependencies and boundary conditions on October 25 and identified no circular use or unresolved premise. A001 checked all 40,545 tilings for n=0,...,8, their decomposition and all symmetry actions. A002 subsequently reconstructed the local bijection independently of blocks and checked 57,468 tilings at heights 1,3,5,7 over the specified ranges, including terminal masks and stabilizer types. Exact matrix and six-dimensional polynomial certificates were also checked.

The general statements rely on the written proofs, not extrapolation from these finite ranges. Independent external review and formal verification remain outstanding. See the English proof and check records in the respective attempts.
