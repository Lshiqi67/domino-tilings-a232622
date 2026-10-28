> **Historical research notes (October 25, 2026). Statements below about pending formalization describe that stage. The current English v2.1 paper and M1–M11 verification are linked from [STATUS](../../STATUS.md); external review and bibliographic priority remain unresolved.**

# A002: Complete half-rectangle proof and extensions

English edited proof record, October 25, 2026. Definitions, arguments and formulas are reproduced from the English mathematical article. Statement and cross-reference numbers follow that article. The PDF and LaTeX source preserve the authoritative equation numbering and typography.

[English article](../../papers/en/README.md) · [Sources](references.md) · Attempt overview

The second proof reuses only the common-denominator simplification from [A001](blocks-proof.md), not its block classification or fixed-point derivation. References to that simplification refer to the accompanying A001 record.

## Introduction

Let $\mathcal T_n$ be the set of domino tilings of a $3\times 2n$
rectangle, where $n\ge1$. A domino covers two unit cells sharing an
edge. Both orientations are allowed, the dominoes are unlabelled,
and no tatami restriction is imposed. Thus a tiling is a set of
unordered pairs of adjacent cells.
Number rows from top to bottom and columns from left to right.
The maps

$$

 h(r,c)=(4-r,c),\qquad v(r,c)=(r,2n+1-c),\qquad \rho=hv

$$

are reflection in the horizontal axis, reflection in the vertical
axis, and rotation through $180^\circ$, respectively.
Since $3\ne2n$, the full symmetry group of the rectangle is
$G=\{e,h,v,\rho\}\cong C_2\times C_2$.
Write $a(n)=|\mathcal T_n/G|$. We set $\mathcal T_0$ to consist of a
single empty tiling, fixed by all four abstract group elements, so
that $a(0)=1$.

Mathar [Mathar (2013), Table 10, Conjecture 6] proposed a generating
function for these symmetry classes. The equivalent formula in
OEIS A232622 [OEIS A232622] is accompanied by a conjectured recurrence
of order seven. We give two derivations of the generating function.
The first uses a complete classification of vertically
indecomposable blocks and the action of $G$ on words in these blocks.
The second counts symmetric tilings directly from partial tilings
of a half-rectangle.
The latter construction also yields a uniform formula for any fixed
odd height.

Transfer matrices and indecomposable tilings are established tools
in fixed-width enumeration. In particular, Mathar
[Mathar (2014), Sections 2.1–2.3] gives the ordinary three-row
generating function and the corresponding indecomposable-block
generating function. We rederive the required block classification
and determine the symmetry action explicitly.
DeFord [DeFord, Enumerating distinct chessboard tilings, Theorem 6.1] establishes a general recurrence
framework for rectangular tilings counted up to symmetry and
illustrates it for two-row domino tilings in Section 6.2.1.
Thus rationality at fixed height is established background;
our odd-height formula specifies the boundary conditions and
gives an explicit five-row evaluation.
None of our
combinatorial arguments assumes the target recurrence or a finite
list of coefficients.
The source entry was checked on October 25, 2026; its conjecture
label does not establish that no equivalent proof appears elsewhere.
No claim of bibliographic priority is made here.

### Main result

Let

$$

 d_n=|\mathcal T_n|,\qquad h_n=|\operatorname{Fix}(h)|,\qquad
 v_n=|\operatorname{Fix}(v)|,\qquad r_n=|\operatorname{Fix}(\rho)|.

$$

Their ordinary generating functions, with $x$ marking the
half-width $n$, are denoted by $D,H,V,R$.
All generating-function identities are interpreted in
$\mathbb Q[[x]]$.

**Theorem 1.1.** 
The number of domino tilings of a $3\times2n$ rectangle up to
rectangle symmetries has generating function

$$

 A(x):=\sum_{n\ge0}a(n)x^n
 =\frac{1-3x-4x^2+10x^3-4x^5+x^6}
 {(1-x)(1-4x+x^2)(1-4x^2+x^4)}.

$$

Consequently,

$$

\begin{aligned}
a(n)={}&5a(n-1)-a(n-2)-19a(n-3)+19a(n-4)\\
       &+a(n-5)-5a(n-6)+a(n-7),\qquad n\ge7,
\end{aligned}

$$

with initial values

$$

 (a(0),\ldots,a(6))=(1,2,5,14,46,156,561).

$$

Multiplying the numerator and denominator in (1.1) by
$-1$ gives the form displayed in A232622.
Sections 2 and 3 give the two proofs.
Section 4 determines the exact stabilizers and the
asymptotic proportion of symmetric tilings.
Sections 5 and 6 treat arbitrary odd height
and the explicit five-row case.

**Lemma 1.2 (Burnside's formula).** 
For every $n\ge0$,

$$

 a(n)=\frac{d_n+h_n+v_n+r_n}{4}.

$$

**Proof.** 
Count the pairs $(g,T)\in G\times\mathcal T_n$ with $gT=T$:

$$

 \sum_{g\in G}|\operatorname{Fix}(g)|
 =\sum_{T\in\mathcal T_n}|\operatorname{Stab}(T)|.

$$

By the orbit–stabilizer formula, each orbit $O$ contributes
$|O|\cdot4/|O|=4$ to the right-hand side.
Division by four proves the assertion.
This is the usual orbit-counting lemma; see
[Stanley, Chapter 7, Chapter 7, Lemma 7.2].
The argument does not require a faithful action and includes $n=0$.

$\square$

## Half-rectangle bijections

We now derive the fixed-point counts without using the block
classification or the palindrome argument. The local construction
is stated for any positive height.

### Partial tilings and a transfer matrix

For $m,j\ge1$ and $S\subseteq[m]=\{1,\ldots,m\}$,
let $\mathcal P_m(j,S)$ be the set of partial tilings of an
$m\times j$ rectangle that cover every cell except the cells in
rows $S$ of the last column.
Each uncovered cell is regarded as the left half of a horizontal
domino to be completed in the next column.
For $j=0$, only the empty object with $S=\varnothing$ is allowed.
Write $q_j(S)=|\mathcal P_m(j,S)|$.

Index rows and columns of $T_m$ by all subsets of $[m]$, and set

$$

 T_m[p,q]=
 \begin{cases}
 1,&p\cap q=\varnothing\ \text{and every consecutive run}\\
   &\quad\text{in }[m]\setminus(p\cup q)\text{ has even length},\\
 0,&\text{otherwise}.
 \end{cases}

$$

An empty complement satisfies the condition.
The cells in $p$ complete the incoming horizontal dominoes;
those in $q$ remain as outgoing halves.
Each remaining consecutive run has a vertical tiling if and
only if its length is even, and then that tiling is unique.
This follows by pairing the endpoint with its only available
neighbour and proceeding along the run.
Consequently, legal state paths and partial tilings determine
one another uniquely.

Let $\mathbf e_0$ be the unit column vector at the empty state, and
let $t_m(j)$ count complete $m\times j$ tilings. Then

$$

 q_j^{\mathsf T}=\mathbf e_0^{\mathsf T}T_m^j,\qquad
 t_m(j)=\mathbf e_0^{\mathsf T}T_m^j\mathbf e_0.

$$

For an auxiliary height-zero term, set $T_0=(1)$ and $t_0(j)=1$.

### Boundary conditions imposed by symmetry

Define $J(S)=\{m+1-r:r\in S\}$.
Let $\mathbf 1$ be the all-ones column vector, and let
$\chi_m(S)=1$ if $J(S)=S$, and $0$ otherwise.
Denote the fixed-point counts of the two reflections and the
half-turn on an $m\times2n$ rectangle by $h_{m,n},v_{m,n},r_{m,n}$,
respectively.

**Lemma 3.1.** 
For every $m\ge1$ and $n\ge0$,

$$

 v_{m,n}=\mathbf e_0^{\mathsf T}T_m^n\mathbf 1,\qquad
 r_{m,n}=\mathbf e_0^{\mathsf T}T_m^n\chi_m.

$$

**Proof.** 
Suppose first that $n\ge1$. Given $P\in\mathcal P_m(n,S)$,
reflect its internal dominoes into the right half of the
rectangle, and insert a horizontal domino joining $(r,n)$
to $(r,n+1)$ for each $r\in S$.
The internal dominoes in the two halves are disjoint, and the
inserted dominoes cover precisely the remaining cells.
The resulting tiling is fixed by vertical-axis reflection.
Conversely, restrict any such fixed tiling to its left half
and cut its midline-crossing dominoes. This recovers $P,S$
uniquely, proving the first bijection and formula.

For the half-turn, rotate the internal dominoes of $P$ into
the right half. The unmatched rows on the right are $J(S)$.
A domino crossing the midline must join two cells in the same
row, so completion is possible if and only if $J(S)=S$.
When this condition holds, inserting one crossing domino in
each row of $S$ gives a half-turn-invariant tiling.
Restriction to the left half is again the inverse map.
Equivalently, necessity follows because the half-turn sends a
crossing domino in row $r$ to one in row $m+1-r$.
The empty-object convention gives both formulas for $n=0$.

$\square$

**Lemma 3.2.** 
If $m=2k+1$ with $k\ge0$, then

$$

 h_{m,n}=t_k(2n)\qquad(n\ge0).

$$

**Proof.** 
In a tiling fixed by horizontal-axis reflection, a vertical
domino incident with the middle row would have a distinct
reflected image sharing its middle-row cell. Such a domino
is impossible.
The middle row must therefore have its unique horizontal
tiling. The top $k$ rows form a complete tiling, and their
reflection determines the bottom $k$ rows.
Conversely, every tiling of the top subrectangle gives a fixed
tiling in this way. Restriction is the inverse.
The conventions cover $k=0$ and $n=0$.

$\square$

### A two-dimensional recurrence for height three

From (3.1), the states reachable from the empty state
at height three are

$$

\varnothing,\quad\{1\},\quad\{3\},\quad\{1,2\},\quad\{2,3\},\quad\{1,2,3\}.

$$

The empty state leads to $\{1\},\{3\},\{1,2,3\}$;
$\{1\}$ leads to $\varnothing,\{2,3\}$;
$\{3\}$ leads to $\varnothing,\{1,2\}$;
The remaining transitions are

$$

\{1,2\}\longrightarrow\{3\},\qquad
\{2,3\}\longrightarrow\{1\},\qquad
\{1,2,3\}\longrightarrow\varnothing.

$$

Starting from the empty profile, induction gives

$$

 q_{2j}(\varnothing)=\alpha_j,\qquad
 q_{2j}(\{1,2\})=q_{2j}(\{2,3\})=\beta_j,

$$

with all other counts zero. One further step gives

$$

 q_{2j+1}(\{1\})=q_{2j+1}(\{3\})=\alpha_j+\beta_j,\qquad
 q_{2j+1}(\{1,2,3\})=\alpha_j.

$$

Taking another step yields

$$

 \binom{\alpha_{j+1}}{\beta_{j+1}}
 =\begin{pmatrix}3&2\\1&1\end{pmatrix}
 \binom{\alpha_j}{\beta_j},\qquad
 (\alpha_0,\beta_0)=(1,0).

$$

The listed transitions also prove that these support patterns
are preserved at every step.

**Proposition 3.3.** 
The ordinary counts $d_j=t_3(2j)$ satisfy

$$

 d_0=1,\qquad d_1=3,\qquad
 d_{j+2}=4d_{j+1}-d_j\quad(j\ge0).

$$

For every $j\ge0$,

$$

\begin{gathered}
 h_n=1\quad(n\ge0),\qquad r_{2j}=r_{2j+1}=d_j,\\
 v_{2j}=d_{j+1}-2d_j,\qquad v_{2j+1}=d_{j+1}.
\end{gathered}

$$

In particular,

$$

\begin{aligned}
 a(2j)&=\frac{d_{2j}+1+d_{j+1}-d_j}{4},\\
 a(2j+1)&=\frac{d_{2j+1}+1+d_{j+1}+d_j}{4}.
\end{aligned}

$$

**Proof.** 
Equation (3.2) gives $d_j=\alpha_j$.
The matrix in (3.5) satisfies
$M^2-4M+I=0$, proving (3.6).
At an even step, the only reachable $J$-invariant state is
$\varnothing$; at an odd step it is $\{1,2,3\}$.
Lemma 3.1 therefore gives the two formulas for $r$.
Summing all terminal counts gives
$\alpha_j+2\beta_j=d_{j+1}-2d_j$ at an even step and
$3\alpha_j+2\beta_j=d_{j+1}$ at an odd step.
Lemma 3.2 gives $h_n=t_1(2n)=1$.
Substitution in Burnside's formula proves (3.8).

$\square$

**Second proof of Theorem 1.1.** 
The recurrence (3.6) gives
$D(x)=(1-x)/(1-4x+x^2)$.
Summing (3.7) over the two parities gives

$$

 H(x)=\frac1{1-x},\qquad R(x)=(1+x)D(x^2),

$$

and

$$

 V(x)=(1+x)\frac{D(x^2)-1}{x^2}-2D(x^2)
 =\frac{1+3x+x^2-x^3}{1-4x^2+x^4}.

$$

Division of $D(t)-1$ by $t$ is valid in the formal power-series
ring because its constant term vanishes.
Burnside's formula now gives (2.7);
the algebraic simplification and coefficient comparison in
the first proof finish the argument.
The combinatorial derivation here uses only the partial-tiling
model and the half-rectangle bijections.

$\square$

## Stabilizers and asymptotics

**Theorem 4.1.** 
For every $n\ge0$, the exact stabilizers of three-row tilings
are distributed as in Table 2.

| Stabilizer | Tilings | Orbit size | Orbits |
| –- | –- | –- | –- |
| $G$ | $1$ | $1$ | $1$ |
| $\{e,h\}$ | $0$ | $2$ | $0$ |
| $\{e,v\}$ | $v_n-1$ | $2$ | $(v_n-1)/2$ |
| $\{e,\rho\}$ | $r_n-1$ | $2$ | $(r_n-1)/2$ |
| $\{e\}$ | $d_n-v_n-r_n+1$ | $4$ | $(d_n-v_n-r_n+1)/4$ |

**Proof.** 
By Lemma 3.2, the only tiling fixed by $h$ is the
tiling in which each of the three rows is tiled horizontally.
It is also fixed by $v$ and $\rho$.
A tiling fixed by any two distinct nonidentity elements is
fixed by their product, and hence by all of $G$.
Thus every pairwise intersection, as well as the triple
intersection, of the three nonidentity fixed sets is this
single tiling.

There are consequently $v_n-1$ tilings with exact stabilizer
$\{e,v\}$, $r_n-1$ with exact stabilizer $\{e,\rho\}$, none with
exact stabilizer $\{e,h\}$, and $d_n-v_n-r_n+1$ with trivial
stabilizer. Since $G$ is abelian, the stabilizer is constant
on an orbit. Dividing by the corresponding orbit size gives
the table. These five subgroups exhaust all subgroups of $G$.

$\square$

For example, when $n=8$ the fixed-point counts are
$d_8=29681$, $v_8=265$, and $r_8=153$.
Among the $7525$ orbits, $7316$ have trivial stabilizer,
$132$ have stabilizer $\{e,v\}$, $76$ have stabilizer
$\{e,\rho\}$, and one has stabilizer $G$.

**Theorem 4.2.** 
Let $\lambda=2+\sqrt3$. If a tiling is chosen uniformly from
$\mathcal T_n$, let $p_n$ be the probability that it has a
nonidentity symmetry. Then, as $j\to\infty$,

$$

 p_{2j}\sim(\lambda-1)\lambda^{-j},\qquad
 p_{2j+1}\sim\frac{\lambda+1}{\lambda}\lambda^{-j}.

$$

In particular, $p_n=O(\lambda^{-n/2})\to0$, and

$$

 a(n)=\frac{d_n}{4}+O(\lambda^{n/2})
 \sim\frac{3+\sqrt3}{24}\lambda^n.

$$

**Proof.** 
Solving (3.6) with its initial values gives

$$

 d_n=c_+\lambda^n+c_-\lambda^{-n},\qquad
 c_\pm=\frac{3\pm\sqrt3}{6}.

$$

By Table 2,
$p_n=(v_n+r_n-1)/d_n$, whereas (3.7) gives

$$

 v_{2j}+r_{2j}=d_{j+1}-d_j,\qquad
 v_{2j+1}+r_{2j+1}=d_{j+1}+d_j.

$$

The leading terms of these numerators are
$c_+(\lambda-1)\lambda^j$ and $c_+(\lambda+1)\lambda^j$,
respectively. The corresponding denominators have leading
terms $c_+\lambda^{2j}$ and $c_+\lambda^{2j+1}$.
This proves (4.1). Finally,
$a(n)=(d_n+1+v_n+r_n)/4$ gives (4.2).

$\square$

Uniform sampling of orbits gives a different probability
space. The number of orbits with nontrivial stabilizer is
$(v_n+r_n)/2$, so their proportion is
$(v_n+r_n)/(2a(n))$, which also tends to zero.

## Rectangles of arbitrary odd height

Fix $m=2k+1\ge1$. Let $a_m(n)$ be the number of domino tilings
of an $m\times2n$ rectangle up to its full symmetry group,
with $a_m(0)=1$. A nonempty rectangle of odd height and even
width is never a square, so its symmetry group is still
$\{e,h,v,\rho\}$.
Use $T_m,\chi_m,\mathbf e_0$ as defined in Section 3.
The following is an explicit specialization of the general
recurrence framework discussed by DeFord [DeFord, Enumerating distinct chessboard tilings].
We include the proof to specify all symmetry boundary terms.

**Theorem 5.1.** 
For every $m=2k+1\ge1$ and $n\ge0$,

$$

 a_m(n)=\frac14\left[
 \mathbf e_0^{\mathsf T}T_m^{2n}\mathbf e_0+
 \mathbf e_0^{\mathsf T}T_k^{2n}\mathbf e_0+
 \mathbf e_0^{\mathsf T}T_m^n(\mathbf 1+\chi_m)\right].

$$

Equivalently,

$$

\begin{aligned}
 A_m(x):=\sum_{n\ge0}a_m(n)x^n
 =\frac14\bigl[&
 \mathbf e_0^{\mathsf T}(I-xT_m^2)^{-1}\mathbf e_0\\
 &+\mathbf e_0^{\mathsf T}(I-xT_k^2)^{-1}\mathbf e_0\\
 &+\mathbf e_0^{\mathsf T}(I-xT_m)^{-1}(\mathbf 1+\chi_m)\bigr].
\end{aligned}

$$

For each fixed odd height, $A_m(x)$ is rational, and its
coefficient sequence satisfies a constant-coefficient linear
recurrence.

**Proof.** 
The identity contribution is given by (3.2).
Lemma 3.2 gives the horizontal-axis reflection
contribution, and Lemma 3.1 gives the other two.
The same double count as in Lemma 1.2 proves
(5.1).
Summing over $n$ and using
$\sum_{n\ge0}x^nM^n=(I-xM)^{-1}$ proves (5.2).
Every matrix is finite, and $I-xM$ has constant term $I$.
Its inverse exists formally, and its entries are rational
by the adjugate formula.
Multiplying the resulting generating function by a denominator
with nonzero constant term and comparing sufficiently high
coefficients gives the asserted recurrence.

$\square$

The vectors $\mathbf e_0$ in the different summands belong to the
corresponding state spaces; when $k=0$, the convention
$T_0=(1)$ applies.
Lemma 3.1 itself holds for even heights as well.
However, (3.4) uses a middle row and cannot be
applied unchanged at even height.
That case requires a separate treatment of vertical dominoes
crossing the horizontal axis. For a square, quarter-turns and
diagonal reflections must also be included to count classes
under the full symmetry group.
Neither extension is asserted here.

## An explicit formula for height five

At height five the transfer calculation reduces to a
six-dimensional polynomial certificate.
We give the reduced matrix and boundary vectors explicitly;
Appendix A supplies the single-column
matrices from which they are obtained.

Represent a row subset by a five-bit mask, with the least
significant bit corresponding to the top row.
The row-reversal orbits of reachable even-column states,
in the chosen order, are

$$

 \{0\},\ \{3,24\},\ \{6,12\},\ \{9,18\},\
 \{15,30\},\ \{27\}.

$$

Row-reversed states have equal counts.
Let each component of $u_j$ record the count of *one
individual state* in the corresponding orbit after $2j$
columns, rather than the sum over that orbit.
Then $u_0=\mathbf e_0$ and $u_{j+1}=Mu_j$, where

$$

 M=\begin{pmatrix}
8&6&4&2&2&1\\
3&4&1&1&1&1\\
2&1&2&1&1&0\\
1&1&1&2&1&0\\
1&1&1&1&1&0\\
1&2&0&0&0&1
\end{pmatrix}.

$$

Define

$$

 P(t)=1-15t+32t^2-15t^3+t^4,\qquad
 N(t)=\begin{pmatrix}
1-7t+7t^2-t^3\\
3t-4t^2+t^3\\
2t-5t^2+t^3\\
t+t^2\\
t-t^3\\
t-t^3
\end{pmatrix}.

$$

Polynomial multiplication gives the exact identity

$$

 (I-tM)N(t)=P(t)\mathbf e_0.

$$

Since $P(0)=1$, it follows that

$$

 f(t):=\sum_{j\ge0}u_jt^j=\frac{N(t)}{P(t)}.

$$

Appendix A also records all four nonconstant
coefficient-vector identities underlying
(6.4).

The terminal row vectors for vertical-axis reflection are

$$

 w_{v,e}=(1,2,2,2,2,1),\qquad
 w_{v,o}=(8,6,4,4,2,1),

$$

and those for the half-turn are

$$

 w_{r,e}=(1,0,0,0,0,1),\qquad
 w_{r,o}=(2,2,0,0,0,1).

$$

The even vectors sum all states or only row-reversal-fixed
states. The odd vectors first apply one column transition
and then take the appropriate sum.
Lemma 3.1 gives

$$

\begin{aligned}
 V_5(x)&=(w_{v,e}+xw_{v,o})f(x^2),\\
 R_5(x)&=(w_{r,e}+xw_{r,o})f(x^2).
\end{aligned}

$$

**Theorem 6.1.** 
The four fixed-point generating functions at height five are

$$
\begin{aligned}
 D_5(x)&=\frac{1-7x+7x^2-x^3}{P(x)},&
 H_5(x)&=\frac{1-x}{1-3x+x^2},\\
 V_5(x)&=\frac{1+8x+8x^2-23x^3-9x^4+16x^5-x^7}{P(x^2)},\\
 R_5(x)&=\frac{1+2x-6x^2-7x^3+7x^4+6x^5-2x^6-x^7}{P(x^2)}.
\end{aligned}
$$

The orbit generating function is

$$

 A_5(x)=\frac{D_5(x)+H_5(x)+V_5(x)+R_5(x)}4.

$$

**Proof.** 
A complete tiling has empty terminal state, so $D_5=f_0$,
giving the first formula.
Substitution of (6.3) into (6.5) gives
the two formulas for $V_5,R_5$.

By Lemma 3.2, $h_{5,n}=t_2(2n)$.
A two-row tiling either starts with one vertical domino or
with two horizontal dominoes covering its first two columns.
Thus $t_2(j)=t_2(j-1)+t_2(j-2)$ for $j\ge2$, with initial
values $t_2(0)=t_2(1)=1$.
The two-step recurrence matrix is
$L=\left(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right)$,
which satisfies $L^2-3L+I=0$.
Hence $c_n=t_2(2n)$ satisfies $c_{n+2}=3c_{n+1}-c_n$,
with $c_0=1,c_1=2$, proving the formula for $H_5$.
Finally, Burnside's formula proves (6.9).

$\square$

Write

$$

 Q(x)=(1-3x+x^2)P(x)P(x^2)=\sum_{j=0}^{14}q_jx^j,\qquad
 U(x)=\sum_{j=0}^{13}b_jx^j,

$$

where $A_5(x)=U(x)/Q(x)$.
Table 3 lists all coefficients and the
fourteen initial values needed for

$$

 a_5(n)=-\sum_{j=1}^{14}q_j a_5(n-j),\qquad n\ge14.

$$

No minimality assertion about the recurrence order is needed.

Coefficients of $U,Q$ and initial values; $b_{14}=0$.

| $j$ | $b_j$ | $q_j$ | $a_5(j)$ |
| –- | –- | –- | –- |
| 0 | 1 | 1 | 1 |
| 1 | -13 | -18 | 5 |
| 2 | 6 | 63 | 33 |
| 3 | 194 | 144 | 329 |
| 4 | -365 | -1060 | 3818 |
| 5 | -371 | 1296 | 46878 |
| 6 | 1304 | 1312 | 584386 |
| 7 | -594 | -3492 | 7318152 |
| 8 | -703 | 1312 | 91752831 |
| 9 | 717 | 1296 | 1150774799 |
| 10 | -154 | -1060 | 14434490195 |
| 11 | -36 | 144 | 181060839597 |
| 12 | 15 | 63 | 2271175917429 |
| 13 | -1 | -18 | 28489049801109 |
| 14 | 0 | 1 | \text{by recurrence} |

The values $a_5(1),\ldots,a_5(5)=5,33,329,3818,46878$
agree with the entries for widths $2,4,6,8,10$ in
[Mathar (2013), Table 12].
This is a comparison made after the derivation; those values
were not used to fit a matrix or a generating function.

## The reduced five-row certificate

The even-column state orbits are listed in
(6.1). The odd-column orbits, in order, are

$$

 \{1,16\},\ \{4\},\ \{7,28\},\ \{13,22\},\
 \{19,25\},\ \{31\}.

$$

These twenty states form the set reachable from the empty
state. This can be checked directly from (3.1):
starting at mask zero and listing all successors reaches
exactly these states, and all their successors remain in
the set. Row reversal commutes with the transition relation
and fixes the initial state, so reversed states have equal
counts.

Let $u_j$ be the even-column count vector, with one-state
counts as in Section 6, and let $z_j$ be the next
odd-column vector. Then $z_j=Bu_j$ and $u_{j+1}=Cz_j$, where

$$

\begin{aligned}
 B&=\begin{pmatrix}
1&1&1&1&1&0\\
1&2&0&0&0&1\\
1&1&0&0&0&0\\
0&0&0&1&0&0\\
1&0&1&0&0&0\\
1&0&0&0&0&0
\end{pmatrix},\qquad
 C=\begin{pmatrix}
2&1&2&0&2&1\\
1&1&1&0&0&0\\
1&0&0&0&1&0\\
1&0&0&1&0&0\\
1&0&0&0&0&0\\
0&1&0&0&0&0
\end{pmatrix}.
\end{aligned}

$$

For an input orbit $O_j$ and an output representative $q_i$,
the corresponding entry is

$$

\sum_{p\in O_j}T_5[p,q_i].

$$

It does not depend on the choice of representative.
For example, $B_{2,2}=2$ because both masks 3 and 24
can precede mask 4.
The reduced matrices need not be symmetric:
their variables record the count of each state, not the
total of an orbit. Matrix multiplication gives $CB=M$.

The even orbit-size vector is $(1,2,2,2,2,1)$ and the odd
orbit-size vector is $(2,1,2,2,2,1)$.
The fixed masks of row reversal are 0 and 27 on the even side,
and 4 and 31 on the odd side. Consequently,

$$

 w_{v,o}=(2,1,2,2,2,1)B,\qquad
 w_{r,o}=(0,1,0,0,0,1)B,

$$

which gives the terminal vectors in the text.

To check (6.4) coefficientwise, write
$N(t)=n_0+n_1t+n_2t^2+n_3t^3$, with

$$

\begin{array}{ll}
n_0=(1,0,0,0,0,0)^{\mathsf T},&
n_1=(-7,3,2,1,1,1)^{\mathsf T},\\
n_2=(7,-4,-5,1,0,0)^{\mathsf T},&
n_3=(-1,1,1,0,-1,-1)^{\mathsf T}.
\end{array}

$$

Direct integer multiplication gives

$$

\begin{aligned}
n_1-Mn_0&=-15\mathbf e_0,&
n_2-Mn_1&=32\mathbf e_0,\\
n_3-Mn_2&=-15\mathbf e_0,&
-Mn_3&=\mathbf e_0.
\end{aligned}

$$

Together with $n_0=\mathbf e_0$, these are all coefficients of
$(I-tM)N(t)=P(t)\mathbf e_0$.
Thus the certificate consists of finitely many explicit
integer identities and determines every coefficient of
the generating functions.
