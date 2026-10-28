> **Historical research notes (October 25, 2026). Statements below about pending formalization describe that stage. The current English v2.1 paper and M1–M11 verification are linked from [STATUS](../../STATUS.md); external review and bibliographic priority remain unresolved.**

# A001: Complete block proof

English edited proof record, October 25, 2026. Definitions, arguments and formulas are reproduced from the English mathematical article. Statement and cross-reference numbers follow that article. The PDF and LaTeX source preserve the authoritative equation numbering and typography.

[English article](../../papers/en/README.md) · [Sources](references.md) · Attempt overview

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

## Indecomposable blocks

### Column states

Consider a three-row rectangle of arbitrary width $w$.
At the cut between columns $j$ and $j+1$, let
$S_j\subseteq\{1,2,3\}$ be the set of rows crossed by a horizontal
domino. Set $S_0=S_w=\varnothing$.
If a column has incoming state $p$ and outgoing state $q$, then
the transition is legal precisely when

$$

 p\cap q=\varnothing,\qquad
 \{1,2,3\}\setminus(p\cup q)\in
 \{\varnothing,\{1,2\},\{2,3\}\}.

$$

Indeed, the cells in $p$ are covered from the left, those in $q$
are covered towards the right, and the remaining cells must be
paired vertically. Their vertical completion is unique.
Table 1 lists every transition.

The complete three-row transition table.

| Input | Outputs | Input | Outputs |
| –- | –- | –- | –- |
| $\varnothing$ | $\{1\},\{3\},\{1,2,3\}$ | $\{1,2\}$ | $\{3\}$ |
| $\{1\}$ | $\varnothing,\{2,3\}$ | $\{1,3\}$ | $\{2\}$ |
| $\{2\}$ | $\{1,3\}$ | $\{2,3\}$ | $\{1\}$ |
| $\{3\}$ | $\varnothing,\{1,2\}$ | $\{1,2,3\}$ | $\varnothing$ |

**Lemma 2.1.** 
Tilings of a $3\times w$ rectangle are in bijection with legal
state paths of length $w$ from $\varnothing$ to $\varnothing$.

**Proof.** 
A tiling determines its cut states uniquely.
Conversely, place a horizontal domino at every row specified by
each internal cut state, and fill the remaining cells in each
column with the unique vertical completion.
Condition (2.1) prevents overlapping horizontal
dominoes and ensures that every remaining cell is covered.
The empty endpoint states exclude dominoes extending beyond the
rectangle. These constructions are inverse to one another.
The empty path gives the empty tiling when $w=0$.

$\square$

### First returns and block classification

**Definition.** 
An internal vertical grid line crossed by no domino is a
*fault*. A nonempty tiling of a three-row rectangle is an
*indecomposable block* if it has no internal fault.

**Lemma 2.3.** 
The indecomposable blocks are exactly $C$ and $A_k,B_k$ for $k\ge1$.
Here $C$ is the width-two block consisting of three horizontal
dominoes. The block $A_k$ has width $2k$ and consists of:

1. vertical dominoes in columns $1$ and $2k$, each covering
rows $1$ and $2$;

1. horizontal dominoes in row $3$ on column pairs
$(2j-1,2j)$, where $1\le j\le k$;

1. horizontal dominoes in each of rows $1,2$ on column pairs
$(2j,2j+1)$, where $1\le j<k$.

The block $B_k$ is the horizontal-axis reflection $h(A_k)$.

**Proof.** 
By Lemma 2.1, a block is a first-return path from the
empty state. Its first step has three possibilities.
If it reaches $\{1,2,3\}$, the next step is forced back to
$\varnothing$, giving $C$.
If it reaches $\{3\}$, every nonterminal excursion consists of
the two steps
$\{3\}\to\{1,2\}\to\{3\}$.
After $k-1$ such excursions, the path returns from $\{3\}$ to
$\varnothing$. This is a path of length $2k$ and gives exactly
the stated coordinates of $A_k$.
If the first step reaches $\{1\}$, the corresponding excursions
are $\{1\}\to\{2,3\}\to\{1\}$, giving $B_k$.
The complete transition table allows no other first-return path.

Every listed block is indeed indecomposable.
In $A_k$, every odd internal cut is crossed by a domino in row
$3$, and every even internal cut is crossed by dominoes in rows
$1,2$. Reflection gives the same assertion for $B_k$.
The unique internal cut of $C$ is crossed in all three rows.
The position of the first vertical domino distinguishes $A_k$
from $B_k$, whereas $C$ has no vertical domino.
Thus the classification has neither omissions nor repetitions.

$\square$

The exact-coordinate vector illustration appears in the accompanying English PDF; all block coordinates are specified in the text.

**Lemma 2.4.** 
Every three-row tiling has a unique decomposition into a word
over $\mathcal B=\{C\}\cup\{A_k,B_k:k\ge1\}$.
Let $\sigma$ fix $C$ and interchange $A_k,B_k$.
Under this correspondence,

$$

 h(W)=\sigma(W),\qquad v(W)=\operatorname{rev}(W),\qquad
 \rho(W)=\sigma(\operatorname{rev}(W)),

$$

where $\sigma$ is applied letterwise.

**Proof.** 
Cut a tiling at all its faults. The resulting pieces have no
internal faults and hence are precisely the blocks of Lemma
2.3. Every boundary in a block decomposition must
be a fault, and every fault must be used: omitting one would
leave a decomposable piece. This proves uniqueness.
Concatenation gives the inverse map, with the empty word
corresponding to the empty tiling.

Horizontal-axis reflection acts on individual blocks by $\sigma$.
Every block is invariant under vertical-axis reflection.
For $A_k$, the column reversal $c\mapsto2k+1-c$ interchanges
the endpoint vertical dominoes. It sends each bottom-row pair
$(2j-1,2j)$ to another such pair, with index $k+1-j$,
and each upper-row pair $(2j,2j+1)$ to another, with index $k-j$.
The block $C$ is fixed domino by domino. Since the two
reflections commute and $B_k=h(A_k)$, every $B_k$ is also
invariant under vertical-axis reflection.

Both reflections preserve the set of faults. Horizontal-axis
reflection preserves block order, whereas vertical-axis
reflection reverses it. Uniqueness of the decomposition now
gives (2.2), including when block widths differ.

$\square$

### Fixed words

Assign weight $x$ to $C$ and $x^k$ to $A_k,B_k$.
The exponent records half the width.
The block generating function is

$$

 F(x)=x+2\sum_{k\ge1}x^k=\frac{3x-x^2}{1-x}.

$$

Since $F(0)=0$, only finitely many words contribute to any
given coefficient.

**Proposition 2.5.** 
The four fixed-point generating functions are

$$
\begin{aligned}
D(x)&=\frac{1}{1-F(x)}=\frac{1-x}{1-4x+x^2},
&H(x)&=\frac{1}{1-x},\\
V(x)&=(1+F(x))D(x^2)
 =\frac{1+3x+x^2-x^3}{1-4x^2+x^4},\\
R(x)&=(1+x)D(x^2)
 =\frac{1+x-x^2-x^3}{1-4x^2+x^4}.
\end{aligned}
$$

**Proof.** 
An arbitrary word contributes to
$D=\sum_{\ell\ge0}F^\ell$.
A word fixed by $h$ must consist entirely of letters fixed by
$\sigma$. The only such letter is $C$, giving $H$.

A word fixed by $v$ is a palindrome. It has a unique expression
$U\operatorname{rev}(U)$ or $Ub\operatorname{rev}(U)$, where $b$ is any block.
The two copies of $U$ contribute $D(x^2)$, and the possible
central block contributes $1+F(x)$.

A word fixed by $\rho$ has a unique expression
$U\sigma(\operatorname{rev}(U))$, or $Ub\sigma(\operatorname{rev}(U))$ with $\sigma(b)=b$.
In the latter case $b=C$, so the central contribution is $1+x$.
In both constructions the two cases are disjoint and the
decomposition is reversible. A central block may cross the
geometric midline; that line is not required to be a fault.

$\square$

**First proof of Theorem 1.1.** 
Burnside's formula and Proposition 2.5 give

$$

 A(x)=\frac14\left[
 \frac{1-x}{1-4x+x^2}+\frac1{1-x}
 +\frac{2(1+2x-x^3)}{1-4x^2+x^4}\right].

$$

Put $P_3=1-4x+x^2$ and $Q_3=1-4x^2+x^4$.
On taking the common denominator $(1-x)P_3Q_3$, its numerator is

$$
\begin{aligned}
 &\frac{(1-x)^2Q_3+P_3Q_3+
 2(1+2x-x^3)(1-x)P_3}{4}\\
 &\hspace{35mm}=1-3x-4x^2+10x^3-4x^5+x^6.
\end{aligned}
$$

This proves (1.1). The denominator expands to

$$

 1-5x+x^2+19x^3-19x^4-x^5+5x^6-x^7.

$$

The numerator has degree six, so comparison of coefficients
of $x^n$ for $n\ge7$ gives (1.2).
The coefficients of degrees zero through six give the initial
values in the theorem.

$\square$

**Remark.** 
In [Mathar (2013), equation (26)], the variable $z$ marks the
full width, so the appropriate comparison is
$\overline T(z,3)=A(z^2)$.
After substitution into (2.7), the
horizontal-reflection contribution $H(z^2)/4$ can be written as

$$

 \frac18\left(\frac1{1+z}+\frac1{1-z}\right)
 =\frac1{4(1-z^2)},

$$

Rearranging the other contributions gives the cited expression.
In the three-row formulas of
[Mathar (2014), equations (4)–(6)], $z$ instead marks the
number of dominoes; the corresponding substitution is $z^3=x$.
