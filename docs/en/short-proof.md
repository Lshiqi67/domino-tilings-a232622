> **Contributed expository note.** An elementary rewrite of the height-three part of [A002](half-board-proof.md) (Lemmas 3.1–3.2 and the height-three recurrence). It introduces no new method, is not part of the Lean development, and makes no priority claim.

# A one-page proof of the three-row theorem

The proof below uses only Burnside's lemma, the midline folding of A002, and two scalar recurrences. Every midline profile is evaluated by a one-line local argument instead of a transfer matrix, and the final common-denominator computation is written out, so the note can be read without the rest of the repository.

## Notation

Notation follows [statement](statement.md) and [A002](half-board-proof.md). Rows are numbered $1,2,3$ from top to bottom and columns from left to right;
$h(r,c)=(4-r,c)$, $v(r,c)=(r,2n+1-c)$ and $\rho=hv$.
Let $d_n,h_n,v_n,r_n$ be the numbers of tilings of the $3\times2n$ rectangle fixed by $e,h,v,\rho$.

For $j\ge0$ and $S\subseteq\{1,2,3\}$, let $q_j(S)$ be the number of tilings of the $3\times j$ rectangle with the cells $(r,j)$, $r\in S$, removed (A002's partial tilings with outgoing rows $S$). Put $q_0(\varnothing)=1$ and $q_0(S)=0$ for $S\ne\varnothing$. Define

$$t_j=q_j(\varnothing),\qquad s_j=q_j(\{1\})=q_j(\{3\}),$$

the second equality by $h$. Both vanish at negative indices.

## 1. Two auxiliary sequences

**Lemma 1.** $t_0=1$, $s_0=0$, and for $j\ge1$

$$t_j=t_{j-2}+2s_{j-1},\qquad s_j=t_{j-1}+s_{j-2}.$$

*Proof.* In a tiling counted by $t_j$, look at $(2,j)$. If it is joined vertically to $(1,j)$, then $(3,j)$ must be joined to $(3,j-1)$, leaving a board counted by $q_{j-1}(\{3\})=s_{j-1}$; joining it to $(3,j)$ is symmetric. If $(2,j)$ is joined horizontally, then $(1,j)$ and $(3,j)$ have no vertical partner, so the last two columns end in three horizontal dominoes: $t_{j-2}$.

In a tiling counted by $s_j$, the cells $(2,j),(3,j)$ are either one vertical domino, giving $t_{j-1}$, or two horizontal dominoes. In the latter case $(1,j-1)$ can only be joined to $(1,j-2)$, giving $s_{j-2}$. $\square$

Cell counts show $t_j=0$ for odd $j$ and $s_j=0$ for even $j$. With $T(y)=\sum_k t_{2k}y^k$ and $U(y)=\sum_k s_{2k+1}y^k$, Lemma 1 reads $T=1+yT+2yU$ and $U=T+yU$, hence

$$T(y)=\frac{1-y}{1-4y+y^2},\qquad U(y)=\frac1{1-4y+y^2}.$$

So $t_0,t_2,t_4,\ldots=1,3,11,41,\ldots$ and $s_1,s_3,s_5,\ldots=1,4,15,56,\ldots$; in A002's notation $t_{2j}=\alpha_j$ and $s_{2j+1}=\alpha_j+\beta_j$.

## 2. All eight midline profiles

**Lemma 2.** For $n\ge0$,

| $S$ | $q_n(S)$ | Reason |
| --- | --- | --- |
| $\varnothing$ | $t_n$ | definition |
| $\{1\}$, $\{3\}$ | $s_n$ | definition |
| $\{1,2\}$, $\{2,3\}$ | $s_{n-1}$ | the remaining cell of column $n$ is joined to column $n-1$ |
| $\{1,2,3\}$ | $t_{n-1}$ | column $n$ is empty |
| $\{2\}$, $\{1,3\}$ | $0$ | see below |

*Proof of the last row.* If $S=\{2\}$, the cells $(1,n),(3,n)$ have no vertical partner and are joined to column $n-1$, which leaves only $(2,n-1)$ in that column; so $q_n(\{2\})=q_{n-1}(\{1,3\})$. If $S=\{1,3\}$, the cell $(2,n)$ is joined to $(2,n-1)$; so $q_n(\{1,3\})=q_{n-1}(\{2\})$. Both counts vanish at $n=0$, hence for all $n$. $\square$

## 3. Fixed-point counts

**Horizontal reflection.** $h_n=1$. Every cell of row 2 is fixed by $h$. A vertical domino covering $(2,c)$ would have a different image covering the same cell, so row 2 consists of horizontal dominoes. Then rows 1 and 3 have no vertical partners, and the tiling is the all-horizontal one, which is $h$-fixed. (A002, Lemma 3.2.)

**Folding.** No vertical domino crosses the midline between columns $n$ and $n+1$. A horizontal domino crossing it in row $r$ is fixed by $v$ and is sent by $\rho$ to the crossing domino in row $4-r$. Restricting a $v$-fixed tiling to the left half and cutting the crossing dominoes gives a bijection with pairs $(S,P)$, where $S$ is arbitrary and $P$ is counted by $q_n(S)$. For $\rho$ the same holds with $S$ restricted to $\{4-r:r\in S\}=S$, that is $S\in\{\varnothing,\{2\},\{1,3\},\{1,2,3\}\}$. The inverse reflects or rotates the left half and inserts the crossing dominoes. (A002, Lemma 3.1.)

With Lemma 2:

$$
\begin{aligned}
d_n&=t_{2n},\\
v_n&=\sum_Sq_n(S)=t_n+t_{n-1}+2s_n+2s_{n-1},\\
r_n&=q_n(\varnothing)+q_n(\{2\})+q_n(\{1,3\})+q_n(\{1,2,3\})=t_n+t_{n-1}.
\end{aligned}
$$

## 4. The generating function

By the parity supports, $\sum_n(t_n+t_{n-1})x^n=(1+x)T(x^2)$ and $\sum_n(s_n+s_{n-1})x^n=x(1+x)U(x^2)$. Therefore

$$
D(x)=\frac{1-x}{1-4x+x^2},\quad H(x)=\frac1{1-x},\quad
V(x)=\frac{(1+x)(1+2x-x^2)}{1-4x^2+x^4},\quad R(x)=\frac{(1+x)(1-x^2)}{1-4x^2+x^4},
$$

in agreement with A001 and A002. Burnside's lemma gives

$$
\sum_{n\ge0}a(n)x^n=\frac14\left[\frac{1-x}{1-4x+x^2}+\frac1{1-x}+\frac{2(1+x)(1+x-x^2)}{1-4x^2+x^4}\right].
$$

Over the common denominator $(1-x)(1-4x+x^2)(1-4x^2+x^4)$ the three numerators are

$$
\begin{aligned}
(1-x)^2(1-4x^2+x^4)&=1-2x-3x^2+8x^3-3x^4-2x^5+x^6,\\
(1-4x+x^2)(1-4x^2+x^4)&=1-4x-3x^2+16x^3-3x^4-4x^5+x^6,\\
2(1-x^2)(1+x-x^2)(1-4x+x^2)&=2-6x-10x^2+16x^3+6x^4-10x^5+2x^6.
\end{aligned}
$$

Their sum is $4(1-3x-4x^2+10x^3-4x^5+x^6)$, which proves

$$
\sum_{n\ge0}a(n)x^n=\frac{1-3x-4x^2+10x^3-4x^5+x^6}{(1-x)(1-4x+x^2)(1-4x^2+x^4)}.\qquad\blacksquare
$$

## Remarks

With $z^2=x$, the three bracketed terms divided by 4 are exactly the three terms of Mathar's equation (26) ([references](references.md)): $H/4$, $(V+R)/4=(1+2x-x^3)/\big(2(1-4x^2+x^4)\big)$ and $D/4$. The proof above supplies the derivation of each term.

| $n$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $d_n$ | 1 | 3 | 11 | 41 | 153 | 571 | 2131 | 7953 |
| $h_n$ | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| $v_n$ | 1 | 3 | 5 | 11 | 19 | 41 | 71 | 153 |
| $r_n$ | 1 | 1 | 3 | 3 | 11 | 11 | 41 | 41 |
| $a(n)$ | 1 | 2 | 5 | 14 | 46 | 156 | 561 | 2037 |
