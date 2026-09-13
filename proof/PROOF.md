# A candidate proof of Erdős Problem 354(i)
## Propagating integer meshes and permanent descent of modular gap runs

**Version:** v0.1.0-candidate — 12 September 2026.  
**Project contributors:** Andrewyzzz and Chatgpt-6 Astra (AI system).

This Markdown research note claims a complete proof of the theorem below and is
being made available for independent checking. It is **not** a statement of
community acceptance, a journal publication, or a proof-assistant-certified result.
It is an English rendering of the [revised Chinese proof](PROOF.zh-CN.md), with the
same numbered argument and the same finite mask certificate. Neither language
version should be used to conceal a discrepancy in the other.

The original frozen proof is preserved [here](../archive/FROZEN_20260912.zh-CN.md).
The changes responding to the supplied review reports are documented in
[the revision notes](../review/CHANGES.md). The mathematical constants are unchanged.

### Claimed theorem

For every pair of positive real numbers $\alpha,\beta$ with
$\alpha/\beta\notin\mathbb Q$, the set

$$
A_{\alpha,\beta}=\{\lfloor2^i\alpha\rfloor,
\lfloor2^i\beta\rfloor:i\ge0\}\setminus\{0\}
$$

is strongly complete: after deletion of any finite set of elements, every
sufficiently large integer is a sum of distinct remaining elements.

The argument has two parts. Sections 2–6 claim that an incomplete sequence with
infinitely many nonzero binary events must eventually have bounded ratios between
successive event positions. Sections 8–11 claim that an irrational ratio of the
real parameters makes such bounded event ratios incompatible with incompleteness.
The second part includes the full finite-event estimate (FE) and digit-budget
propagation (DB); these are internal arguments, not externally accepted theorems.
The only external mathematical facts used are standard continued-fraction facts,
referenced in Section 14. The finite coefficient certificate is an explicit part
of the argument. Random and finite-prefix tests are not substitutes for any
infinite quantifier.

## 1. Normalization, indices, and two different notions of gap

Start with the original parameters $\alpha_0,\beta_0>0$. Choose an integer $k$
such that $1<2^k\alpha_0/\beta_0<2$. Equality at an endpoint would make the
original ratio a rational power of two, so cannot occur. Choose nonnegative
integers $u,v$ with $u-v=k$. Replacing the two parameters by
$\alpha_1=2^u\alpha_0$ and $\beta_1=2^v\beta_0$ deletes only finite prefixes.
A further common multiplication by a sufficiently large power $2^T$ gives

$$N=\lfloor\beta\rfloor<M=\lfloor\alpha\rfloor<2N,\qquad N\ge2.$$

Indeed, both $\alpha_1-\beta_1$ and $2\beta_1-\alpha_1$ are positive; after
multiplication they dominate the bounded floor errors. No downward or arbitrary
real scaling is used. A complete retained tail is enough to prove completeness
of the original set.

Write

$$a_i=\lfloor2^i\alpha\rfloor,\quad b_i=\lfloor2^i\beta\rfloor,
\quad a_{i+1}=2a_i+u_i,\quad b_{i+1}=2b_i+v_i,$$

where $u_i,v_i\in\{0,1\}$. The inequalities

$$b_i<a_i<2b_i\le b_{i+1}$$

persist. Thus the actual sorted order is $b_i,a_i,b_{i+1},a_{i+1},\ldots$,
with each next weight at most twice its predecessor. In particular the retained
sequences have no repeated values between them.

**Events are indexed by the arrival layer:**

$$\mathcal T=\{t\ge1:(u_{t-1},v_{t-1})\ne(0,0)\},\qquad
K_n=|\mathcal T\cap[1,n]|.$$

A digit pair $u_i,v_i$ describes departure from layer $i$, whereas the associated
event has position $i+1$. Define

$$
P_n=P(a_i,b_i:0\le i<n),\quad S_n=\sum_{i<n}(a_i+b_i),\quad
L_n=a_n+b_n,\quad D_n=\gcd(a_n,b_n),\quad X_n=P_n\bmod D_n.
$$

Here $P$ includes the empty sum; each original index can be used at most once in
each representation. $P_n$ does not use $a_n,b_n$, although $K_n$ counts the
conversion that determines them.

If the event set were finite, both sequences would double exactly after some
$n_0$. Dividing by $2^i$ and taking limits would give
$\alpha=a_{n_0}/2^{n_0}$ and $\beta=b_{n_0}/2^{n_0}$, contradicting the irrational
ratio. Thus the event set is infinite for the theorem's parameters.

For a nonempty subset $X$ of $\mathbb Z/d\mathbb Z$, let $h(X)$ be the number
of residues in its longest consecutive missing run around the circle, and set
$h(X)=0$ when $X$ is full. Put $h_n=h(X_n)$. For a finite integer set $W$ with
at least two elements define

$$\operatorname{span}(W)=\max W-\min W,\qquad
\operatorname{gap}(W)=\max\{w_{j+1}-w_j\},$$

where the $w_j$ are its distinct elements in increasing order. A gap of $k$
corresponds to at most $k-1$ consecutive missing integers.

### 1.1 A fixed bound for every prefix

For sorted positive weights $c_j$ with $c_{j+1}\le2c_j$,

$$c_{j+1}-\sum_{i\le j}c_i\le c_j-\sum_{i<j}c_i\le c_0.$$

When adding a weight, the new subset sums are the old set and a translate. If
their convex hulls are disjoint, the only new gap is bounded by the expression
above; if they intersect, gaps do not increase. Hence $\operatorname{gap}(P_n)
\le N$ on $[0,S_n]$.

For $n\ge2$,

$$S_n-a_n\ge(N-1)2^n-M-N+1\ge3N-M-3\ge N-2\ge0.$$

Using Lemma 2.3 and $D_n\le b_n\le a_n$ gives

$$0\le h_n\le N-1\qquad(n\ge2).\tag{1.1}$$

The single-column identity
$a_j-\sum_{i<j}a_i=M+\sum_{i<j}u_i>0$ and its $b$ analogue also imply
$S_n<L_n$.

## 2. Three finite lemmas

### Lemma 2.1: erosion by one translate

For a nonempty $X\subseteq\mathbb Z/d\mathbb Z$,

$$h(X\cup(X+1))=\max(0,h(X)-1).\tag{2.1}$$

The complement is the intersection of the old complement with its one-step
translate. Each missing run of length $r$ is shortened to $\max(0,r-1)$.
Nonemptiness excludes the all-missing circle.

### Lemma 2.2: propagation of a finite integer mesh

If $\operatorname{span}(W)\ge c>0$ and $\operatorname{gap}(W)\le k$, then

$$\operatorname{gap}(W\cup(W+c))\le k,\qquad
\operatorname{span}(W\cup(W+c))=\operatorname{span}(W)+c.\tag{2.2}$$

The two convex hulls intersect or touch, and their endpoints belong to the union.
An empty interval between consecutive union points cannot cross a hull endpoint
in its interior. It is therefore contained in one of the hulls, where its length
is at most $k$.

Consequently, if future weights obey $c_{i+1}\le2c_i$ and the initial span is at
least $c_1$, this construction keeps the same gap bound indefinitely: adding
$c_i$ makes the span at least $2c_i\ge c_{i+1}$.

### Lemma 2.3: projection to any smaller modulus

If $\operatorname{span}(W)\ge m\ge1$ and $\operatorname{gap}(W)\le k$, then

$$h(W\bmod m)\le k-1.\tag{2.3}$$

Translate $W$ analytically so that $\min W=0$; this merely rotates its residues,
and does not introduce negative original summands. The case $m=1$ is immediate.
For $m\ge2$, gaps among the points of $W\cap[0,m)$ are at most $k$. Let $w_-$
be its last point and $w_+$ the first point of $W$ at least $m$. The latter exists
by the span assumption. They are consecutive in $W$, so
$m-w_-\le w_+-w_-\le k$. This also bounds the wraparound interval to zero.
Adding residues from other points only reduces gaps.

We will preserve an actual integer mesh, not just a density in a changing group.

## 3. A long exact block and its finite coefficient certificate

At a fixed layer $n$, write

$$A=a_n=dp,\quad B=b_n=dq,\quad (p,q)=1,\quad q<p<2q,$$

and put $E=P_n$, $S=S_n<d(p+q)$, $X=E\bmod d$, $H=h(X)$,
$k=\max(1,H)$. Thus $1\le k\le d$.

Use $\ell$ exact doubling pairs at indices $n,\ldots,n+\ell-1$, with
$K=2^\ell$. The next conversion is nonzero, $(u_1,v_1)\ne(0,0)$; the following
two conversions $(u_2,v_2),(u_3,v_3)$ are arbitrary. The three new pairs are

$$
\begin{array}{ll}
dKp+u_1,&dKq+v_1,\\
2dKp+2u_1+u_2,&2dKq+2v_1+v_2,\\
4dKp+4u_1+2u_2+u_3,&4dKq+4v_1+2v_2+v_3.
\end{array}
$$

They use indices $n+\ell,\ldots,n+\ell+2$ and belong to $P_r$ for
$r=n+\ell+3$. Define

$$F=q(p-1),\qquad B_*=S+d(F+p+q)+22,\qquad
K_*=2q(p-1)+4(p+q)+64,$$

and assume $K\ge K_*$.

### 3.1 The old coefficient interval

The exact block provides $d\{px+qy:0\le x,y<K\}$. When $K\ge p$ this includes
$d$ times the interval

$$[F,(p+q)(K-1)-F].\tag{3.1}$$

For $F\le z\le p(K-1)$ choose $0\le y<p$ with $qy\equiv z\pmod p$, then
$x=(z-qy)/p$ belongs to $[0,K-1]$. Reflecting the coefficients in the center of
the square gives the other interval, whose left endpoint is $q(K-1)$. They
intersect because $q<p$.

### 3.2 Two alternative offsets whose constants differ by one

Suppose two subset sums of the six new weights have the form

$$\sigma_0=dK l_0(p,q)+c,\qquad
\sigma_1=dK l_1(p,q)+c+1,\qquad0\le c<c+1\le22.$$

They are alternatives, not sums to be used together. Set

$$L=\max(l_0,l_1),\quad U=\min(l_0,l_1)+p+q,\quad
J=[dKL+B_*,dKU-B_*].$$

Every $z\in J$ whose residue lies in $(X+c)\cup(X+c+1)$ has a legal
representation. Choose the corresponding offset and $f\in E$ so that
$d\mid z-\sigma_j-f$. Since $0\le f\le S$, the two endpoint bounds ensure

$$F\le(z-\sigma_j-f)/d\le(p+q)(K-1)-F.$$

Equation (3.1) supplies the remaining old-block sum. The three groups of indices
are disjoint. The bound $B_*$ pays for actual representatives, not merely residues.
By (2.1), this proves

$$\text{every $k$ consecutive integers contained in $J$ include a point of $P_r$.}\tag{3.2}$$

### 3.3 The finite cone certificate

The mask table in Appendix A supplies a chain of the intervals $[L,U]$ satisfying

$$L_{\rm first}\le p+2q,\quad U_{\rm last}\ge7p+6q,$$

$$U_i-L_i>0,\qquad U_i-L_{i+1}>0,\qquad U_{i+1}-L_i>0.$$

Every quantity is an integer, so each strict margin is at least one. To check a
homogeneous form $ap+bq$ on $q<p<2q$, write $p=2x+y$, $q=x+y$ with $x,y>0$.
The form is nonnegative on the closed cone exactly when $2a+b\ge0$ and $a+b\ge0$;
if its coefficients are not both zero, it is positive in the open cone.

The first two pairs have 16 subset masks. There are three possible nonzero first
digits and four second digits, hence 12 templates. To each pair of masks with
constant difference one, add the same subset of the third pair to both offsets.
This shifts coefficients by $0,4p,4q$, or $4p+4q$; it does not change the constant
difference. For all four third digits the constants stay between 0 and 22.

Appendix A contains all 125 nodes and 113 strict links. The standalone
[checker](../certificate/check_templates.py) reconstructs coefficients from masks,
checks the cone inequalities, checks all 500 third-digit instances, and compares
the two proof appendices and the JSON. These finite symbolic checks, not sampled
ratios, establish the stated finite coefficient lemma.

## 4. Connecting meshes rather than complete intervals

Since $S$ is an integer, $S\le d(p+q)-1$. Thus

$$
\begin{aligned}
dK-2B_*&\ge d[2F+4(p+q)+64]
-2[d(p+q)-1+d(F+p+q)+22]\\
&=64d-42\ge22d.\tag{4.1}
\end{aligned}
$$

This includes $d=1$, where the last margin is exactly 22. Each actual node and
each adjacent overlap has width at least $22d$.

Put

$$L_*=dK(p+2q)+B_*,\qquad U_*=dK(7p+6q)-B_*,\qquad I=[L_*,U_*].$$

The constants $c$ can differ between nodes, so short internal gaps alone are not
enough to connect them. For a node $J_i=[l_i,r_i]$, the starting points of its
length-$k$ integer windows form $J_i^-=[l_i,r_i-k+1]$. As $k\le d$, (4.1)
ensures that these shortened intervals remain nonempty and adjacent ones still
intersect. Their union is connected and covers $[L_*,U_*-k+1]$. No monotonicity
of the node endpoints is required.

Every length-$k$ integer window in $I$ is therefore contained in a single node,
where (3.2) applies. Consequently, the actual subset-sum set $W=P_r\cap I$ satisfies

$$\min W\le L_*+k-1,\quad \max W\ge U_*-k+1,\quad
\operatorname{gap}(W)\le k,$$

$$\operatorname{span}(W)\ge U_*-L_*-2(k-1).\tag{4.2}$$

The next unused smallest weight has $b_r\le8dKq+15$. Since $6p-4q\ge1$,

$$U_*-L_*-(8dKq+15)\ge dK-2B_*-15\ge22d-15.$$

Hence

$$\operatorname{span}(W)-b_r\ge22d-15-2(k-1)\ge20d-13>0.\tag{4.3}$$

This is a mesh of actual integers with sufficient span to propagate.

## 5. Permanent descent, uniform over every future continuation

### Theorem 5.1

Under Section 3's hypotheses, for every legal continuation and every $t\ge r$,

$$h_t\le\max(0,h_n-1).\tag{5.1}$$

If $h_n\le1$, the whole continuation is complete.

**Proof.** For each $t\ge r$ define the actual set

$$W_t=W+P(a_i,b_i:r\le i<t)\subseteq P_t.$$

Apply Lemma 2.2 in the sorted order of unused weights. Its hypotheses hold by
(4.3), and each next weight is at most twice the preceding one. Thus

$$\operatorname{gap}(W_t)\le k,\qquad
\operatorname{span}(W_t)\ge b_t\ge D_t.$$

Lemma 2.3 gives $h(W_t\bmod D_t)\le k-1$, and $P_t$ contains $W_t$, proving
(5.1). When $k=1$, the $W_t$ are full integer intervals with the same fixed left
endpoint and unbounded right endpoints. Their union contains a half-line. ∎

This does not assert that $h_t$ is monotone at each individual conversion. It
asserts a permanently lower bound for all future moduli after a qualifying
update. Neither a majority hypothesis nor a changed endpoint ratio is required.

Since $K_*\le16p^2$ and $p\le a_n<(M+1)2^n$, the sufficient length condition

$$\ell\ge2n+C_M,\qquad C_M=2\lceil\log_2(M+1)\rceil+4\tag{5.2}$$

implies $K\ge K_*$. The constant is independent of every future word and modulus.

## 6. An incomplete sequence cannot have infinitely many qualifying gaps

Let the infinitely many arrival-event positions be $t_1<t_2<\cdots$. Call the
adjacent pair $n=t_j<m=t_{j+1}$ qualifying if $n\ge2$ and
$m-n\ge2n+C_M$.

By the arrival convention, $u_i=v_i=0$ for $n\le i\le m-2$. The indices
$n,\ldots,m-1$ supply exactly $\ell=m-n$ doubling pairs. The three new pairs
are at $m,m+1,m+2$, so Theorem 5.1 is effective from $m+3$.

If infinitely many gaps qualify, choose successive ones whose starting layers
lie beyond the preceding update. At the first one, (1.1) gives $h_n\le N-1$.
If $h_n\le1$, completeness follows at once. Otherwise each selected update
permanently reduces the bound on all subsequent $h_t$ by at least one. A
nonnegative integer bound cannot sustain this process: at most $N-1$ such
updates suffice for completeness.

Consequently every incomplete sequence with infinitely many events eventually
satisfies

$$t_{j+1}<3t_j+C_M,\qquad
\limsup_j t_{j+1}/t_j\le3.\tag{6.1}$$

In particular, $t_{j+1}\le4t_j$ eventually. This conclusion uses no FE or DB.

## 7. The final contradiction and strong completeness

Sections 8–11 prove the complementary statement:

> If $\alpha/\beta$ is irrational and $t_{j+1}\le R t_j$ eventually for a
> fixed $R$, then the sequence is complete.

Assume the claimed theorem false for the normalized parameters. Their event set
is infinite by Section 1. Section 6 gives eventual event ratio at most 4, while
Section 11 says this is incompatible with incompleteness. This is the contradiction.

The two arguments concern the same fixed parameters, prefixes, and arrival-event
set. Section 3's $p,q$ are reduced integer endpoint coordinates; Section 11's
$p_j,q_j$ are convergents of the real ratio. They are different auxiliary objects
and are never required to agree.

For any finite deletion, retain both tails above the deleted values and normalize
again using only upward dyadic shifts. The ratio is still irrational. Applying
the same argument proves completeness of the retained tail, hence strong
completeness of the original ordinary set. No repetition of equal-valued elements
is needed because the normalized tails strictly interlace.

## 8. Finite-event decay (FE), including the changing-period comparison

This section re-proves the internal estimate used below. To avoid confusing a
window deficit with a gcd, write

$$B_n=L_n-S_n=M+N+\sum_{i<n}(u_i+v_i)>0,\quad
Q_n=L_n-|P_n|,\quad G_n=|P_{n+1}|-2|P_n|\ge0.$$

The two sets $P_n$ and $P_n+L_n$ are disjoint. With $w_n=u_n+v_n$,

$$P_{n+1}=P_n+\{0,a_n,b_n,L_n\},\qquad
Q_{n+1}=2Q_n+w_n-G_n.\tag{8.1}$$

Periodically extend the indicator of missing positions in $[0,L_n-1]$ to $f_n$.
For a function of period $L$, put

$$J_t(f)=\sum_{x\bmod L}|f(x+t)-f(x)|.$$

Then $J_{-t}=J_t$, $J_{s+t}\le J_s+J_t$, and $J_1$ counts twice the number of
cyclic missing runs. Internal runs have length at most $N-1$; the terminal padding
run has length at most $B_n-1$. Thus

$$Q_n\le(N/2)J_1(f_n)+B_n.\tag{8.2}$$

Regard $P_n$ as a subset of $\mathbb Z/L_n\mathbb Z$. Every residue in
$(P_n+a_n)\setminus P_n$ has an actual new representative outside both basic
copies. Distinct residues give distinct integers. Therefore

$$J_{a_n}(f_n)\le2G_n,\quad J_{b_n}(f_n)=J_{a_n}(f_n),\quad
J_{2a_n}(f_n)\le4G_n.\tag{8.3}$$

Set $a=a_n,b=b_n,L=a+b,u=u_n,v=v_n,w=u+v$. The new period is $L'=2L+w$.
Before adding the two single translates, the missing word is $f_n f_n 1^w$;
these translates fill exactly $G_n$ holes. Comparing with the old periodic
extension yields

$$\sum_{0\le x<L'}|f_{n+1}(x)-f_n(x)|\le G_n+w.\tag{8.4}$$

The old function is extended using its old period. The two periods have not been
identified; the final $w$ positions are explicitly paid for.

### 8.1 Nonzero events control the unit boundary

Suppose $u=1$. The new shift is $a'=2a+1$, whose nonwrapping segment is
$0\le x<2b+v$. By (8.3) at the next layer and two applications of (8.4),

$$\sum_{x=0}^{2b+v-1}|f_n(x+2a+1)-f_n(x)|
\le2G_{n+1}+2G_n+2w.$$

Use its first $2b$ terms, $x=0,\ldots,2b-1$. They are legitimate because
$x+a'\le2L<L'=2L+1+v$. Requiring $x+a'<2L$ would impose an unnecessary old-period
cutoff. Cancelling the $2a$ shift costs at most $4G_n$. For
$\tau(x)=|f_n(x+1)-f_n(x)|$ this gives, on the old circular arc
$I=[L-2b,L-1]$,

$$\sum_I\tau\le2G_{n+1}+6G_n+2w.$$

The arcs $I$ and $I+b$ cover the old circle since $b<a<2b$. Moreover,

$$\sum_{x\bmod L}|\tau(x+b)-\tau(x)|\le2J_b(f_n)\le4G_n.$$

It follows that

$$J_1(f_n)\le16G_n+4G_{n+1}+4w.\tag{8.5}$$

If $u=0,v=1$, use the new period $2L+1$ and shift $2a$. Take the $L$ wrapping
positions $x=2b+1,\ldots,2b+L$, which are valid because $b<a$. The wrapped
coordinate is $x-2b-1$, equivalent modulo the old period to $x+2a-1$.
Equations (8.3)–(8.4) give

$$J_{2a-1}(f_n)\le2G_{n+1}+2G_n+2,\qquad
J_1(f_n)\le2G_{n+1}+6G_n+2,$$

which is stronger than (8.5). This covers all three nonzero digit types.

### 8.2 Two-step decay without double-counting events

From (8.2) and (8.5),

$$G_n+G_{n+1}\ge\frac{Q_n-B_n-4N}{8N}.$$

Using (8.1) twice, for $w_n>0$,

$$Q_{n+2}\le\left(4-\frac1{8N}\right)Q_n+\frac{B_n}{8N}+\frac{13}{2}.$$

Let $\rho=1-1/(32N)$ and $z_n=Q_n/2^n$. Since $B_n<3N+2n$,

$$z_{n+2}\le\rho z_n+2(n+1)2^{-n}\quad(w_n>0),\qquad
z_{n+1}\le z_n\quad(w_n=0).$$

Greedily partition the first $n$ conversions into one-step zero blocks and
nonoverlapping two-step blocks starting at nonzero events. At most a final
single event remains. If $r$ is the number of two-step blocks, then
$r\ge(K_n-1)/2$ and $r\le n/2$.

If the $j$-th two-step block starts at $i_j$, then $j\le i_j+1$. Its error at
the endpoint has factor $\rho^{r-j}$. Hence

$$\sum_j\rho^{r-j}2(i_j+1)2^{-i_j}
\le\rho^r\frac2\rho\sum_{i\ge0}(i+1)(2\rho)^{-i}.$$

The possible final single event satisfies $Q_n\le2Q_{n-1}+2$, contributing at
most $2^{1-n}$ after normalization. Thus

$$z_n\le\rho^r\left[z_0+\frac2\rho\sum_{i\ge0}(i+1)(2\rho)^{-i}\right]+2^{1-n}.$$

Since $N\ge2$, $\rho\ge63/64$, the geometric-series term is at most
$8064/961<9$, and $2^{1-n}\le2\rho^r$. With $z_0=M+N-1$ this yields

$$Q_n\le C_0 2^n\rho^{K_n/2}
\le C_0 2^n e^{-aK_n},\qquad
C_0=2(M+N+10),\quad a=\frac1{64N}.\tag{FE}$$

The intermediate step uses $\rho^r\le\rho^{-1/2}\rho^{K_n/2}<2\rho^{K_n/2}$.
All cardinalities above count different subset-sum values, not masks.

### 8.3 A contiguous-seed lower bound

Let $e_n=S_n+1-|P_n|\le Q_n$, and let $R_n$ be the largest width of an integer
interval contained in $P_n$. Its at most $e_n+1$ represented runs imply

$$R_n+2\ge\frac{S_n+2}{e_n+1}.$$

For $n\ge1$, $S_n\ge(M+N)2^{n-1}$, and
$2^ne^{-aK_n}\ge1$ because $K_n\le n$ and $a<\log2$. Therefore

$$R_n+2\ge c_0 e^{aK_n},\qquad
c_0=\frac{M+N}{2(C_0+1)}>0.\tag{FE-R}$$

## 9. Digit-budget propagation (DB)

Let $\theta=\alpha/\beta\in(1,2)$ and choose relatively prime $p,q$, $q\ge2$,
with $|\theta-p/q|<1/q^2$. At prefix depth $n$ put

$$\lambda=2^n\beta,\quad k=\lceil\log_2(8q)\rceil,\quad K=2^k,\quad
E_{n,k}=\sum_{i=n}^{n+k-1}(\{2^i\alpha\}+\{2^i\beta\}).$$

For either column, $r_{i+1}=2r_i-\epsilon_i$ implies
$\sum_{i=n}^{n+k-1}r_i=\sum_{i=n}^{n+k-1}\epsilon_i-r_n+r_{n+k}$. Thus

$$0\le E_{n,k}<2(K_{n+k}-K_n)+2.\tag{9.1}$$

The ideal suffix sums are $\lambda(\theta x+y)$ for $0\le x,y<K$. Each
corresponding actual sum is shifted down by an amount in $[0,E_{n,k}]$.

The $q$ phases $j\theta\bmod1$, $0\le j<q$, lie within $1/q$ of a uniformly
spaced $q$-grid, so their maximum circular gap is less than $3/q$. Set
$t_0=\lceil(q-1)\theta\rceil$. For each $0\le\ell\le K-q$, the values with
$x=\ell,\ldots,\ell+q-1$ give mesh at most $3/q$ in

$$[\ell\theta+t_0,\ell\theta+K-1].$$

Both endpoints are available by taking $x=\ell$. For finite-coefficient legality,
write $x=\ell+j$. Subtracting $\ell\theta$, any retained phase point is
$j\theta+y\in[t_0,K-1]$; $t_0\ge j\theta$ gives $y\ge0$, and the upper
bound gives $y\le K-1$. Thus no coefficient outside the finite square is used.

These windows overlap. Their union is
$[t_0,\theta(K-q)+K-1]$, of width $D\ge2K-3q+1>K$. On replacing the labelled
ideal points by actual sums, every ordered statistic moves down by at most
$E_{n,k}$. Hence gaps are at most $3\lambda/q+E_{n,k}$, and span at least
$\lambda D-E_{n,k}$. An old represented interval of width

$$W\ge3\lambda/q+E_{n,k}$$

connects all these points to form an integer interval wider than $\lambda K$.
The next unused weight is $b_{n+k}=\lfloor\lambda K\rfloor$, so this implies
completeness. The old interval uses indices below $n$, the suffix uses
$[n,n+k)$, and their supports are disjoint.

When $q\ge\lambda$, incompleteness therefore forces, with integer
$b=K_{n+k}-K_n$,

$$R_n<3\lambda/q+E_{n,k}<2b+5,\qquad
R_n\le2b+4.$$

Take the first convergent denominator $q(n)\ge2^n\beta$ and define
$f(n)=n+\lceil\log_2(8q(n))\rceil$. Combining with FE-R gives

$$K_{f(n)}\ge K_n+\frac{c_0}{2}e^{aK_n}-3.\tag{DB}$$

This is asserted for every sufficiently large $n$ under incompleteness, not just
for a matching subsequence.

## 10. Two restrictions on an incomplete parameter pair

Let $p_j/q_j$ be the continued-fraction convergents of $\theta$.

### 10.1 Sparse matching layers

At $n_j=\lfloor\log_2(q_j/\beta)\rfloor$, one has
$2^{n_j}\beta\le q_j$ and $k_j=\lceil\log_2(8q_j)\rceil=n_j+O(1)$.
Using the crude error bound $E\le2k_j$ in Section 9, incompleteness gives
$R_{n_j}\le2k_j+O(1)$. FE-R implies

$$K_{n_j}\le A\log(n_j+2)\tag{10.1}$$

for a constant depending on the fixed parameters. This bound is used only at
these matching layers.

### 10.2 Infinitely many large denominator jumps

If eventually $\log_2q_{j+1}\le(\log_2q_j)^2$, the first denominator crossing
$2^n\beta$ has logarithm $O(n^2)$, and hence $f(n)\le n^3$ eventually.
Since $K_n$ is nondecreasing and tends to infinity, DB then gives
$K_{n^3}\ge K_n^4$ for all sufficiently large $n$. Along
$n_r=n_0^{3^r}$ this implies
$K_{n_r}\ge K_{n_0}^{4^r}$, contradicting $K_{n_r}\le n_0^{3^r}$.
Thus an incomplete pair has infinitely many $j$ with

$$\log_2q_{j+1}>(\log_2q_j)^2.\tag{10.2}$$

## 11. Irrationality rules out bounded event ratios (BG)

Suppose, for contradiction, that the ratio is irrational, the sequence is
incomplete, and for a fixed integer $R\ge2$ every sufficiently large integer
$n$ has an event in $(n,Rn]$. This follows from any eventual bound on successive
event ratios, after enlarging the constant.

Along (10.2), set

$$T_j=\lfloor\log_2(q_{j+1}/\beta)\rfloor,\qquad
h_j=\lceil\log_2(p_j+q_j+1)\rceil.$$

Equation (10.1) applies to $T_j$, which is precisely the matching layer of the
next denominator. Thus $K_{T_j}=O(\log T_j)$ and $h_j=O(\sqrt{T_j})$.

Fix one such $j$ and write $p,q,T,h$ for these quantities. The convergent error
$|q\alpha-p\beta|<\beta/q_{j+1}$ gives $2^T|q\alpha-p\beta|<1$. For all
$i\le T$ the integers $\Delta_i=qa_i-pb_i$ obey
$|\Delta_i|<p+q+1\le2^h$. If the next $h$ conversions are zero, then
$\Delta_{i+h}=2^h\Delta_i$, forcing $\Delta_i=0$.

Every nonexact layer $0\le i\le T-h$ therefore sees an event among its next
$h$ arrival positions. Each event is counted at most $h$ times. The last $h$
layers are separately included, so on the whole interval

$$\#\{0\le i\le T:\Delta_i\ne0\}\le hK_T+h=:E
=O(\sqrt T\log T).\tag{11.2}$$

Define the minimum return cost

$$\nu(p,q)=\min_{c\ge1}s_2\bigl((cp)\mathbin{\mathrm{OR}}(cq)\bigr).$$

If $x<y$ are exact layers and $(x,y]$ contains an event, the legitimate suffix
words $U,V$ satisfy $qU=pV$. Hence $U=cp,V=cq$ with $c\ge1$, and

$$K_y-K_x=s_2(U\mathbin{\mathrm{OR}}V)\ge\nu(p,q).\tag{11.3}$$

As $p_j/q_j$ tends to a fixed irrational number in $(1,2)$,
$\nu(p_j,q_j)\to\infty$. Otherwise choose multiples with a uniformly bounded
number of joint one-bit positions. Divide both coordinates by the largest power
of two present. The numerator lies in $[1,2)$ and the denominator stays above
$1/2$. Passing to a subsequence, each of the bounded number of relative bit
positions either becomes constant or tends to negative infinity, and each bit
label stabilizes. Both limits are finite dyadic sums, with positive denominator;
their ratio is rational, contradicting the prescribed irrational limit. No bound
on the common multiplier or on its gcd is assumed here.

Let $n_0$ be a depth from which the event-window condition holds, and put
$x_0=\max(n_0+1,2E+1)$, $B=2R+1$. Each interval
$[B^ix_0,2B^ix_0]\subseteq[0,T]$ contains more than $E$ integers, hence an exact
layer $z_i$. Adjacent choices satisfy $z_{i+1}>Rz_i$, so $(z_i,z_{i+1}]$ really
contains an event. These intervals of conversions are disjoint; consequently

$$K_T\ge r\nu(p,q),\tag{11.4}$$

where $r$ is the number of adjacent chosen pairs. Since eventually
$x_0\le T^{2/3}$, their number is at least $\log T/(4\log B)$ for all sufficiently
large windows. The bound $K_T=O(\log T)$ would then make $\nu(p_j,q_j)$ uniformly
bounded along this subsequence, the contradiction just proved.

Thus irrationality and bounded event ratios imply completeness. Combined with
Section 6, this completes the claimed argument in Section 7.

## 12. A finite descent example

Take the empty old prefix, $A=12,B=8$, so $d=4,p=3,q=2$. The old residues are
just zero and the longest missing run has length 3. Here $K_*=92$; take
$K=128$, $\ell=7$, and the next three digit pairs $(1,1),(1,0),(0,0)$, followed
by $(0,0)$. After the old block and three new pairs, the next endpoint is
$(12300,8200)$, with gcd 4100. The actual prefix has 1052 missing residues modulo
4100, but the longest missing run has length 2. The modulus and number of holes
have increased; the saved mesh gap bound has improved. This rational-ratio
example tests the finite descent only.

## 13. Verification boundaries

Run `python certificate/check_templates.py` for the finite symbolic certificate.
Run `python verification/run_checks.py --full` for that certificate and the four
historical finite regression suites. The runner uses temporary directories and
writes fresh output to `verification/local_run.json` and `local_logs/`.

The regression suites are copied without mathematical changes. Their source
hashes are preserved in the package manifest. Historical input notes are supplied
for provenance; the main proof above does not require a reader to assume their
unproved conclusions. Finite samples do not establish FE, DB, compactness, the
existence of convergent subsequences, or all future continuations. Those
quantifiers are borne by the text. The independent certificate reimplementation
is a second implementation, not an external expert endorsement.

No formalization of the full theorem in Lean or another proof assistant is
claimed. Reviewers are particularly invited to challenge Section 4's window
covering, Section 5's permanent projection, Section 8.1's changing-period boundary,
and the common-parameter and event-index interfaces.

## 14. Sources and scope

1. [NIST DLMF, Section 1.12](https://dlmf.nist.gov/1.12): continued-fraction
   recurrences and identities; in particular the familiar convergent bounds
   $|\theta-p_j/q_j|<1/q_j^2$ and $|q_j\theta-p_j|<1/q_{j+1}$.
2. [Steve Fan, *Strongly Complete sets and a conjecture of Erdős*,
   arXiv:2607.14071v4](https://arxiv.org/html/2607.14071v4), 9 September 2026:
   equation (1.9) records the two dyadic-floor-sequence problem. This reference is
   background only; its five-elements-per-dyadic-block criterion is not used here.
3. [Erdős Problems, Problem 354](https://www.erdosproblems.com/354): the target
   is part (i), with base exactly 2. This repository does not claim the proof of
   part (ii) as its contribution.
4. [Historical internal inputs](../verification/inputs/): FE, DB, and BG notes.
   They are project working drafts, not independently certified literature.

No exhaustive priority review has been completed. This candidate and its release
must not be described as an accepted solution solely because code runs or a
forum link is visible.

## Appendix A. Complete finite mask certificate

The bit order for the first four weights is `a1,b1,a2,b2`, starting at the least
significant mask bit. A triple `(M0,M1,J)` specifies the two first-four masks and
the same third-pair subset added to both. `J=0,1,2,3` denotes neither, `a3`, `b3`,
or both. All intervals are reconstructed as in Section 3.

| First digits | Second digits | Complete mask chain |
|---|---|---|
|(1, 0)|(0, 0)|`[(3, 4, 0), (6, 5, 0), (2, 1, 2), (3, 4, 2), (6, 5, 2), (14, 7, 2), (2, 1, 3), (3, 4, 3), (6, 5, 3)]`|
|(1, 0)|(0, 1)|`[(10, 9, 0), (11, 12, 0), (7, 13, 0), (2, 1, 1), (3, 4, 1), (6, 5, 1), (2, 1, 3), (3, 4, 3), (6, 5, 3)]`|
|(1, 0)|(1, 0)|`[(10, 3, 0), (6, 5, 0), (2, 1, 2), (10, 3, 2), (6, 5, 2), (14, 7, 2), (2, 1, 3), (10, 3, 3), (6, 5, 3)]`|
|(1, 0)|(1, 1)|`[(3, 9, 0), (6, 5, 0), (2, 1, 2), (7, 13, 0), (2, 1, 1), (6, 5, 2), (3, 9, 1), (6, 5, 1), (2, 1, 3), (14, 13, 1), (3, 9, 3), (6, 5, 3)]`|
|(0, 1)|(0, 0)|`[(9, 10, 0), (12, 11, 0), (1, 3, 2), (9, 10, 2), (12, 11, 2), (7, 13, 2), (1, 2, 3), (4, 3, 3), (5, 6, 3)]`|
|(0, 1)|(0, 1)|`[(9, 10, 0), (12, 11, 0), (1, 3, 2), (9, 10, 2), (12, 11, 2), (13, 14, 2), (1, 2, 3), (4, 3, 3), (5, 6, 3)]`|
|(0, 1)|(1, 0)|`[(3, 9, 0), (5, 6, 0), (1, 2, 2), (1, 3, 2), (3, 9, 2), (5, 6, 2), (3, 9, 1), (5, 6, 1), (1, 2, 3), (1, 3, 3), (3, 9, 3), (5, 6, 3)]`|
|(0, 1)|(1, 1)|`[(8, 10, 0), (6, 9, 0), (1, 2, 2), (8, 10, 2), (4, 6, 2), (8, 10, 1), (6, 9, 1), (1, 2, 3), (1, 3, 3), (9, 10, 3), (5, 6, 3)]`|
|(1, 1)|(0, 0)|`[(3, 9, 0), (6, 11, 0), (0, 1, 2), (1, 8, 2), (3, 9, 2), (6, 11, 2), (7, 14, 2), (0, 1, 3), (1, 8, 3), (3, 9, 3), (6, 11, 3)]`|
|(1, 1)|(0, 1)|`[(3, 8, 0), (6, 9, 0), (7, 11, 0), (1, 3, 2), (13, 15, 0), (3, 8, 1), (6, 9, 1), (7, 11, 1), (3, 8, 3), (6, 9, 3), (5, 7, 3)]`|
|(1, 1)|(1, 0)|`[(3, 4, 0), (4, 5, 0), (5, 12, 0), (7, 13, 0), (0, 1, 1), (1, 8, 1), (3, 4, 1), (4, 5, 1), (5, 12, 1), (7, 13, 1), (3, 4, 3), (4, 5, 3), (5, 12, 3)]`|
|(1, 1)|(1, 1)|`[(3, 4, 0), (6, 11, 0), (7, 12, 0), (3, 4, 2), (6, 11, 2), (3, 4, 1), (6, 11, 1), (7, 12, 1), (3, 4, 3), (6, 11, 3)]`|
