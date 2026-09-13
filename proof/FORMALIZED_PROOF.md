# Strong completeness of two dyadic floor sequences

Andrewyzzz and Chatgpt-6 Astra (AI system)

13 September 2026

Copyright 2026 Andrewyzzz. The manuscript text is licensed under
[CC BY 4.0](../LICENSE-CC-BY-4.0); code excerpts are offered under
[Apache-2.0](../LICENSE). See [LICENSING.md](../LICENSING.md) for the scope
and third-party notices.

## Abstract

For positive real numbers $\alpha$ and $\beta$ with irrational ratio, we prove
that the nonzero values of the two sequences $\lfloor2^n\alpha\rfloor$ and
$\lfloor2^n\beta\rfloor$ form a strongly complete set: every finite deletion
leaves a set whose distinct-element sums contain all sufficiently large
integers. We construct finite integer meshes from an explicit coefficient
certificate and propagate their gap bounds through every subsequent layer.
Sufficiently long intervals between binary events then produce permanent
descent of a modular gap invariant. Conversely, finite-event decay and a
digit-budget estimate yield long rational-approximation windows with few
events. Compactness of ratios of sparse binary sums forces a large event
cost between exact layers, contradicting the spacing bound obtained from
permanent descent. These arguments establish part (i) of Erdős Problem 354
and the stated finite-deletion strengthening.

## Theorem and scope

For $\alpha,\beta>0$, set

$$
A_{\alpha,\beta}
=\{\lfloor2^n\alpha\rfloor,\lfloor2^n\beta\rfloor:n\in\mathbb N\}
 \setminus\{0\}.
$$

**Theorem.** If $\alpha/\beta$ is irrational, then for every finite set
$F\subseteq\mathbb Z$, there exists an integer $H$ such that every integer
$m\ge H$ is a sum of distinct elements of $A_{\alpha,\beta}\setminus F$.

In particular, every sufficiently large integer is a finite-index sum of
the interleaving of the two floor sequences. In that indexed formulation,
each index is used at most once; different indices may have the same value.
The theorem above gives the stronger conclusion formulated in terms of
distinct values.

The [problem statement](https://www.erdosproblems.com/354) attributes the
dyadic completeness question to Graham and records Hegyvári's earlier
result when one parameter is dyadic rational and the other is not.
Hegyvári's broader conjecture concerns ratios other than integral powers
of two, with at least one non-dyadic parameter. Our theorem treats the
irrational-ratio case, with base exactly $2$; the rational-ratio cases of
that broader conjecture and the variable-base question in part (ii) are
different statements.

We give the argument in full below, including the finite certificate in
Appendix A. Our [Lean formalization](../formalization/README.md) proves the
indexed and strong-completeness targets under exactly the hypotheses above.
This exposition follows its use of good rational approximants, an explicit
decay potential, and a $T^{3/4}$ bound in the final counting argument.
The [original English manuscript](PROOF.md) is retained as the fixed
pre-formalization source. Our [contribution statement](../CREDITS.md)
describes the use of Chatgpt-6 Astra in both the mathematical development
and the Lean formalization.

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

We also have $S_n\ge a_n$ for $n\ge2$. Indeed,
$S_2\ge3(M+N)$ and $a_2\le4M+3$, whence
$S_2-a_2\ge3N-M-3\ge N-2\ge0$. The induction step is

$S_{n+1}-a_{n+1}=(S_n-a_n)+b_n-u_n\ge0.$

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
the two proof appendices and the JSON. In Lean, the concrete checker is evaluated by kernel reduction, and the
soundness theorem proves that acceptance implies these inequalities and legal
six-weight representations for every admissible pair $p,q$. Thus the finite
data supply a universal coefficient lemma.

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

$$\ell\ge2n+C_M,\qquad C_M=16(M+1)^2\tag{5.2}$$

implies $K\ge K_*$, since $2^{C_M}\ge16(M+1)^2$. We use this
explicit, non-optimal constant in the formalization. It is independent of
every future word and modulus.

## 6. Event spacing by well-founded descent

Suppose the arrival-event set is infinite. For consecutive events $n<m$,
call the gap qualifying if $m-n\ge2n+C_M$.

There is no nonzero conversion between arrival layers $n$ and $m$.
Accordingly, the $\ell=m-n$ pairs at indices $n,\ldots,m-1$ form an exact
doubling block, and the first nonzero conversion produces the pair at $m$.
The three new pairs occur at $m,m+1,m+2$. Theorem 5.1 therefore gives

$$h_t\le\max(0,h_n-1)\qquad(t\ge m+3).$$

We show that qualifying starting layers cannot be unbounded for an incomplete
sequence. Otherwise, begin at any qualifying layer. If its gap invariant is
at most one, Theorem 5.1 already gives completeness. If it is larger, choose
the next qualifying starting layer beyond the preceding permanent update.
Its invariant is strictly smaller. Well-founded descent on the natural
numbers rules out indefinite repetition. Notice that this argument uses
the permanent bound after each update, not monotonicity at every layer.

Thus, under incompleteness, consecutive sufficiently late events satisfy

$$m<3n+C_M,$$

and hence $m\le4n$ once $n\ge C_M$. Equivalently, after increasing a fixed
threshold $n_0$ if necessary, every integer $n\ge n_0$ has an arrival event
in $(n,4n]$. To see this, take the last event at or before $n$ and its
successor; the last event is eventually beyond the threshold for the
consecutive-event bound.

## 7. Reduction to the finite-event contradiction

For the normalized parameters, irrationality gives infinitely many events
by Section 1. If their interleaved sequence were incomplete, Section 6
would give a fixed bound on event spacing. Sections 8–11 contradict this
combination of irrationality, incompleteness, and bounded spacing.

To recover the theorem for the original parameters, let $F$ be a finite
set of deleted values and choose an upper bound for $F\cup\{0\}$.
We may carry out the upward dyadic shifts in Section 1 so that both
retained tails lie above this bound. Their ratio is still irrational.
Their values strictly interlace, so a finite-index representation from
these tails is a sum of distinct values of $A_{\alpha,\beta}\setminus F$.
Completeness of these tails proves strong completeness of the original set.
Taking $F=\varnothing$ also gives the indexed conclusion: select one original
index for each of the finitely many represented values.

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

### 8.2 A potential for two-step decay

From (8.2) and (8.5),

$$G_n+G_{n+1}\ge\frac{Q_n-B_n-4N}{8N}.$$

Applying (8.1) twice at a nonzero event gives

$$Q_{n+2}\le\left(4-\frac1{8N}\right)Q_n
                  +\frac{B_n}{8N}+\frac{13}{2}.$$

Set

$$z_n=\frac{Q_n}{2^n},\qquad
\rho=1-\frac1{32N},\qquad \sigma=1-\frac1{64N}.$$

Since $B_n<3N+2n$, we obtain

$$
\begin{aligned}
z_{n+1}&\le z_n &&(w_n=0),\\
z_{n+1}&\le z_n+2^{-n} &&\text{always},\\
z_{n+2}&\le\rho z_n+2(n+1)2^{-n} &&(w_n>0).
\end{aligned}
$$

We absorb the errors into the potential

$$V_n=z_n+9(n+1)2^{-n}.$$

For $N\ge2$ we have $\rho\ge63/64$ and $\rho\le\sigma^2$.
The elementary inequality

$$2(n+1)2^{-n}+9(n+3)2^{-(n+2)}
       \le \rho\,9(n+1)2^{-n}$$

shows that $V_{n+2}\le\rho V_n\le\sigma^2V_n$ at a nonzero
event. At a zero event $V_{n+1}\le V_n$, and always
$z_{n+1}\le V_n$.

Partition a finite interval of conversions into one-step zero blocks and
two-step blocks beginning with a nonzero event. A two-step block contains
at most two events. Since $0<\sigma<1$, its factor $\sigma^2$ pays for both;
a zero block needs no decay factor. There can be at most one final unpaired
conversion. Its estimate $z_{n+1}\le V_n$ is absorbed by a factor $2$,
because $\sigma\ge1/2$. Induction on the interval length therefore gives,
for all $m,d\ge0$,

$$z_{m+d}\le2V_m\,\sigma^{K_{m+d}-K_m}.$$

At $m=0$, $V_0=M+N+8$. Using $1-x\le e^{-x}$, we conclude

$$
Q_n\le C_0\,2^n e^{-aK_n},\qquad
C_0=2(M+N+10),\qquad a=\frac1{64N}.
\tag{FE}
$$

All cardinalities here count distinct subset-sum values. This potential
argument is the form of the error estimate used in the formalization.

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

$$[s,t]=[t_0,\theta(K-q)+K-1],$$

and $t-s>K+1$, since $K\ge8q$. In particular, for each $\xi\in[s,t]$
there are integers $0\le x,y<K$ with

$$\xi\le\theta x+y<\xi+3/q.$$

We now give a direct construction of legal integer representations.
Suppose an old represented interval $[a,b]\subseteq P_n$ has width

$$W=b-a\ge3\lambda/q+E_{n,k}.$$

Put $A=\lambda s+b-E_{n,k}$ and $B=\lambda t+b-E_{n,k}$.
For any integer $z\in[\lceil A\rceil,\lfloor B\rfloor]$, apply the
coefficient estimate to $\xi=(z-b+E_{n,k})/\lambda$.
The corresponding actual suffix sum $v$ satisfies

$$
z-b\le v<z-b+E_{n,k}+3\lambda/q\le z-a.
$$

Thus $z-v\in[a,b]$ and $z=(z-v)+v$ is a legal representation.
The old interval uses indices below $n$, and $v$ uses only indices in
$[n,n+k)$, so the supports are disjoint.

The represented integer interval has width

$$\lfloor B\rfloor-\lceil A\rceil
   >\lambda(t-s)-2>\lambda K,$$

where $\lambda\ge2$ and $t-s>K+1$. Its width exceeds the next unused
weight $b_{n+k}=\lfloor\lambda K\rfloor$. Lemma 2.2 with unit gap
then proves completeness.

Consequently, incompleteness forces $R_n<3\lambda/q+E_{n,k}$.
If $q\ge\lambda$, (9.1) and integrality give

$$R_n\le2(K_{n+k}-K_n)+4.$$

Combining this with FE-R yields

$$K_{n+k}\ge K_n+\frac{c_0}{2}e^{aK_n}-3.
\tag{DB}$$

This holds for every $n\ge1$ and every reduced rational approximant
with $q\ge2^n\beta$ and $|\theta-p/q|<1/q^2$.

## 10. Good rational approximants and long sparse windows

We call a reduced rational $r=p/q$, with $q>0$, good if

$$|\theta-r|<q^{-2}.$$

Dirichlet approximation gives good rationals with arbitrarily large
denominators when $\theta$ is irrational. For completeness, bounded
denominators would allow only finitely many good rationals, whereas
Dirichlet's estimates with increasing bounds force their errors to tend
to zero. None can equal $\theta$.

For an integer $b\ge2$, let $D(b)$ be the least denominator at least $b$
of a good rational. Dirichlet's theorem with bound $D(b)-1$ supplies a
reduced rational $p/q$ such that

$$q<D(b),\qquad |\theta-p/q|\le\frac1{D(b)q}.$$

This rational is itself good, because $q<D(b)$. Minimality of $D(b)$
therefore gives $q<b$. We shall use both the good rational at the crossing
denominator $D(b)$ and this pre-crossing rational; they serve different
purposes.

### 10.1 Matching layers and large advances

Put

$$
b(n)=\lceil2^n\beta\rceil,\qquad D_n^*=D(b(n)),\qquad
k(D)=\lceil\log_2(8D)\rceil,\qquad f(n)=n+k(D_n^*).
$$

Let $m(D)=\lfloor\log_2(D/\beta)\rfloor$ for $D\ge\beta$, and set

$$C_\beta=\lceil\log_2\lceil16\beta\rceil\rceil.$$

Then

$$2^{m(D)}\beta\le D<2^{m(D)+1}\beta,\qquad
k(D)\le m(D)+C_\beta.$$

Apply DB to a good rational with denominator $D_n^*$. Under incompleteness,

$$K_{f(n)}\ge K_n+\frac{c_0}{2}e^{aK_n}-3
\qquad(n\ge1).$$

We claim that $f(n)>n^3$ for arbitrarily large $n$. Otherwise,
monotonicity of $K_n$, its divergence to infinity, and exponential
growth would give

$$K_{n^3}\ge K_n^4$$

for all sufficiently large $n$. Choose such an $n_0>1$ with $K_{n_0}\ge2$.
Iteration yields

$$2^{4^r}\le K_{n_0}^{\,4^r}
   \le K_{n_0^{3^r}}\le n_0^{3^r},$$

which is impossible as $r\to\infty$, since $(4/3)^r\to\infty$.
This is the cubic-advance argument in the formalization.

At a matching layer $m=m(D)\ge1$, the crude bound
$E_{m,k(D)}\le2k(D)$ in Section 9, together with FE-R, gives

$$c_0 e^{aK_m}\le2m+2C_\beta+5.
\tag{10.1}$$

Indeed, $R_m<3+2k(D)$, so $R_m+2<2k(D)+5$.
We apply this estimate only to matching layers.

### 10.2 Simultaneous window estimates

Choose an arbitrarily large $n$ for which $f(n)>n^3$, put
$D=D_n^*$ and $m=m(D)$, and set $T=m-1$.
For $n\ge C_\beta+4$, the bound $k(D)\le m+C_\beta$ implies
$T\ge n^2$.

Take the pre-crossing rational $r=p/q$ constructed above, so that

$$q<b(n),\qquad |\theta-r|\le\frac1{Dq}.$$

Since $D\ge2^n\beta$, these rationals approach $\theta$ as $n\to\infty$;
in particular, $1<r<2$ for all sufficiently large choices.
Define its binary height by

$$H=\lceil\log_2(p+q+1)\rceil.$$

As $p<2q$ and $q<\lceil2^n\beta\rceil\le2^n\lceil\beta\rceil$,
we have $H\le n+C'_\beta$, where
$C'_\beta=\lceil\log_2(3\lceil\beta\rceil)\rceil$.
Taking $n\ge C'_\beta$ gives

$$H^2\le4T.$$

For $0\le i\le T$, put $\delta_i=qa_i-pb_i$. The approximation implies

$$2^T|q\alpha-p\beta|\le\frac{2^{m-1}\beta}{D}\le\frac12.$$

The floor errors lie in $[0,1)$, so

$$|\delta_i|<p+q+1\le2^H\qquad(0\le i\le T).$$

Finally, (10.1) at the crossing denominator $D$ and monotonicity of $K$
give

$$c_0e^{aK_T}\le2T+2C_\beta+7.$$

Thus there is a fixed constant $L>0$ such that, on arbitrarily large
windows, all the following hold simultaneously:

$$
H^2\le4T,\qquad K_T\le L\log T,\qquad
|\delta_i|<2^H\ (0\le i\le T),\qquad p/q\longrightarrow\theta.
\tag{10.2}
$$

Here and below $\log$ denotes the natural logarithm. More precisely,
for every prescribed error tolerance and lower bound on $T$, we can
choose a window satisfying the displayed estimates and that tolerance.
The good crossing rational supplies the event bound, while the
pre-crossing rational supplies the small height and all-layer precision.
No continued-fraction indexing is required.

## 11. The bounded-spacing contradiction (BG)

Assume the sequence is incomplete and, for some integer $R\ge2$ and
threshold $n_0$, every $n\ge n_0$ has an event in $(n,Rn]$.
Section 6 supplies this condition with $R=4$.
We derive a contradiction using the windows from Section 10.

### 11.1 Exact layers

Call $i$ exact if $\delta_i=qa_i-pb_i=0$.
If the next $H$ conversions after layer $i$ are zero, then

$$\delta_{i+H}=2^H\delta_i.$$

For $i+H\le T$, the bound $|\delta_{i+H}|<2^H$ and integrality force
$\delta_i=0$. Hence every nonexact layer $i\le T-H$ sees an event among
the next $H$ arrivals. Each event can be counted by at most $H$ such
layers. Including the last $H$ layers separately, we obtain

$$\#\{0\le i\le T:\delta_i\ne0\}
      \le H K_T+H=:E.
\tag{11.1}$$

By (10.2), $E=O(\sqrt T\log T)$.

### 11.2 A uniform lower bound on nontrivial return cost

Fix a positive integer $k$. Let

$$\mathcal A=\{0\}\cup\{2^{-j}:j\in\mathbb N\},\qquad
\mathcal S_k=\underbrace{\mathcal A+\cdots+\mathcal A}_{k\text{ times}}.$$

The set $\mathcal A$ is compact, and every element is rational.
Therefore $\mathcal S_k$ is compact and consists of rational numbers.
The set of ratios

$$
\mathcal C_k=
\{x/y:x,y\in\mathcal S_k,\ y\ge1/2\}
$$

is also compact and consists entirely of rational numbers. A fixed
irrational $\theta$ consequently has a neighbourhood disjoint from
$\mathcal C_k$.

Suppose $a<b$ are exact layers and the interval of arrivals $(a,b]$
contains at least one event. Unrolling the floor recurrences gives
nonnegative binary words $U,V$ with

$$a_b=2^{b-a}a_a+U,\qquad b_b=2^{b-a}b_a+V.$$

Exactness at both ends implies $qU=pV$. Since some event occurs, the
words are not both zero; since $p,q>0$, both are positive and $U/V=p/q$.

If $(a,b]$ contained at most $k$ events, divide $U$ and $V$ by the
largest power of two appearing in either word. Each normalized word
belongs to $\mathcal S_k$, and at least one is at least one.
The ratio lies in $(1,2)$, so the normalized denominator is at least
$1/2$. Hence $p/q\in\mathcal C_k$.

It follows that, once $p/q$ is sufficiently close to $\theta$, every
nontrivial return between exact layers costs more than $k$ events.
This estimate is uniform over the common multiplier in $U=cp,V=cq$;
we impose no bound on that multiplier.

### 11.3 Geometric capacity

Put $B=2R+1$ and choose a fixed positive integer $k$ with
$k\ge8L\log B$. Choose a window from Section 10 sufficiently far out
that the return-cost conclusion for this $k$ holds. Write $K=K_T$ and set

$$x=\max(n_0+1,E+1),\qquad r=\lfloor K/k\rfloor+1.$$

Since $E=O(\sqrt T\log T)$, we have $x\le T^{3/4}$ for all sufficiently
large windows. Also, $K\le L\log T$ implies

$$B^r\le B\,T^{1/8}.$$

Thus, after enlarging the lower bound on $T$,

$$2B^r x\le2B\,T^{7/8}\le T.$$

For each $i=0,\ldots,r$, the integer interval
$[B^i x,2B^i x]$ lies in $[0,T]$ and contains more than $E$ layers.
By (11.1), it contains an exact layer $z_i$. Consecutive choices satisfy

$$z_{i+1}\ge B^{i+1}x>R(2B^i x)\ge Rz_i.$$

Moreover, $z_i\ge n_0$, so there is an event in $(z_i,Rz_i]$ and
hence in $(z_i,z_{i+1}]$. The $r$ return intervals are disjoint.
Each costs more than $k$ events, and in particular at least $k$.
Therefore $rk\le K_T=K$, contradicting
$r=\lfloor K/k\rfloor+1$.

This proves that irrationality and bounded event spacing are incompatible
with incompleteness. Sections 6 and 7 now establish the theorem. $\square$

## 12. Correspondence with the Lean proof

The formalization uses integer-valued floor sequences and finite sets of
natural-number indices. The final statements in
[Statements.lean](../formalization/Dyadic354/Statements.lean) are fixed
independently of the intermediate proof modules.

| Argument in this exposition | Principal Lean modules |
|---|---|
| Normalization and distinct retained values, §§1 and 7 | Normalization, SetBridge, Main |
| Finite cone certificate, §3 and Appendix A | Basic, CertificateData, Certificate |
| Mesh lemmas and permanent descent, §§2–6 | CyclicGaps, Mesh, InitialMesh, PermanentMesh, FloorDescent, EventGaps |
| Finite-event decay and interval seeds, §8 | FECounting, FEMissingRuns, FEShift, PeriodChange, EventBoundary, FERecurrence, EventDecay, FE, FER |
| Legal coefficient coverage and digit budget, §9 | DBPhases, DBWindows, DBDigits, DBCover, DB |
| Good rational crossings and sparse windows, §10 | RationalWindows, CubicGrowth, DBScale, BGWindowBounds, BGWindows |
| Exact layers, return cost, and contradiction, §11 | BGExactLayers, BGSparseCompact, BGBinaryRatio, BGReturns, BGGeometric, BGCapacity, BG |

The [detailed theorem map](../formalization/STATUS.md) identifies the
principal declarations. The two final results are
Dyadic354.erdos354_part_i and Dyadic354.erdos354_strong_completeness.
The extracted-definition adapter also proves the positive part-(i)
target in the exact upstream definitions.

The project fixes Lean 4.27.0 and its dependency revisions. Our build and
audit check all 381 local theorems and require every transitive axiom set
to be a subset of {propext, Classical.choice, Quot.sound}.
The certificate computation is checked by the kernel. The
[verification records](../formalization/RESULTS.md) give the source
revisions, commands, and actual build output.

### References

1. T. F. Bloom, [Erdős Problem 354](https://www.erdosproblems.com/354):
   problem statement and references to Graham and Hegyvári.
2. The Mathlib Community,
   [Diophantine approximation](https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/NumberTheory/DiophantineApproximation/Basic.lean),
   pinned revision a3a10db0: the Dirichlet approximation results used in
   the good-rational construction.
3. The Formal Conjectures Authors,
   [Erdős Problem 354](https://github.com/google-deepmind/formal-conjectures/blob/a748dd915c908b21c4d864abf239f61049fa9d96/FormalConjectures/ErdosProblems/354.lean),
   pinned revision a748dd91: provenance of the formal target definitions.

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
