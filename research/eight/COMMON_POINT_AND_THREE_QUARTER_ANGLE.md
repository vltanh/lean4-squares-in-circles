# A hand common-point lemma for every exterior square

This note gives a whole-domain geometric inequality. Its arithmetic consists
of two explicit polynomials and four short Bernstein rows. It does not assume
the radial-boundary reduction, any sampled state set, or an interval-tree
certificate.

Write

\[
 Q=\frac{9789}{2500},\qquad h=\frac38,\qquad \lambda=\frac{103}{100}.
\]

**Common-point lemma.** Let a closed unit square lie in the closed disk
\(\lVert x\rVert^2\le Q\), and suppose it does not meet the open disk of
radius \(1/12\). If the polar angle of its center belongs to \([-h,h]\),
then the point \((\lambda,0)\) belongs to the **interior** of the square.

Consequently, the smaller angle between the centers of any two such squares
with disjoint interiors is strictly greater than \(3/4\).

## 1. Coordinates and two elementary bounds

Choose a square axis within \(\pi/4\) of the center ray. Reflection permits
its angle relative to the center ray to be written as
\(\alpha\in[0,\pi/4]\). Let the center ray make angle \(\beta\) with the
positive horizontal axis; thus \(|\beta|\le h\). In the square frame its
center is

\[
 (a,-b),\qquad a=r\cos\alpha,\qquad b=r\sin\alpha,\qquad a\ge b\ge0.
\]

If \(a\le1/2\), then also \(b\le1/2\), so the origin belongs to the
square, contrary to the core hypothesis. Thus \(a>1/2\). The nearest-point
formula and the core hypothesis now give

\[
 \frac1{144}
 \le \max(a-\tfrac12,0)^2+\max(b-\tfrac12,0)^2
 \le 2(a-\tfrac12)^2.
\]

In particular

\[
 a\ge\frac12+\frac1{12\sqrt2}>\frac59. \tag{1}
\]

The farthest vertex gives the other necessary bound

\[
 (a+\tfrac12)^2+(b+\tfrac12)^2\le Q. \tag{2}
\]

Only (1) and (2) will be used below. Thus the lemma applies to every radial
position between the core and the containing circle.

## 2. An outer-boundary inequality on the entire quadrant

For \(0\le\theta\le\pi/2\), let \(\rho(\theta)>0\) solve

\[
 \rho^2+\rho(\cos\theta+\sin\theta)+\frac12=Q.
\]

We claim

\[
 \rho(\theta)\cos\theta
 <\frac12+\lambda\cos(\theta+h)
 \quad(0\le\theta\le\pi/2). \tag{3}
\]

The alternating Taylor series at \(h=3/8\) give

\[
 \frac{9305}{10000}<\cos h<\frac{9306}{10000},
 \qquad \sin h<\frac{3663}{10000}. \tag{4}
\]

For example use the cosine series through its negative degree-six term for
the lower bound, through degree eight for the upper bound, and the sine
series through its positive degree-five term for the upper bound.

Put \(c=\cos\theta\), \(s=\sin\theta\), and

\[
 H=\frac12+\lambda\left(\frac{9305}{10000}c-
                         \frac{3663}{10000}s\right)>0.
\]

The nonnegative number \(\rho c\) is a root of

\[
 X^2+Xc(c+s)+(\tfrac12-Q)c^2=0.
\]

The left side increases with \(X\ge0\). Therefore (3) follows if

\[
 H^2+Hc(c+s)+(\tfrac12-Q)c^2>0. \tag{5}
\]

Use \(u=\tan(\theta/2)\in[0,1]\), so that
\(c=(1-u^2)/(1+u^2)\), \(s=2u/(1+u^2)\). Multiplying the left side of
(5) by \((1+u^2)^3\) gives \(P(u)\), where

\[
\begin{aligned}
10^{12}P(u)={}&169789312225-38723747740u-109557354141u^2\\
 &-3833660000000u^3+6742414645859u^4\\
 &+854071747740u^5-3663870687775u^6.
\end{aligned} \tag{6}
\]

Its positivity follows from the first two rows of the table in Section 4.

## 3. A core inequality

For \(0\le\alpha\le\pi/4\), we also claim

\[
 \lambda\sin(\alpha+h)-\frac59\tan\alpha<\frac12. \tag{7}
\]

Writing \(c=\cos\alpha\), \(s=\sin\alpha\), (4) shows that it suffices
to prove

\[
 \frac12c+\frac59s-
 \lambda\frac{9306}{10000}sc-
 \lambda\frac{3663}{10000}c^2>0. \tag{8}
\]

After multiplying by \((1+u^2)^2\), with
\(u=\tan(\alpha/2)\), the left side is the polynomial \(V(u)\):

\[
 9000000V(u)=1104399-7253324u+6791202u^2
             +27253324u^3-7895601u^4. \tag{9}
\]

Here \(0\le u\le\sqrt2-1<3/7\). The final two rows of Section 4 prove
positivity on the slightly larger interval \([0,3/7]\).

## 4. The complete small arithmetic table

On an interval \([l,r]\), substitute \(u=l+(r-l)v\) and write a degree
\(n\) polynomial as

\[
 \sum_{k=0}^n b_k\binom nk v^k(1-v)^{n-k}.
\]

The Bernstein basis terms are nonnegative and sum to one for
\(0\le v\le1\). In the following table, each listed integer divided by
\(100000\) is a **lower bound** for the corresponding coefficient \(b_k\).

| Polynomial | Interval | Degree | Lower bounds for \(100000b_0,\ldots,100000b_n\) |
|---|---|---:|---|
| \(P\) | \([0,1/2]\) | 6 | 16978, 16656, 16150, 13067, 7817, 4070, 3467 |
| \(P\) | \([1/2,1]\) | 6 | 3467, 2864, 5404, 12730, 24457, 32896, 12046 |
| \(V\) | \([0,3/14]\) | 4 | 12271, 7953, 4213, 1796, 1260 |
| \(V\) | \([3/14,3/7]\) | 4 | 1260, 725, 2072, 5861, 12468 |

All entries are positive. The table can be checked directly from (6) and
(9): if \(\sum a_jv^j\) is the power expansion after substitution, then
\(b_k=\sum_{j\le k} a_j\binom{k}{j}/\binom{n}{j}\). This is the entire
finite arithmetic required for (3) and (7).

The companion `common_point_polynomials.py` simply reproduces these two
expansions and these four rows using rational arithmetic. Its purpose is
to check transcription; the mathematical proof is the displayed table
and the preceding identity.

## 5. The four strict side inequalities

In the chosen square frame, the displacement from its center to
\((\lambda,0)\) has coordinates

\[
 d_e=\lambda\cos(\alpha+\beta)-a,
 \qquad
 d_f=-\lambda\sin(\alpha+\beta)+b.
\]

First, by (1),

\[
 d_e\le\lambda-a<\lambda-\frac59<\frac12.
\]

Since \(a\le\rho(\alpha)\cos\alpha\), (3) gives

\[
 a-\lambda\cos(\alpha+\beta)
 \le a-\lambda\cos(\alpha+h)<\frac12.
\]

Apply (3) at \(\theta=\pi/2-\alpha\), using
\(\rho(\theta)=\rho(\alpha)\). It yields

\[
 b<\frac12+\lambda\sin(\alpha-h),
\]

and hence

\[
 b-\lambda\sin(\alpha+\beta)<\frac12.
\]

Finally, \(b=a\tan\alpha>(5/9)\tan\alpha\) unless \(\alpha=0\), and
(7) gives

\[
 \lambda\sin(\alpha+\beta)-b
 \le\lambda\sin(\alpha+h)-b<\frac12.
\]

Thus both \(|d_e|<1/2\) and \(|d_f|<1/2\), proving the common-point
lemma, including the endpoints of the closed angular sector.

## 6. Global consequences for a seven-square exterior cycle

If two center rays had smaller angle at most \(3/4\), rotate their
bisector to the horizontal axis. Both squares would contain the same
point \((103/100,0)\) in their interiors. This contradicts interior
disjointness. Therefore every smaller center angle is greater than
\(3/4\).

For seven squares listed in cyclic center order, every consecutive gap
\(\delta_i\) is at least its smaller center angle. Since the gaps sum to
\(2\pi\),

\[
 \frac34<\delta_i<2\pi-6\frac34
 =2\pi-\frac92<\frac{3\pi}{4}. \tag{10}
\]

This also proves directly that each consecutive gap is less than \(\pi\).
It applies to an adjacent-pair representative: only disjointness of its
seven neighboring pairs is needed.

### Two backward secondary axes can never separate

Use the usual radial frame convention \(|\alpha_i|,|\alpha_j|\le\pi/4\).
Every state has \(1/2<r<3/2\), by (1) and
\(r^2+r+1/2\le Q<4\). Its transverse component satisfies
\(r|\sin\alpha|<1\), since (2) and \(a\ge b\) give
\(b<\sqrt2-1/2<1\).

For an ordered pair at gap \(0<\delta<3\pi/4\), the projection of the
center displacement on the **negative source secondary axis** is

\[
 -r_j\sin(\delta-\alpha_i)-r_i\sin\alpha_i.
\]

If \(\delta-\alpha_i\ge0\), its sine is nonnegative because the argument
is at most \(\pi\); the displayed projection is at most
\(r_i|\sin\alpha_i|<1\). If \(\delta-\alpha_i<0\), then
\(\alpha_i>\delta>0\), and the projection is strictly less than
\((r_j-r_i)\sin\alpha_i<1\).

Likewise the projection on the **negative target secondary axis** is

\[
 -r_i\sin(\delta+\alpha_j)+r_j\sin\alpha_j<1.
\]

If the sine argument is nonnegative, use the transverse bound; if it is
negative, use \((r_i-r_j)|\sin\alpha_j|<1\).

Every square-pair support threshold is at least 1. Thus these two signed
axes cannot witness separation. In the eight-axis indexing
\((e_i,f_i,e_j,f_j,-e_i,-f_i,-e_j,-f_j)\), axes **5 and 7** are absent
from every actual exterior seven-cycle. Combining this with the separate
outward-cap lemma, which removes axes 0 and 6, leaves exactly the four
possible axes **1, 2, 3, 4** over the entire continuous domain.

This note supplies a stronger global angle floor and an analytic axis
reduction. It does not by itself prove the remaining four-terminal
classification.
