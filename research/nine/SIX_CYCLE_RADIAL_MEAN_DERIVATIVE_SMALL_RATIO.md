# The radial mean-port derivative on the complementary small-ratio domain

Date: October 26, 2026.

**Status: complete analytic scalar proof, accepted after root and separate
independent reviews.** See REVIEW_C6_RADIAL_MEAN_FAMILIES_ROOT_2026_10_26.md
and REVIEW_C6_RADIAL_ADJACENT_MEAN_AND_SMALL_RATIO_2026_10_26.md.
This complements
[SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md](SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md).
It uses one monotone rational function and one completed square.

Let

\[
 0<a\le2,\qquad \frac47\le u\le1,\qquad 0<r\le\frac12,
 \qquad D=1-ur,\qquad k=\frac{1-u}{D}.
\tag{1}
\]

For the same derivative bracket

\[
 \mathcal B=
 \left(1-\frac{1+u}{a(u+r)}\right)
       \left(2-2k+\frac{k^2}{a}\right)
       -\frac{r(1+u)(a-k)^2}{a^2D},
\tag{2}
\]

we prove

\[
                              \mathcal B<0.
\tag{3}
\]

Put \(M=(1+u)/(u+r)\). The exact domain bounds are

\[
 0\le k\le\frac35,\qquad M\ge\frac43,\qquad
 M-2k\ge\frac2{15}>0.
\tag{4}
\]

The first follows because k decreases in u and increases in r;
the second because M decreases in u and r. All denominators are
positive on (1).

If \(a\le M\), the first term of (2) is nonpositive because
\(2-2k+k^2/a>0\), and the second is nonpositive. They cannot
both vanish: if \(a=M\), then \(a-k>0\); if \(a=k\), then
\(a<M\). Hence (3) is strict in this case.

Suppose now \(M<a\le2\). In particular \(a-k>0\). Multiplication
by the positive number \(a^2/(a-k)^2\) shows that (3) is equivalent to

\[
 f(a):=\frac{(a-M)\{2a(1-k)+k^2\}}{(a-k)^2}
                    <\frac{r(1+u)}D.
\tag{5}
\]

Direct differentiation gives

\[
 f'(a)=
 \frac{2a(1-k)(M-2k)
              +k\{2M-(a+k)k\}}{(a-k)^3}>0.
\tag{6}
\]

Indeed the first numerator term is strictly positive by (4), and
the second is nonnegative, since

\[
 2M-(a+k)k
       \ge\frac83-\left(2+\frac35\right)\frac35
       =\frac{83}{75}>0.
\tag{7}
\]

Thus \(f(a)\le f(2)=2-M\). The final comparison is valid on the
larger domain \(0<u\le1,\ r>0,\ ur<1\):

\[
 2-M-\frac{r(1+u)}D=-\frac{J}{(u+r)D},
\tag{8}
\]
where
\[
 J=(3u+1)r^2-2(1-u)(1+u)r+(1-u).
\tag{9}
\]

For \(u<1\), its completed square is

\[
 J=(3u+1)
       \left(r-\frac{(1-u)(1+u)}{3u+1}\right)^2
       +\frac{(1-u)u(u^2+u+2)}{3u+1}>0.
\tag{10}
\]

For \(u=1\), directly \(J=4r^2>0\). Equations (5)--(10)
prove the strict sign (3), including \(a=2\), \(u=1\), and
\(r=1/2\).

Together with the complementary source, this gives \(\mathcal B<0\)
whenever

\[
 \frac43\le a\le2,\qquad \frac47\le u\le1,\qquad 0<r<1.
\tag{11}
\]

For \(r\ge1/2\), use the earlier proof; for \(r\le1/2\), use
the present proof. The overlap at \(r=1/2\) is included in both.
This is an analytic cover of two whole ratio ranges and introduces no
finite sign packet or subdivisions within either range.

As in the complementary source, applying this scalar result to a
physical core still requires its actual chart, its derivative formula,
and a connected interval on which all premises hold. No original
geometric gate is closed by this lemma alone.
