# Zero-quarter primary owners are excluded before mismatch contraction

**Status.** The primary-edge estimate in Sections 2–5 is a table-free hand
proof on its complete continuous domain. Section 6 turns it into a
seven-cycle exclusion using the common four-type pair inequality from G1.
That G1 inequality is an explicit prerequisite: this note does **not**
claim to have removed its remaining continuous certificates, nor to have
proved the coarse mismatch bound G4.

The resulting dependency is stronger than the old bootstrap: after G1,
all zero-quarter edges already have only original axes 0 and 2, before
any E/G/T cut or bound on the five-edge mismatch sum S. The argument
uses the frame tour's compulsory return, which is lost when a zero edge
is treated as an independent pair.

## 1. Hypotheses and the unchanged common marker

Work on the boundary neighbor cycle at

\[
 Q=9789/2500,\qquad R=\sqrt Q,\qquad
 a_0=\sqrt{Q-1/4}-1/2,\qquad c_0=\sqrt{Q/2}-1/2.
\]

Each canonical center is \((a,-\sigma b)\), with \(0\le b\le a\),
and lies either on the outer curve

\[
 (a+1/2)^2+(b+1/2)^2=Q,
\]

or on the core side/corner curve. Thus the already geometric coordinate
bounds are

\[
 447/800<a<283/200,\qquad 0\le b<9/10,
\tag{1}
\]

and a core center has \(a\le7/12\). The corner equation and the core
side share their actual common endpoint; neither is assigned a unique
chart label by this note.

Use exactly the unsigned G1 marker from
`../HAND_EXTERIOR_FRAME_CONCENTRATION.md`:

\[
\begin{aligned}
 F_C(a,b)&=7.506931(7/12-a)+1.077372b,\\
 F_L(a,b)&=.403875(a-a_0)+1.089065b, &&0\le b/a\le1/4,\\
 F_M(a,b)&=-2.143075+1.489593a+1.580219b,
                  &&1/4\le b/a\le3/7,\\
 F_H(a,b)&=\pi/4-.569472(a-c_0)+.390886(b-c_0),
                  &&3/7\le b/a\le1.
\end{aligned}
\tag{2}
\]

All terminating decimals in (2) are exact rational constants. The signed
marker is \(\ell=\sigma F\). At a shared endpoint choose a containing
marker once for the vertex and use it on both incident edges. Every
estimate below holds for either marker at such an endpoint.

The seven frame lifts have spread less than \(7/10\). On a zero-quarter
edge write \(\phi=d\), \(|d|<7/10\), with physical gap

\[
 g=d+\sigma\arctan(b/a)-\tau\arctan(B/A)>19/25.
\tag{3}
\]

Set

\[
 W(d)=\frac{1+\cos d+|\sin d|}{2},\qquad
 h(x)=\frac{\sin x+\cos x-1}{2}\quad(0\le x\le7/10),
 \qquad\beta=9/50.
\]

In zero-based original-axis numbering, the primary margins are

\[
 M_1=A-a\cos d+\sigma b\sin d-W(d),\qquad
 M_3=a-A\cos d-\tau B\sin d-W(d).
\tag{4}
\]

## 2. A primary separator has a positive large frame difference

Suppose first that \(M_1\ge0\).

If \(d\le0\) and \(\sigma b\ge0\), the signed sine term is
nonpositive. Since \(\cos d\ge151/200\), (1) gives

\[
 A-a\cos d+\sigma b\sin d-1
 <\frac{283}{200}-\frac{447}{800}\frac{151}{200}-1
 =-\frac{1097}{160000}<0.
\tag{5}
\]

If \(d\le0\) and \(\sigma b<0\), (3) implies \(\tau B<0\)
and \(g\le d+\pi/4\). Hence, using \(\pi<22/7\),

\[
 d>19/25-\pi/4>-3/100.
\]

With \(x=-d<3/100\), \(b\le a\) now gives

\[
\begin{aligned}
 A-a\cos d+\sigma b\sin d-1
 &\le A-a(\cos x-\sin x)-1\\
 &<\frac{283}{200}-\frac{447}{800}
       \left(1-\frac12(3/100)^2-3/100\right)-1\\
 &=-\frac{2027777}{16000000}<0.
\end{aligned}
\tag{6}
\]

Both alternatives contradict \(W\ge1\). Therefore \(d>0\).
If \(\sigma b\le0\), (5) applies again at this positive d; hence
\(\sigma b>0\). Because \(\cos d-\sin d>0\), feasibility also
forces

\[
 A\ge W+a\cos d-b\sin d
 \ge1+a(\cos d-\sin d)>1.
\tag{7}
\]

In particular the target is outer.

For \(0<d\le9/20\), (1), \(b\le a\), and the elementary sine and
cosine bounds give instead

\[
\begin{aligned}
 M_1
 &<\frac{183}{200}-\frac{847}{800}\cos d
                         +\frac{47}{800}\sin d\\
 &\le\frac{183}{200}-\frac{847}{800}
       \left(1-\frac12(9/20)^2\right)
                         +\frac{47}{800}\frac9{20}
 =-\frac{6473}{640000}<0.
\end{aligned}
\tag{8}
\]

Thus every feasible target-primary axis has

\[
 \boxed{9/20<d<7/10,\qquad\sigma b>0,\qquad A>1.}
\tag{9}
\]

For a source-primary axis exchange the states and replace both transverse
signs by their negatives, keeping d unchanged. The new target-primary
margin equals the old source-primary margin; its physical gap and its
marker difference also remain exactly the same. Consequently a feasible
source-primary axis has \(d>9/20\) and \(\tau B<0\). This is an
identity on the original margins, including ties, rather than a new owner
selection.

## 3. Whole-chart marker bounds

The following deliberately coarse bounds suffice:

\[
\boxed{
 F_O(a,b)\ge\frac45b\ge0,\qquad
 F_O(a,b)\le\frac25(a-a_0)+\frac{111}{100}b.}
\tag{10}
\]

Here \(F_O\) means whichever one of L, M or H was selected. For the
core marker,

\[
 \boxed{F_C(a,b)\ge7(7/12-a)+\frac{107}{100}b.}
\tag{11}
\]

The latter follows immediately from (2), \(a\le7/12\), and \(b\ge0\).
For completeness, the following is a whole-chart proof of (10), with no
subdivision within L, M or H.

The circle equation gives

\[
 a_0-a=\frac{b(b+1)}{a_0+a+1},\qquad
 a_0>707/500,\quad a_0<283/200,\quad
 899/1000<c_0<9/10.
\tag{12}
\]

Thus \((a_0-a)/b<3/5\) when \(b>0\). For L this proves

\[
 F_L\ge(1.089065-.403875\cdot3/5)b=.84674b\ge4b/5.
\]

The upper L bound follows from \(a-a_0\le0\),
\(.403875>2/5\), and \(1.089065<111/100\).

The function \(a(b)=\sqrt{Q-(b+1/2)^2}-1/2\) is concave. Therefore
\(-2.143075+1.489593a(b)+.780219b\) takes its minimum over M at
one of its two endpoints. At \(b/a=1/4\) we have \(a>649/500\);
at \(b/a=3/7\) we have \(a>1199/1000\). Substitution at those two
endpoints leaves, respectively, the positive lower reserves

\[
 87195559/2000000000,\qquad 38384599/875000000.
\tag{13}
\]

These endpoint bounds on a follow by inserting the proposed smaller a
in the circle equation: the positive squared-radius deficits are
\(11983/4000000\) and \(26771/24500000\), respectively.

For the upper M bound, put \(u=1.089593\), \(v=.470219\).
Circle support gives

\[
 ua+vb\le R\sqrt{u^2+v^2}-(u+v)/2.
\]

The exact bounds \(R<1979/1000\) and
\(\sqrt{u^2+v^2}<1187/1000\) imply

\[
 F_M-\frac25(a-a_0)-\frac{111}{100}b
 <-2.143075+\frac25\frac{283}{200}
 +\frac{1979}{1000}\frac{1187}{1000}-\frac{u+v}{2}
 =-1977/250000<0.
\tag{14}
\]

For the lower H bound, write \(f=.569472\), \(r=.390886\). The
circle support estimate, \(R<2\), and
\(\sqrt{f^2+(4/5-r)^2}<71/100\) give

\[
\begin{aligned}
 F_H-4b/5
 &\ge\pi/4+(f-r)c_0-
       R\sqrt{f^2+(4/5-r)^2}+(f+4/5-r)/2\\
 &>31/40+(f-r)\frac{899}{1000}-2\frac{71}{100}
                       +(f+4/5-r)/2\\
 &=2420907/500000000>0.
\end{aligned}
\tag{15}
\]

For the upper H bound, the difference is

\[
 C-u a-vb,\quad
 C=\pi/4+(f-r)c_0+\tfrac25a_0,
 \quad u=f+\tfrac25,\quad v=\tfrac{111}{100}-r.
\]

Both u and v are positive. Concavity again places the minimum of
\(u a(b)+vb\) at an endpoint of H. Bound
\(C<11/14+(f-r)(9/10)+(2/5)(283/200)\), and use the lower endpoint
bounds \(a>1199/1000\) at ratio \(3/7\) and \(a=b=c_0>899/1000\)
at ratio 1. The resulting upper reserves for the difference are

\[
 -68169877/3500000000,\qquad -19589949/3500000000,
\tag{16}
\]

both strictly negative. This proves all of (10).

All comparisons in (12)–(16) are single rational endpoint or norm
comparisons. For example the positive norm-square reserves in (14)
and (15) are \(65018639/10^{11}\) and \(621368811/(5\cdot10^{10})\).
There is no state or angle cover hidden in this calculation.

## 4. The primary-edge support estimate

We prove the uniform statement

\[
 \boxed{d+\ell_s-\ell_t+\beta h(d)>197/200}
\tag{17}
\]

for every feasible original primary axis on a zero-quarter edge.
By the exact exchange from Section 2 it suffices to take \(M_1\ge0\).
The source signed transverse coordinate is then strictly positive; the
target is outer. Since its unsigned marker is nonnegative, either target
sign obeys \(-\ell_t\ge-F_O(A,B)\).

Put \(p=2/5\), \(r=111/100\). Choose one of the following two support
parameters according to the source's intrinsic radial kind:

\[
 (m,c)=
 \begin{cases}
 (107/100,\;7/12),&\text{source core},\\
 (4/5,\;899/1000),&\text{source outer},
 \end{cases}
 \qquad\lambda=\frac{m}{\sin d}>0.
\tag{18}
\]

For an outer source, (10) and \(a\ge c_0>c\) give

\[
 F_O(a,b)+\lambda a\cos d-\lambda b\sin d
 \ge\lambda c\cos d.
\tag{19}
\]

For a core source, \(\lambda\cos d=m\cot d<m/d<7\), because
\(d>9/20\). Thus (11), together with \(a\le7/12\), gives exactly
the same inequality:

\[
\begin{aligned}
 F_C(a,b)+\lambda a\cos d-\lambda b\sin d
 &\ge7(7/12-a)+\lambda a\cos d\\
 &\ge\lambda(7/12)\cos d.
\end{aligned}
\tag{20}
\]

This explains the multiplier: it cancels the source transverse force
on the entire source chart. It is not fitted independently on small arcs.

Subtract \(\lambda M_1\) from the left side of (17), use (10),
(19)–(20), and support the single target circle. Since \(M_1\ge0\),
the original expression is at least

\[
\begin{aligned}
 X_{m,c}(d)={}&d+\beta h(d)+\lambda\bigl(W(d)+c\cos d\bigr)
              +p a_0+\frac{\lambda+p+r}{2}\\
 &\hspace{30mm}-R\sqrt{(\lambda+p)^2+r^2}.
\end{aligned}
\tag{21}
\]

Only the two displayed radial choices occur. The next section proves
\(X_{m,c}>197/200\) simultaneously over their entire allowed angle
interval. No physical-gap or sign condition is discarded before it has
supplied (9).

## 5. A single interval and two short polynomial identities

Put \(z=\tan(d/2)\), \(D=1+z^2\). From (9),

\[
 9/40<z<3/8.
\tag{22}
\]

The upper inclusion follows from
\(\arctan(3/8)\ge3/8-(3/8)^3/3>7/20\).
The cubic arctangent lower bound and concavity of
\(z/5-2z^3/3\) give, on the whole closed interval in (22),

\[
 d=2\arctan z\ge\frac95z+\frac{37}{1000}.
\tag{23}
\]

Indeed the endpoint reserves after subtracting the right side from the
cubic lower bound are \(13/32000\) and \(91/32000\). This is one
concavity argument, not a subdivision of the angle interval.

Use \(a_0>707/500\). Multiplying the desired inequality (21) by
\(2zD>0\), and applying (23), reduces it to

\[
 B_{m,c}(z)>R D\sqrt{V_m(z)},\qquad
 V_m(z)=\bigl(mD+\tfrac45z\bigr)^2+4(111/100)^2z^2.
\tag{24}
\]

For the two choices (18), the lower numerator is respectively

\[
\begin{aligned}
 B_C(z)&=\frac{107}{48}+\frac{2269}{1250}z
              +\frac{61}{10}z^2+\frac{1819}{1250}z^3
              +\frac{4213}{1200}z^4,\\
 B_O(z)&=\frac{2399}{1250}+\frac{3863}{2500}z
              +\frac{139}{25}z^2+\frac{2963}{2500}z^3
              +\frac{4101}{1250}z^4.
\end{aligned}
\tag{25}
\]

Every coefficient is positive. To check (24) it therefore suffices to
square it with the correct positive sign. Define

\[
 P_C=B_C^2-QD^2V_{107/100},\qquad
 P_O=B_O^2-QD^2V_{4/5}.
\]

Let \(x=3/8-z\), so \(0\le x\le3/20\). Direct expansion of the two
explicit degree-eight polynomials gives the common lower bound

\[
\begin{aligned}
 P_C(3/8-x),\;P_O(3/8-x)\ \ge\ 
 J(x):={}&\frac1{100}+3x-4x^2-16x^3+33x^4-56x^5\\
 &+45x^6-28x^7+7x^8.
\end{aligned}
\tag{26}
\]

For clarity, this coefficient comparison is completely specified by
(24)–(26): it asserts that both differences have nonnegative coefficients
in x. The smallest constant difference is the core one,

\[
 \frac{157644571203349}{15099494400000000}-\frac1{100}
 =\frac{6649627203349}{15099494400000000}>0.
\]

All other coefficient lower comparisons in (26) have reserves greater
than \(1/10\). They involve two degree-eight expansions, not any
computed state or angle lookup. The bound (26) itself has the following
visible whole-interval positivity proof:

\[
\begin{aligned}
 J(x)
 &\ge\frac1{100}
 +\left(3-4\frac3{20}-16(\frac3{20})^2\right)x
 +\left(33-56\frac3{20}\right)x^4\\
 &\quad+\left(45-28\frac3{20}\right)x^6+7x^8\\
 &=\frac1{100}+\frac{51}{25}x+\frac{123}{5}x^4
                 +\frac{204}{5}x^6+7x^8>0.
\end{aligned}
\tag{27}
\]

Thus both P polynomials are positive throughout (22). Since both B
polynomials are positive, (24) follows without a sign ambiguity after
squaring. Equations (21)–(24) prove (17) on the full primary-edge domain.

## 6. Close the whole-cycle owner contradiction

For the other six edges, use the actual G1 pair conclusion with the same
selected marker at each shared vertex. Every entry in its four-type
matrix is at least \(8833/10000\), so

\[
 \phi_j+\ell_j-\ell_{j+1}-\beta h(|d_j|)>8833/10000.
\tag{28}
\]

This is the only imported continuous pair inequality in this section.
Its remaining certificate dependency must be removed in G1 to make the
assembled theorem table-free.

A closed real frame walk whose range is less than \(7/10\) obeys

\[
 \sum_{j\ne i}h(|d_j|)\ge h(|d_i|).
\tag{29}
\]

To prove it, use the path formed by the other six edges between the two
endpoints of edge i. On this common real interval, h of distance is a
metric: if the middle point lies between the other two, the triangle
inequality is the subadditivity of the increasing concave function h
with h(0)=0; if it lies outside, one of the incident distances is at least
the direct distance and monotonicity suffices. Repeated application along
the path proves (29). Hence the full tour has width cost at least
\(2h(|d_i|)\).

If a primary axis were feasible on edge i, sum its boosted estimate (17)
with (28) on the six other edges. The shared marker cancels exactly,
and (29) gives

\[
\begin{aligned}
 \frac{197}{200}+6\frac{8833}{10000}
 &<\sum_j\phi_j+\beta h(d_i)-\beta\sum_{j\ne i}h(|d_j|)\\
 &\le2\pi.
\end{aligned}
\tag{30}
\]

But

\[
 \frac{197}{200}+6\frac{8833}{10000}-\frac{710}{113}
 =\frac{114}{70625}>0,\qquad 2\pi<\frac{710}{113}.
\tag{31}
\]

This contradiction excludes every feasible primary axis, including a
primary axis tied with a secondary one. Therefore every zero-quarter
edge uses only original zero-based axes \(\{0,2\}\).

## 7. Dependency and application boundary

The exclusion uses no tangent cut, no candidate-specific sign pattern,
no mismatch bound S, no quarter-owner theorem, and no nonneighbor
constraint. It applies to any normalized seven-cycle at Q satisfying the
common frame spread and actual G1 pair inequalities. All chart junctions,
original signs, and original feasible axis ties were kept.

It can be applied before the candidate coarse mismatch stage: a chosen
bad original witness can be preserved when the boundary reduction and
radius expansion to Q are made. The frame differences and quarter
increment do not change under that radial process. The common G1 marker
must be selected on this Q-boundary cycle; it must not be silently reused
as a different radial or candidate arc label after changing the ceiling.

The new complete mathematical result is the primary-edge estimate (17)
and its conditional cyclic consequence (30). The full G1 pair theorem,
the first bound on S, and the unrestricted sharp theorem are not proved
by this note. No Lean source, compilation, CI, or certificate table was
changed. Exploratory contact optimization was used to identify the
support cancellation; the proof uses only the displayed whole-domain
inequalities and rational polynomial identities.
