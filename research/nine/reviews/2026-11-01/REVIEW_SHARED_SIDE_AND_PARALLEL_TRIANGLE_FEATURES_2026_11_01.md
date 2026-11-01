# Independent review: complete internal shared-side and parallel-pair exclusions

Reviewed November 1, 2026. The reviewer did not contribute to the four
manuscripts under review. All four proofs were read in full; their geometric
coverage, force signs, complete moments, mean inequalities, actual outside
points, and final scalar bounds were independently reconstructed.

**Verdict: all four pass on their stated original physical domains.** No gap
was found. Their union excludes every no-common-point direct unloaded triangle
with an internal positive-length physical shared side, and every such triangle
with any parallel pair of core frames. Joining the separately reviewed
common-point theorem extends those feature exclusions to the whole direct
triangle domain. This review itself does not re-audit that separate theorem or
close all-pairwise-nonparallel singleton triangles.

## 1. Sources and exact reviewed versions

| Source | SHA-256 |
| --- | --- |
| [Complete notch classification and Type II torque](../../DISTINCT_SHARED_SIDE_TRIANGLE_COMPLETE_NOTCH_CHART_AND_TORQUE_EXCLUSION_2026_11_01.md) | `4dab59e090722540de93da92bd93789c8470494ea9a4a16ce7a8b645f277e381` |
| [Type I strict-side-owner disk exclusion](../../STRICT_SIDE_OWNER_SHARED_SIDE_NOTCH_EXCLUSION_2026_11_01.md) | `04d0df6e9048c49c44b0100bfa9d6cad26f33963ea44581f45edb0679c12cfa3` |
| [Type III strict-normal vertex endpoint](../../DISTINCT_SHARED_SIDE_VERTEX_ENDPOINT_DISK_EXCLUSION_2026_11_01.md) | `c6608f3be445ce0baaaf7dfc3a644107726f4ed75827f45b86ef7a07393d4a43` |
| [Parallel-frame corner-pair exclusion](../../DISTINCT_TRIANGLE_PARALLEL_CORNER_PAIR_EXCLUSION_2026_11_01.md) | `9eb92e073101333758047ad55a967ab3fb6bdc306acbab593d56afd36c77ca67` |

Changes to evidence labels after this review do not alter its mathematical
scope; changes to hypotheses, formulas, or proof steps require comparison
against these reviewed sources.

## 2. Exhaustive shared-side chart, including both corner boundaries

The shared pair can be placed as \(A=[0,1]^2\),
\(B=[1,2]\times[s,s+1]\), \(0\le s<1\), preserving its original mean
\((1,m)\), \(s\le m\le1\). At \(s=0\), a segment in the convex square \(C\)
joining its contacts with \(A\) and \(B\) crosses their common edge, giving a
forbidden actual triple point. Three parallel frames also force a triple
point, by the pairwise interval-intersection property in both coordinates.
Thus \(s>0\), \(C\) is nonparallel, and its two pair intersections are
singletons.

The segment joining those two actual contacts crosses \(x=1\) outside the
shared interval. Choosing the upper notch by the stated symmetry is exhaustive.
If the \(B\)-contact had \(x>1\), the segment immediately after its crossing
would lie in \(\operatorname{int}(B)\), since its height is strictly above
\(1>s\) and below the endpoint height \(\le s+1\). This is incompatible with
its containment in \(C\). The corresponding argument at \(A\) gives
\(p=(x,1)\), \(0\le x<1\), and \(q=(1,y)\), \(1<y\le s+1\).

With the nonparallel frame \(u=(c,h)\), \(v=(-h,c)\), \(c,h>0\), both contacts
lie on the lower-right edge \(P+[0,1]u\) of \(C\). Side-interior normals force
the relevant extremal vertices. At an outer \(A\) or \(B\) corner, the actual
normal lies strictly Northwest: for a singleton vertex/vertex this is the
stipulated strict convention; for a vertex against a nonparallel side it
follows because the side normal has two nonzero components. Its dot product
with \(v\) is strictly positive, so its minimizing support on \(C\) has
\(v\)-coordinate zero. This covers corner-to-side cases as well as strict
vertex/vertex cases.

The possibility \(p=(0,1)\) would give horizontal contact separation one,
exceeding the edge's extent \(c<1\). Hence \(p=P\) is on the relative interior
of \(A\)'s top side. Writing \(q=P+\lambda u\), \(0<\lambda\le1\), gives
exactly the source's three rows:

- \(\lambda=1\), \(h<s\): Type I, \(B\)-side interior.
- \(0<\lambda<1\), \(s=\lambda h\): Type II, \(B\)-corner against the
  relative interior of the \(C\)-edge.
- \(\lambda=1\), \(s=h\): Type III, original strict vertex/vertex endpoint.

There is no omitted finite or angular boundary. A zero separation would be a
triple point, and angular endpoints are parallel frames. Type III correctly
retains its free original strict normal; it is not assigned the West normal
of Type I. Every original shared-side mean \(m\in[s,1]\) remains included.

## 3. Type II: complete torque contradiction

The actual force features force the source's vectors, and complete translation
forces the exit applications to \((0,0)\), \((2,s)\), and \(P+u+v\).
In particular \(E_C\cdot u=ah>0\), \(E_C\cdot v=b+ac>0\), so the last
application is physically compelled.

Expansion of the three original \(B\)-moments gives exactly

\[
 (m-s)t+b(h-c)=0,
 \qquad c\ge h.
\]

At \(C\), the original BC force contributes \(-\lambda b\) about \(P\), and
the original exit contributes \(b+a(c-h)\). Thus

\[
 (1-\lambda)b+a(c-h)=0,
\]

whose left side is strictly positive. This excludes all Type II means and
positive weight ratios without any radius assumption.

## 4. Type I: all exit-support alternatives and the first disk lemma

The retained \(A\)-torque gives \(t/a=(1-c)/\mu<d/(1+c)<1\), so its actual
unit-step point is \((-\alpha,-\beta)\), with \(0<\alpha<\beta\) and unit norm.
The complete \(B\)-exit is horizontal, so its actual unit-step point has first
coordinate three for every original tangent mean.

At \(C\), the sign split of \(ad-bc\) is exhaustive. Independent torque
expansion gives, in order, \(b(c-d)=ad\), \(a(c-d)+bc=0\), or the retained
side-mean equation \(\tau=d^2\). The corresponding actual unit-step points
all satisfy \(w_x\le1\), \(w_y>0\), and \(w_y-w_x\ge3\). The first two
cases use \(2c+d\ge2\) or its symmetric counterpart and the stated radical
comparison. In the mean case the exact difference is

\[
 \frac{h(7-h^2)}2
 =3+\frac{(h-1)(2-h)(h+3)}2\ge3,
 \qquad h=c+d\in[1,\sqrt2].
\]

The three-point disk lemma was also independently expanded. Its obstruction is

\[
 F=-13+\frac{11}{3}(\alpha+\gamma)+\alpha^2+2\gamma^2
       +2\beta\delta+\delta^2.
\]

The auxiliary bound \(K\ge2\) follows from
\(\beta\ge1-\alpha^2\) and \(\alpha\le1/\sqrt2<11/15\).
For \(0\le\gamma\le3\), the exact remaining quadratic is
\(3(\gamma-13/18)^2+47/108>0\). The \(\gamma\le0\) and \(\gamma\ge3\)
branches give the stated positive bounds two and sixteen. The midpoint
argument can safely square its horizontal lower bound because
\(D\ge5/2>25/12\). Thus the complete Type I result \(R>25/12\) is valid,
including all original exit means and all closed scalar boundaries.

## 5. Type III: strict original normal and the endpoint disk lemma

Normalizing the positive BC horizontal magnitude is legitimate. Its original
strict normal is \((-1,k)\), with \(k>0\) and \(C_0-kS>0\). Complete \(A\)
and \(B\) torques give exactly

\[
 t\mu=a(1-C_0),\qquad k-1=t(\mu-S)\ge0.
\]

Hence \(k\ge1\) and \(C_0>S\). At \(C\), both strict-sign exit alternatives
have the stated impossible moment equations. The surviving zero-component
case keeps the original side mean and forces

\[
 a=C_0/S-k,\qquad F=v/S,\qquad
 \lambda=S^2+kSC_0\in(0,1).
\]

The original mean bounds \(S\le\mu\le1\) produce
\(\alpha<5/13<2/5\), \(w_{B,x}>27/10\), \(t<1/2\), and \(k<3/2\).
The actual \(C\)-point is precisely \(P+2v+\lambda u\). Its horizontal bound
reduces to
\(-\tfrac12S(3S^2-3S+1)<0\). Its vertical bound follows from the exact squared
difference \(S^3(4-3S-2S^3)>0\), giving \(w_{C,y}>3\). These inequalities
retain every permitted original mean and strict-normal parameter.

For the endpoint disk lemma, independent expansion gives

\[
 F=-\frac{371}{25}+\frac{37}{15}(\alpha+g)+\alpha^2+2g^2
       +2\beta d+d^2.
\]

Using \(d\ge3\), \(\beta\ge1-\alpha^2\), and \(\alpha\le2/5\) yields the
claimed uniform lower margin \(F\ge4/25>0\). Here
\(D\ge27/10>25/12\), so the midpoint argument again has the required positive
horizontal sign. Thus all Type III endpoints satisfy \(R>25/12\).

Both disk theorems exceed the target at the exact margin
\(625/144-1105/256=55/2304>0\). Together with Type II and the exhaustive
chart, they exclude the entire no-common-point internal shared-side feature.

## 6. Parallel corner pairs: complete chart and actual diameter

A parallel point-only pair has the stated diagonal-corner chart. The third
square is nonparallel by the interval-intersection argument. Its joining
contact segment must occupy one of the two open notches; choosing the Southeast
one forces contacts \((x,0)\), \((0,-y)\) with \(x,y>0\).

For the frame \(u=(c,h)\), \(v=(h,-c)\), every permitted support at either
contact lies on \(L+[0,1]u\). At an outer corner, the Southeast normal has
strictly positive dot product with \(v\), including a vertex against a
nonparallel side; the original strict convention supplies the same conclusion
at a vertex/vertex singleton. The edge extents \(c,h<1\) rule out \(x=1\)
and \(y=1\). Thus both original contacts are forced side-interior contacts,
and the entire actual chart reduces to \(q=L=(0,-h)\), \(p=L+u=(c,0)\).

The original strict SW normal on AB and complete translations force outside
applications \((1,1)\), \((-1,-1)\), with strictly NE and SW outside vectors.
The actual unit-step points have squared separation

\[
 8+4(\alpha+\beta+\gamma+\delta)
      +(\alpha+\gamma)^2+(\beta+\delta)^2>18.
\]

Both strict inequalities used here follow from positive components and unit
norm. The original disk diameter gives \(R^2>9/2\), uniformly over every
outside frame, application mean, and terminal identity. No torque equation
is modified; this contradiction simply does not need the retained moments.

## 7. Union and limits of adoption

All constructed outside points are actual points of the unchanged original
outside squares: adding a unit normal to an original minimum-support point
moves each nonzero own-coordinate component inward by at most one; a zero
component preserves its original mean. Repeated terminals therefore cause no
exception. Every original full core star and all other actual squares remain.

The reviewed union closes the whole no-common-point shared-side family and
the whole no-common-point parallel-core-pair family. After joining the separate
common-point exclusion, any surviving unloaded direct triangle must have
pairwise nonparallel core frames and three physical singleton intersections.
It does not follow that this remaining family is infeasible, that all original
callers have been joined, or that any canonical parent count changes without
the corresponding original-domain adoption.
