# A hand elimination of outward separating axes

This note contains an analytic lemma for the boundary-pair hand conversion.
It does not use the existing interval certificates. The coordinate conventions
are the same as those in `verify_fourtype_pairs.cpp`.

## 1. A unit square in a circular cap

**Lemma.** Let a unit square lie in the disk of squared radius \(Q\). If
every point of that square satisfies \(n\cdot x\geq h\), where \(n\) is a
unit vector and \(h\geq0\), then

\[
Q\geq(h+1)^2+\frac14.
\tag{1}
\]

Choose the square's orthonormal edge vectors so that
\(c=n\cdot e\geq s=n\cdot f\geq0\). Thus \(c^2+s^2=1\).
If its least \(n\)-projection is \(h'\geq h\), the midpoint \(m\) of
its farther edge parallel to \(f\) has

\[
n\cdot m=h'+c+\frac s2\geq h+1,
\]

because
\((c+s/2)^2=1+cs-3s^2/4\geq1+s^2/4\geq1\).
The two endpoints of that edge have mean squared norm
\(|m|^2+1/4\), which is at least \((h+1)^2+1/4\).
At least one endpoint therefore has that squared norm or more, proving (1).

In particular, for \(Q\leq98/25\), a unit square cannot lie beyond a
line at distance \(11/12\) from the origin: such a square would require

\[
Q\geq\left(\frac{23}{12}\right)^2+\frac14
=\frac{565}{144}>\frac{98}{25}.
\tag{2}
\]

## 2. Application to boundary states

Write a source state in its own frame as \((a,-at)\), and a target state
in its own frame as \((b,-bu)\), with \(|t|,|u|\leq1\).
Every core or outer boundary state used here has \(a,b>1/2\).
For core states, \(a=7/12\) on the side branch, whereas on the corner
branch \(a\geq1/2+1/(12\sqrt2)>1/2\). For outer states
at \(Q\geq5/2\), the minimum \(a\) is attained at \(|t|=1\), where
\(a=\sqrt{Q/2}-1/2>7/12\).

The eight signed separating axes, in the verifier's order, are

| Index | Signed projection of target centre minus source centre |
|---:|---|
| 0 | source \(+e\) |
| 1 | source \(+f\) |
| 2 | target \(+e\) |
| 3 | target \(+f\) |
| 4 | source \(-e\) |
| 5 | source \(-f\) |
| 6 | target \(-e\) |
| 7 | target \(-f\) |

A separation in source \(+e\) would put the whole target square beyond
the source face at distance \(a+1/2>1>11/12\), contradicting (2).
A separation in target \(-e\) gives the same contradiction with the two
squares interchanged. **Axes 0 and 6 are therefore impossible for every
boundary pair.**

If \(a|t|\geq5/12\), the source's outward secondary face has distance
at least \(11/12\), so its outward secondary separation is also impossible.
The same reasoning applies to the target. In signed-axis notation:

| Additional condition | Impossible axis |
|---|---:|
| \(t>0,\ at\geq5/12\) | 5 |
| \(t<0,\ -at\geq5/12\) | 1 |
| \(u>0,\ bu\geq5/12\) | 3 |
| \(u<0,\ -bu\geq5/12\) | 7 |

## 3. Simple rational thresholds

Set \(v=|t|\) and \(b_0=va\). On the outer boundary,

\[
(a+1/2)^2+(va+1/2)^2=Q,
\qquad
\frac{d(va)}{dv}
=\frac{a(a+1/2)}{(a+1/2)+v(va+1/2)}>0.
\tag{3}
\]

For every squared radius used in the completed route,
\(Q\geq Q_* > 281/72\). At \(v=1/3\), substituting
\(a=5/4\) gives

\[
(a+1/2)^2+(va+1/2)^2
=\left(\frac74\right)^2+\left(\frac{11}{12}\right)^2
=\frac{281}{72}<Q.
\]

Consequently the actual outer value satisfies \(a>5/4\), hence
\(va>5/12\). By (3), **every outer state with \(|t|\geq1/3\)**
satisfies the extra outward-secondary exclusion.

On the core side branch, \(a=7/12\), so \(va\geq5/12\) exactly when
\(v\geq5/7\). At the corner transition \(v=6/7\), one has
\(va=1/2\). On the core corner branch,

\[
(a-1/2)^2+(va-1/2)^2=\frac1{144},
\qquad
\frac{d(va)}{dv}
=\frac{a(a-1/2)}{(a-1/2)+v(va-1/2)}>0.
\tag{4}
\]

Thus **every core state with \(|t|\geq5/7\)** also satisfies the
extra exclusion. In particular, all outer states of four-type class 3
already do; class 2 may be split once at \(1/3\), and the core class once
at \(5/7\). These are exact geometric reductions of the remaining
continuous pair inequalities, independent of any fitted state potential.

### Radius scope

The first two sections hold for \(5/2\leq Q\leq98/25\).
The outer threshold \(1/3\) in section 3 additionally uses
\(Q>281/72\), which holds both at the coarse ceiling \(9789/2500\)
and at the isolated sharp ceiling used for the completed captures.
The latter statement uses the existing exact isolated-root bound; no
claim is made for smaller arbitrary radii.
