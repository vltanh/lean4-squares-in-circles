# Refined five-square fan: a 1/5 upper-cap cutoff

Research continuation, 2026-10-12. This is a strict strengthening
of [HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md).
The earlier note excluded \(h_U\ge21/100\); the present fully
analytic argument lowers that to \(h_U\ge1/5\). The five
square frames are arbitrary and independent, and no contact
graph or numerical parameter mesh is assumed.

## Improved five-square theorem

Suppose five **distinct** pairwise interior-disjoint unit
squares fit in a disk of squared radius \(R^2\le9789/2500\).
Three lie wholly beyond the right side \(x\ge h_R\),
and two other squares lie wholly beyond the perpendicular
upper side \(y\ge h_U\), with
\[
\boxed{h_R>17/200,\qquad h_U\ge1/5.}
\]
Suppose exactly two of the three right-cap squares have
center norm \(<1\), the third has center norm \(\ge1\),
and both upper-cap squares have center norms \(<1\).

**Conclusion:** these five square labels cannot coexist.

A "whole cap" means actual whole-square containment
beyond its supporting line, not just a center-coordinate
sign. Neither an actual contact nor a common square
orientation is assumed.

## 1. Stronger mixed inner/outer angular gap at radius >117/200

Every center radius obeys
\[
r^2+r+1/2\le9789/2500,
\qquad r<283/200,
\]
by the exact farthest-vertex square formula and the
orientation-independent inequality \(L\ge1\).

**Claim.** Let two distinct packed square centers have
radii \(117/200<r<1\) and \(1\le s<283/200\).
Then their smaller angular gap satisfies
\[
\boxed{\delta>311/500\ {\rm radians}.}           \tag{1}
\]

To prove this, put \(x=311/500\).
The exact alternating Taylor bound for cosine gives
\[
\cos x\ge1-x^2/2+x^4/24-x^6/720
>13/16,
\]
with strict rational difference
\[
2409818510486639/11250000000000000000>0.
\]
For \(\delta\le x\), the cosine law would imply
\[
|p-q|^2
<r^2+s^2-(13/8)rs.
\]
This quadratic is convex separately in r and s.
Its four corner values on
\([117/200,1]\times[1,283/200]\) are exactly
\[
979/2500,\quad319781/320000,\quad
3/8,\quad14057/20000,
\]
all strictly less than one. But the disjoint
inscribed radius-\(1/2\) disks of the two unit
squares require \(|p-q|\ge1\).
Contradiction, proving (1). No sampled angular
minimum is involved.

The prior mixed lemma in
HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md also proves
that an inner center of radius \(>7/10\) and an
outer center in the search disk have angular gap
**strictly greater than \(2\pi/9\)**.

## 2. An exact angle comparison at upper offset 1/5

Let
\[
\alpha:=\arcsin(h_U+1/2)\ge\arcsin(7/10).
\]
We prove the exact inequality
\[
\boxed{4\pi/9-\alpha<311/500.}                \tag{2}
\]
Indeed \(\pi<22/7\) implies
\[
4\pi/9-311/500
<88/63-311/500=24407/31500
<31/40.
\]
The latter difference is \(11/63000>0\).
For \(z=31/40\), the alternating sine
Taylor inequality gives
\[
\sin z\le z-z^3/6+z^5/120<7/10,
\]
with exact final rational margin
\[
7/10-[z-z^3/6+z^5/120]
=3082849/12288000000>0.
\]
Since \(z\in(0,\pi/2)\), sine is increasing,
so \(z<\arcsin(7/10)\le\alpha\).
Combining the bounds yields
\(4\pi/9-\alpha<311/500\), as claimed.

## 3. Four inner rays leave no room for a right-cap outer ray

Name the inner right-cap centers \(R_-,R_+\)
by their negative/positive y signs, and
the inner upper-cap centers \(U_+,U_-\)
by their positive/negative x signs.
Both opposite-sign claims follow from the
arbitrary-frame inner-center cap theorem
HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md.
The usual separation of two inner-center rays
by \(>\pi/3\), combined with the distinct
whole-cap labels, forces their ordered angles
to satisfy
\[
-\pi/3<\theta_{R_-}<-\alpha,\quad
0<\theta_{R_+}<\pi/3-\alpha,
\]
\[
\pi/3<\theta_{U_+}<2\pi/3-\alpha.              \tag{3}
\]
These are the same four-inner fan inequalities
proved in HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md;
they remain valid for \(\alpha\ge\arcsin(7/10)\),
without requiring \(\alpha>\pi/4\).

**The two mixed large-angle witnesses.**
The \(U_+\) inner radius is \(>7/10\):
its y projection is \(\ge h_U+1/2\ge7/10\)
and its x coordinate is strictly positive.
For \(R_-\), the x projection exceeds
\(h_R+1/2>117/200\), and (3) gives
\[
|p_{R_-}|>(117/200)/\cos\alpha
\ge(117/200)/\sqrt{51/100}
>7/10.
\]
The final inequality is an elementary
positive rational square comparison.
Therefore the independent mixed-radius theorem
applies to both \(R_-\) and \(U_+\) with
gap \(>2\pi/9\).

Write \(\psi\) for the **outer** right-cap
center's polar angle. Its x center
projection is \(>117/200\), while its
radial norm is \(<283/200\). Hence
\(\cos\psi>117/283>2/5>\cos(3\pi/8)\),
so
\[
-3\pi/8<\psi<3\pi/8.                         \tag{4}
\]

The outer ray cannot lie below \(R_-\):
then (3)–(4) would give angular gap
\(<3\pi/8-\alpha<5\pi/24<2\pi/9\),
since \(\alpha>\pi/6\).
It also cannot lie above \(U_+\):
that gap would be \(<3\pi/8-\pi/3
=\pi/24<2\pi/9\).
Thus the \(>2\pi/9\) separations force
\[
-\pi/9
<\psi
<4\pi/9-\alpha
<311/500.                                      \tag{5}
\]

The remaining inner R+ center satisfies
\[
|p_{R_+}|>h_R+1/2>117/200,
\qquad
0<\theta_{R_+}<\pi/3-\alpha.
\]
If \(\psi\ge\theta_{R_+}\), their angular
gap is \(<\psi<311/500\) by (5).
If \(\psi<\theta_{R_+}\), their angular
gap is
\[
<(\pi/3-\alpha)+\pi/9
=4\pi/9-\alpha<311/500.
\]
Both contradict the sharpened mixed
inner/outer separation bound (1).
This proves the improved five-square theorem. QED.

## New remaining S3/k=3 region

In the exclusive one-side S3=(3+1,2+1)
branch, normalize side populations to
R=3,L=1,U=2,D=1.
With **exactly k=3 outer exterior centers**,
the far L and D singleton squares are outer,
the R triple has exactly one outer and two
inner members, and both U members are inner,
with five distinct R/U labels.
The far L cap envelope gives \(h_R>17/200\);
the two-outer triple theorem gives
\(h_R<13/100\), as before.

The new five-square theorem excludes **all**
\(h_U\ge1/5\). Therefore S3/k=3 must satisfy
\[
\boxed{
17/200<h_R<13/100,\qquad
17/200<h_U<1/5.                                \tag{6}
}
\]

The far D singleton lies wholly beyond its
opposite cap at offset \(1-h_U>4/5\).
By the sharp arbitrary-orientation one-square
cap envelope, for its transverse center x,
\[
(|p_D.x|+1/2)^2
<9789/2500-(9/5)^2=1689/2500
<(33/40)^2,
\]
where the last exact squared difference
is \(201/40000>0\). Hence
\[
\boxed{|p_D.x|<13/40.}                          \tag{7}
\]
Since \(-p_D.y>3/2-h_U>13/10\),
its polar ray lies within
\(\arctan(1/4)\) of the negative y axis.
The previous far L singleton transverse bound
\(|p_L.y|<3/20\) is retained.

The sole R-outer angular two-sector classification
in HUMAN_S3_K3_REMAINING_TWO_LANES.md is
also retained: neither sector is proved feasible,
and no full S3/k=3 exclusion is claimed.

## Scope

This result is **continuous-region pruning**, not a
proof of the global eight-square optimality theorem.
S3/k=3 remains open in its smaller offset rectangle;
other S3, S2, S1, S4, D1 and D2 branches remain open.
The actual S4/k=7 candidate equality configuration
is unaffected. No Lean formalization is claimed.

[verify_five_square_fan_refined.py](verify_five_square_fan_refined.py)
audits the exact rational Taylor and cap-envelope margins.
