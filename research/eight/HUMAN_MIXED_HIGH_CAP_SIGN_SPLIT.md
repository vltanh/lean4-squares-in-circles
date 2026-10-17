# Mixed inner/outer two-square caps above offset 2/5 have opposite transverse center signs

Research continuation, 2026-10-12. This is a new **all-frame,
all-center-position** continuous-region exclusion in the
remaining exclusive S2/k=4 geometry. It uses the previously
proved mixed-center angular polarity lemma and the sharp
one-square cap envelope. It is **not** a full S2/k=4
or eight-square optimality proof.

## General theorem (no contact assumptions)

Let two distinct unit squares with disjoint open interiors
lie in a disk centered at zero with squared radius
\[
R^2\le9789/2500.
\]
Suppose both *whole* squares lie beyond the same
outward supporting line
\[
\{y\ge h\},\qquad h\ge2/5.
\]
Suppose exactly one of their center norms is below one:
write \(p=(p_x,p_y)\) for the **inner** center (\(|p|<1\))
and \(q=(q_x,q_y)\) for the **outer** center (\(|q|\ge1\)).

Then their transverse center coordinates have
**strictly opposite signs**:
\[
\boxed{p_xq_x<0.}                                \tag{1}
\]

Every square frame may be independently rotated.
This is about *centers* and whole-cap membership,
not the assertion that either whole square occupies
an origin quadrant.

## Proof

If \(h\ge1/2\), an inner center is impossible:
whole-cap containment forces
\(p_y\ge h+1/2\ge1\), contradicting \(|p|<1\).
Thus it suffices to consider
\(2/5\le h<1/2\).

The previously proved all-frame
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
applies because \(h\ge2/5>7/24\).
It establishes, **if both center x coordinates
have the same strict sign**, the bounds
\[
|p_x|<1/4,\qquad |q_x|>7/10.                    \tag{2}
\]

First rule out a zero transverse coordinate.
If \(p_x=0\), the polar inner angle is
\(\theta_p=\pi/2\), and the strict mixed
angular gap \(>3/4\) implies that
\(|\theta_q-\pi/2|>3/4\). Consequently
\[
|q_x|=q_y\tan|\theta_q-\pi/2|
>(h+1/2)\tan(3/4)>(19/24)(9/10)>7/10,
\]
by the same exact tangent bound in the cited
mixed-center lemma. Thus the forthcoming
rectangle argument also applies with
\(p_x=0\), using \(|p_x|\le1/4\).

If instead \(q_x=0\), then \(\theta_q=\pi/2\).
The mixed gap \(>3/4\) forces
\(|\theta_p-\pi/2|>3/4\).
But the inner polar elevation lies
in \((\alpha,\pi-\alpha)\) where
\(\alpha=\arcsin(19/24)>17/20\);
hence its angular deviation from \(\pi/2\)
is \(<\pi/2-17/20<3/4\).
Contradiction. Therefore \(q_x\ne0\).

It remains to exclude same nonzero signs, and
the case \(p_x=0\) as above.
Reflect x if needed so
\[
0\le p_x<1/4,\qquad q_x>7/10.                   \tag{3}
\]

Now invoke the arbitrary-frame sharp
single-square cap envelope in
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md).
For a **whole square** in a cap \(y\ge h\ge2/5\)
with center q it gives
\[
(1+h)^2+(|q_x|+1/2)^2\le R^2\le9789/2500.
\]
Since \(1+h\ge7/5\), we have
\[
(q_x+1/2)^2
\le9789/2500-(7/5)^2=4889/2500
<(7/5)^2.
\]
Therefore
\[
\boxed{7/10<q_x<9/10}.                         \tag{4}
\]

The two cap projections and the inner radial
bound give
\[
9/10\le p_y<1,\qquad q_y\ge9/10.
\]
For q, the universal farthest-vertex radius
bound \(|q|<283/200\) and (4) yield
\[
q_y^2< (283/200)^2-(7/10)^2
=60489/40000
<(123/100)^2,
\]
where the strict rational squared margin is
\[
(123/100)^2-60489/40000=27/40000>0.
\]
Thus
\[
\boxed{9/10\le q_y<123/100}.                   \tag{5}
\]

Together, (3)–(5) imply
\[
|q_x-p_x|<9/10,\qquad
|q_y-p_y|<33/100.
\]
Consequently the distinct square centers satisfy
\[
|q-p|^2
< (9/10)^2+(33/100)^2
=\frac{9189}{10000}<1.                           \tag{6}
\]
The positive strict deficit is
\(811/10000\).

But each actual unit square contains an
open inscribed disk of radius \(1/2\).
Two different unit squares with disjoint
open interiors must have center distance
at least one. Inequality (6) is impossible.

This rules out every same-sign or zero-sign case,
so \(p_xq_x<0\), proving (1). QED.

## Actual n=8 case-queue consequence

In exclusive S2=(3+0,2+2), normalize the
nearer 2+2 cap as U, at outward offset
\(h_U\in(7/24,1/2]\), and the farther as D.
The previously completed
[HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
eliminates the case with **both U centers inner**;
its full S2/k=3 exclusion and the two far-D
outer labels imply the following for **S2/k=4**:
the two U centers are exactly **one inner
and one outer**.

Therefore, for its high-offset subregion
\[
\boxed{\text{S2/k=4 and }h_U\ge2/5,}
\]
the two near-U center x coordinates must have
**strictly opposite signs**, regardless of
the actual square frames or selected contacts.

When \(7/24<h_U<2/5\), this theorem alone
does not exclude same-sign centers. But the
earlier mixed-cap lemma still forces the
\(>3/4\) polar gap and
\(|x_{\rm inner}|<1/4,\ |x_{\rm outer}|>7/10\)
under same strict signs, while the independent
[HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md](HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md)
forces at least one near-side square frame to
deviate by **more than 1/2600 radians** from
the cap-aligned axes. These two statements
have different assumptions and neither
is extrapolated outside its proved scope.

This is **genuine continuous geometric pruning**,
not an exclusion of all S2/k=4 configurations.
No assertion about actual whole-quadrant
membership, the global \(R_8\ge\widehat R\)
bound, or Lean formalization follows.
The sharp S4/k=7 equality case is intact.

[verify_mixed_high_cap_sign_split.py](verify_mixed_high_cap_sign_split.py)
audits the few exact rational square comparisons.
