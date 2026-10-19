# Forced angular lanes for the all-single-side S1 / k=3 branch

Research continuation, 2026-10-12.
This sharpens the *continuous center-direction order* in
the remaining exact S1=(3+0,3+1) branch when exactly three
exterior centers have norm >=1. No circle-contact graph,
square parallelism, or selected inter-exterior separator
is assumed.

## Theorem

Let eight pairwise interior-disjoint unit squares fit in
\(D_R\), \(R^2\le9789/2500\), and let C denote the
unique central origin-containing square.
Suppose every noncentral square has **exactly one**
central-owned whole-square side status, of type
S1=(3+0,3+1). By reflecting/rotating, let
\[
N_R=3,\quad N_L=0,\quad N_U=3,\quad N_D=1,
\]
where each exterior square occurs in precisely one
population. Suppose exactly \(k=3\) exterior centers
have norm \(\ge1\), the others having norm \(<1\).

Then there are **four distinct inner-center squares**
whose center-ray angles, measured counterclockwise
from the positive x-axis and represented in \((-\pi,\pi]\),
obey the compulsory strict lanes

| Inner label | Whole central-side status | Center angle |
| --- | --- | --- |
| \(R_-\) | R | \(-\pi/3<\theta_{R_-}<-\pi/6\) |
| \(R_+\) | R | \(0<\theta_{R_+}<\pi/6\) |
| \(U_+\) | U | \(\pi/3<\theta_{U_+}<\pi/2\) |
| \(U_-\) | U | \(2\pi/3<\theta_{U_-}<5\pi/6\) |

Their **three successive gaps** satisfy
\[
\theta_{R_+}-\theta_{R_-}>\pi/3,\qquad
\theta_{U_+}-\theta_{R_+}>\pi/3,\qquad
\theta_{U_-}-\theta_{U_+}>\pi/3.                 \tag{1}
\]
In particular, the two distinct NE inner centers
\(R_+,U_+\) lie on **opposite sides of the
45-degree diagonal**, at angles below 30 degrees
and above 60 degrees, respectively.

These are necessary angular lanes; they are not
a realizability assertion for a full packing.

## Proof

The D singleton has whole-square cap offset
\(h_D=1-h_U>17/24>1/2\), by the sharp
three-square cap theorem applied to U. Every
square wholly beyond a cap offset \(\ge1/2\)
has a center norm \(\ge1\), by the normal
projection bound \(n\cdot p\ge h+1/2\).
Thus D is **outer**.

The R triple and U triple each have at least
one outer center by the three-inner-center cap
theorem in HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md.
Because the seven statuses are exclusive
single-side, these are three distinct
outer labels. Since the assumption is
*exactly* \(k=3\), each of the R and U
triple populations has **exactly one**
outer center, leaving **exactly two inner**
centers in R and two in U.

Apply the arbitrary-frame two-inner-center
cap lemma
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md).
In each cap the two inner center rays have
angular separation \(>\pi/3\) and their
transverse center coordinates have **opposite
strict signs**.

For the two R inner centers, since their
whole squares are contained in \(x\ge h_R>0\),
the center x coordinates exceed \(h_R+1/2>1/2\).
With norms \(<1\), their angles lie in
\((-\pi/3,\pi/3)\). Their opposite transverse
signs give
\[
-\pi/3<\theta_{R_-}<0<
\theta_{R_+}<\pi/3.
\]
For the two U inner centers,
\[
\pi/6<\theta_{U_+}<\pi/2<
\theta_{U_-}<5\pi/6.
\]

Now \(R_+\) and \(U_+\) are **different square
labels**, both with centers in the open NE quadrant
and norm \(<1\). Their smaller angular gap
must be \(>\pi/3\). The reverse ordering
\(\theta_{R_+}>\theta_{U_+}\) could give
a gap of at most \(\pi/3-\pi/6=\pi/6\),
which is impossible. Thus
\[
\theta_{U_+}-\theta_{R_+}>\pi/3.
\]
Since \(\theta_{U_+}<\pi/2\), it follows that
\(\theta_{R_+}<\pi/6\). Since
\(\theta_{R_+}>0\), it also follows that
\(\theta_{U_+}>\pi/3\).

The R pair gap \(>\pi/3\) now forces
\[
\theta_{R_-}<\theta_{R_+}-\pi/3<-\pi/6.
\]
Likewise the U pair gap \(>\pi/3\) forces
\[
\theta_{U_-}>\theta_{U_+}+\pi/3>2\pi/3.
\]
All four stated strict lanes and (1) follow.
QED.

## Consequences and limitations

This is a **center-ray, not whole-quadrant,
classification**. For instance, an R_+ square
whose center lies in the NE quadrant need not
lie wholly in that origin quadrant; do not
promote center signs to central-owned cap status.
No square frame is forced to be parallel.

The exact angular gaps and upper/lower cap
center projections can be combined with
mutual square separators and the central
square's location in a future sharp S1/k=3
inequality. They do **not** by themselves
exclude S1/k=3, give a universal contact
graph, or establish \(R_8\ge\widehat R\).
