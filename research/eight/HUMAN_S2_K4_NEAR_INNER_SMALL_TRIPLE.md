# The exclusive S2/k=4 near-inner branch forces right triple offset <1/10

Research continuation, 2026-10-12. This removes a full
**continuous offset region** from the remaining S2/k=4
problem, by combining actual angular order among the outer
centers with the third inner right-cap square.

## Theorem

Let eight independently oriented unit squares with
pairwise disjoint open interiors fit in a disk of
squared radius \(R^2\le9789/2500\).
Assume they have exclusive all-seven-single-side
statuses S2=(3+0,2+2), normalized as
\[
R:3,\ L:0,\ U:2,\ D:2,
\]
with U the *nearer* of the opposite U,D two-member
whole-square caps and offset \(h_U\).

Suppose **both** U-square centers are inner
(radial norm <1). Then:
\[
\boxed{\text{the triple-side whole-cap offset }0<h_R<1/10.} \tag{1}
\]

By HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md the same hypotheses
already imply exactly **two outer-center R squares, one
inner-center R square, two inner-center U squares,
and two outer-center D squares** (hence k=4).
The new assertion excludes the entire \(h_R\ge1/10\)
continuous subregion, not the remaining \(0<h_R<1/10\)
branch. No orientations or physical contacts are prescribed.

## 1. Exact auxiliary mixed-center angular separation

Let \(r\in[3/5,1)\) and \(s\in[1,283/200)\)
be norms of centers of two distinct packed unit squares.
The smaller angular separation must satisfy
\[
\boxed{\delta>631/1000\ {\rm radians}.}             \tag{2}
\]
This statement uses only the mutual unit-distance
condition of the inscribed radius-1/2 disks.

For \(x=631/1000<1\), the standard alternating
cosine Taylor inequality gives
\[
\cos x\ge1-x^2/2+x^4/24-x^6/720>803/1000.        \tag{3}
\]
The final strict rational difference is exactly
\[
\frac{3194884125544152719}{720000000000000000000}>0.
\]
Thus if \(\delta\le x\), the cosine law implies
\[
|p-q|^2=r^2+s^2-2rs\cos\delta
<r^2+s^2-\frac{803}{500}rs.
\]
This final expression is convex in each radius
separately, so its maximum over
\([3/5,1]\times[1,283/200]\)
occurs at one of the four corners.
In the order \((3/5,1),(3/5,283/200),
(1,1),(1,283/200)\), those exact values are
\[
991/2500,\quad998731/1000000,\quad
197/500,\quad145947/200000.
\]
All are strictly below one. This contradicts
center distance \(\ge1\), proving (2). QED.

The angular constant is deliberately rational.
No numerical square-frame or center optimization
is a premise of the theorem.

## 2. The four outer rays leave two gaps too short

For the opposite 2+2 pair, the signed cap theorem
gives
\[
7/24<h_U<1/2,
\]
and both U centers are inner. The farther D cap
has two outer centers. There are exactly two
R outer centers and one R inner center by the
preceding
HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md theorem.

Let the two D outer ray angles be
\(\phi_1<\phi_2<0\), and the two R outer angles
be \(\psi_1<\psi_2\).
The all-frame angular theorem in that note gives
\[
-\pi+\beta<\phi_1<\phi_2<-\beta,\qquad
\beta>\pi/4+7/50,
\]
where D centers are strictly below the x axis;
the exact outer-outer minimum angle
\(\delta_0=\pi/4-1/500\) gives
\[
\phi_2>\phi_1+\delta_0>-\pi+\beta+\delta_0.
\]
All R outer rays lie strictly above \(\phi_2\), and
\[
-\pi/4+17/125<\psi_1<\psi_2<7\pi/36.
\]
In addition their gap \(\psi_2-\psi_1>\delta_0\).

Define the rationally bounded angular width
\[
W:=4\pi/9-17/125.
\]
The previous inequalities give **both**
\[
\psi_1-\phi_2<W,\qquad
\psi_2-\psi_1<W.                                  \tag{4}
\]
For the first, substitute
\(\psi_1<7\pi/36-\delta_0\) and
\(\phi_2>-\pi+\beta+\delta_0\);
for the second use the bounds on
\(\psi_1,\psi_2\).

The crucial elementary exact margin is
\[
W<4(22/7)/9-17/125
=\frac{9929}{7875}
<\frac{631}{500}=2(631/1000),                    \tag{5}
\]
where the last rational difference is
\[
631/500-9929/7875=37/31500>0.
\]
This uses only \(\pi<22/7\).

## 3. There is no angular location for the inner R square

Suppose contrary to (1) that \(h_R\ge1/10\).
Let \(Q\) denote the **remaining inner-center**
R-square and let \(\theta\) be its center-ray
angle. Its whole-square R membership gives
\[
p_Q.x\ge h_R+1/2\ge3/5.
\]
Its radial norm satisfies \(3/5\le|p_Q|<1\),
and therefore
\[
-\beta_0<\theta<\beta_0,\qquad
\beta_0:=\arccos(3/5)=\arcsin(4/5).              \tag{6}
\]
The D uppermost outer ray has
\(\phi_2<-\beta<-\beta_0\); hence
\[
\boxed{\theta>\phi_2.}                            \tag{7}
\]

Apply the exact mixed-radius angular lemma (2)
to Q and **every** D or R outer center.
Since the relevant ordinary angular gaps are
less than \(\pi\), Q must be more than
\(631/1000\) radians from each of
\(\phi_2,\psi_1,\psi_2\).
There are three mutually exclusive positions:

* **Between \(\phi_2\) and \(\psi_1\).**
  Their total gap would exceed
  \(2(631/1000)\), contradicting (4)–(5).
* **Between \(\psi_1\) and \(\psi_2\).**
  The same contradiction applies.
* **Above \(\psi_2\).**
  Since \(\psi_2>67/500\) by the previous
  outer-polarity theorem, (2) gives
  \[
  \theta>\psi_2+631/1000>
  67/500+631/1000=765/1000>0.                 \tag{8}
  \]

In the last case, consider the **positive-x inner**
U member \(U_+\). The two U inner centers
straddle the vertical diameter and have their
own mutual angle gap \(>\pi/3\); since
\(h_U>7/24\), its ray angle \(\theta_{U_+}\)
satisfies
\[
\pi/4<\theta_{U_+}<5\pi/12.                     \tag{9}
\]
But the inner R square's ray is
\(\theta\in(765/1000,\beta_0)\),
with \(\beta_0<\pi/2\).
The two angles in (8)–(9) have
**ordinary difference strictly less than \(\pi/3\)**:
if \(\theta\le\theta_{U_+}\),
the difference is \(<5\pi/12-765/1000<\pi/3\)
because \(765/1000>\pi/12\);
if \(\theta>\theta_{U_+}\),
the difference is \(<\pi/2-\pi/4=\pi/4<\pi/3\).

This contradicts the inner-inner center-ray
separation theorem: two distinct centers of
radial norm <1 and mutual distance \(\ge1\)
must have angular gap **strictly greater**
than \(\pi/3\).

All three possible center-ray positions for Q
are impossible. Thus \(h_R<1/10\), proving (1).
QED.

## Pruning result, honest scope and next gate

The exclusive S2 branch with **both** nearer U cap
centers inner is now restricted to
\[
\boxed{k=4,\quad 0<h_R<1/10,}
\]
with the two outer R squares forced into strict
opposite transverse angular lanes from
HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md.

This is **not** a complete exclusion of S2/k=4:
the small-offset \(h_R<1/10\) sector is still
possible under the known necessary conditions,
and S2 with one or two *outer* U centers
has different outer-count patterns.
All actual square frames and inter-exterior
separating axes remain unfixed.

The S4/k=7 equality construction and the
unrestricted \(R_8\ge\widehat R\) lower-bound
goal are unaffected.
