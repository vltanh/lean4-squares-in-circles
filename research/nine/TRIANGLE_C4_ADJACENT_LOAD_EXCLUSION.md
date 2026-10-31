# A triangle attached to a four-cycle has no adjacent two-load block

**Status: complete hand whole-load-orbit exclusion; root and separate
independent full hand audits passed.** Work with the common
selected physical certificate in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1<\frac{61}{60},\qquad
 \delta=d-1<\frac1{60}.
\tag{1}
\]
The exact positive component has edges
\[
                  HA,AB,BC,CH,HX,XY,YH.
\tag{2}
\]
The block loads are exactly A,B: C has zero circle weight and exact
positive degree two. A,B,X,Y are loaded with exact positive degree two.
The common root H is physically circle-clear and has its true positive
degree four. These are the complete adjacent-load premises established
in TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md. All three other physical
packing squares remain present and arbitrary.

**Theorem.** The whole adjacent-load orbit AB, including its reflected
BC image, is impossible. Every physical circle mask, individual zero
circle-corner weight, actual shared-side mean and contact owner is
retained. No new point-normal choice or secondary minimizer is used.

## 1. The actual unit channel and its transverse bypass

The unloaded degree-two square C transmits one positive force of
magnitude \(\lambda\) between H and B. The unit A physically touches
both endpoints H,B. UNIT_BYPASS_NORMAL_CHANNEL.md therefore gives
reserve exactly one and the complete transverse separation of A,C.
Rotate and, if needed, reflect so that the channel direction is
\(e=e_x\) and A lies above C. Write the actual channel applications
and the actual AH application as
\[
 P=(\alpha,y_0)\in H\cap C,\qquad
 P_B=(\alpha+1,y_0)\in B\cap C,\qquad
 Q\in H\cap A.
\tag{3}
\]
The side-normal transmitter has an actual height interval
\([z,z+1]\), and the full occupied squares satisfy
\[
 \begin{split}
 C&=[\alpha,\alpha+1]\times[z,z+1],\qquad y_0\in[z,z+1],\\
 H&\subset\{x\le\alpha\},\qquad
 B\subset\{x\ge\alpha+1\},\qquad
 A\subset\{y\ge z+1\}.
 \end{split}
\tag{4}
\]
In particular
\[
                 Q_x\le\alpha,\qquad Q_y\ge z+1\ge y_0.
\tag{5}
\]
The original channel mean is retained in (3); neither endpoint is moved
to the center of a side or to a corner.

Every contained unit whose minimum support in a unit direction is h
has \(h\le d\), by the sharp center/half-width bound in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1. Applied to B,
this gives
\[
                           \alpha+1\le d,
                  \qquad\alpha\le\delta.
\tag{6}
\]

Let n be the actual H-to-A unit normal and \(\mu>0\) its magnitude.
Let g be the A-to-B unit normal and \(\gamma>0\) its magnitude.
Write the intact petal resultant as
\[
                 M=F_X+F_Y.
\]
The true equations at A,B and H give
\[
 F_A=\mu n-\gamma g,\qquad
 F_B=\lambda e+\gamma g,\qquad
 M=-(\mu n+\lambda e).
\tag{7}
\]
No extra H force has been omitted: its other two forces are precisely
the two original petal forces whose sum is M.

## 2. The complete bypass-normal sign and the parallel alternative

We first have
\[
                              n_x\ge0.
\tag{8}
\]
Indeed, if \(n_x<0\), the quantitative support-span lemma gives
\[
                   \max_{p\in A}p_x-Q_x\le|n_y|<1.
\tag{9}
\]
It applies at every minimum-n support point Q of A, including every
side mean. For reference, at a vertex at most one inward side axis
has positive x-component; its nonnegative scalar product with n
bounds that component by \(|n_y|\). At an interior side point the
inward normal points strictly left and the tangential interval has
horizontal span at most \(|n_y|\). This is also the full lemma in
HOUSE_MIDDLE_TRIPLE_NONPARALLEL_STAR_EXCLUSION.md, Section 1.
But an actual point of \(A\cap B\) has x-coordinate at least
\(\alpha+1\), while \(Q_x\le\alpha\). This contradicts (9).

If \(n_y<0\), the support inequality for P,Q on H gives
\[
       0\ge n\cdot(P-Q)
          =n_x(\alpha-Q_x)+n_y(y_0-Q_y)\ge0.
\tag{10}
\]
Thus \(Q_y=y_0=z+1\). If \(n_x>0\), it also gives
\(Q_x=\alpha\), so Q=P; the support in (10) prevents H from
having any point of its right support face below P. If \(n_x=0\),
then \(n=-e_y\) and the entire H lies above \(y=y_0\), with the
same conclusion. Since C lies below \(y=y_0\) and to the right
of \(x=\alpha\), the physical HC intersection is the singleton P.
It is a vertex of both squares: P is the upper-left vertex of C
and an endpoint, or the sole vertex, of H's right support face.
The positive HC normal e is a side axis of C and hence is not
strictly exposing at that vertex. This contradicts the selected
point-only vertex/vertex convention. Therefore
\[
               n=e\quad\hbox{or}\quad n_x\ge0, n_y>0.
\tag{11}
\]

The parallel alternative \(n=e\) is entirely impossible. If H
does not own the side axis e, its right support is a single vertex P.
Both positive neighbors A,C then contain P and lie in \(x\ge\alpha\).
The HC contact is a singleton. Its strict-normal convention forces
P to be in the relative interior of C's left side: a C-side endpoint
would again be a forbidden vertex/vertex contact with side-axis normal.
Near P, C therefore occupies the whole open right half-plane. The
two-dimensional square A has interior points arbitrarily near P in
that same half-plane, giving open overlap. Hence H must own e.

In that case \(h_H(-e)=1-\alpha\), and (7) makes the true petal
resultant a positive multiple of \(-e\). The complete end-triangle
axis-resultant theorem, at the actual degree-four H, gives
\[
                 h_H(-e)<\frac{59}{60}.
\]
But (6) gives
\[
                 h_H(-e)=1-\alpha\ge2-d>\frac{59}{60}.
\tag{12}
\]
This excludes every parallel-root mean and feature. We henceforth
retain the full nonparallel alternative of (11).

## 3. The actual root intersection is on the positive petal ray

Let q be the intersection of the two actual H force lines through
Q in direction n and through P in direction e. Equations (5),(11)
give explicitly
\[
 \begin{split}
 b_0&=\frac{Q_y-y_0}{n_y}\ge0,\qquad
 q=Q-b_0n,\\
 a_0&=\alpha-q_x\ge0,\qquad
 P=q+a_0e,\qquad Q=q+b_0n.
 \end{split}
\tag{13}
\]
Thus the root intersection is behind both actual ports. This is
proved from the actual channel and bypass; no triangle-only geometric
lemma is applied to the missing HB edge.

Each true loaded tip A,B has the other as a physical boundary neighbor.
The full all-mask proper-concurrence Lemma 2.1 in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md therefore applies to both.
Their own two pair forces are nonparallel, their concurrence points
\(q_A,q_B\) are positive multiples of their actual circle resultants,
and each concurrence lies behind both actual outward ports. Consequently
\[
 q_A=q+u n,\qquad q_B=q+v e,\qquad
 u\ge0,\qquad v\ge a_0+1>0,
 \qquad q_B-q_A=\ell g,\quad\ell>0.
\tag{14}
\]
The extra one in v is the actual reserve from P to \(P_B\), not a
deleted transmitter. The strict inequality \(\ell>0\) follows because
the two positive radial concurrence rays are distinct. Their boundary
center directions differ by more than forty degrees and each actual
circle resultant is within fifteen degrees of its center direction,
so those resultant directions cannot coincide. This local all-mask
fact is in FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section 1.

Summing the actual origin moments of A,B,C cancels every internal
edge, and every original circle force has zero origin moment. Hence
\[
                 \det(Q,\mu n)+\det(P,\lambda e)=0.
\tag{15}
\]
Since both lines pass through q, (15) gives
\(q=\tau(\mu n+\lambda e)\) for a real \(\tau\). The vectors
n,e are independent, and (7),(14) give
\[
 \begin{split}
 q_A&=(\tau\mu+u)n+\tau\lambda e,\\
 F_A&=\left(\mu+\frac{\gamma u}{\ell}\right)n
                              -\frac{\gamma v}{\ell}e.
 \end{split}
\tag{16}
\]
The positive proportionality of \(q_A\) and \(F_A\), compared in
their e-coefficients, forces \(\tau<0\) because \(v>0\).
Together with (7),(11), this proves
\[
       q\text{ is a positive multiple of }M,\qquad
                  q_x<0,\quad q_y=y_0<0,\qquad M_x<0, M_y<0.
\tag{17}
\]
No concurrence at a radial two-corner tip has been asserted to lie
inside its square. Only its true proper-port relations were used.

## 4. A nonpositive channel height would put the whole petal on a high face

We claim
\[
                               \alpha>0.
\tag{18}
\]
Suppose instead \(\alpha\le0\). If H owns e, its minimum
\(-e\)-coordinate is \(-\alpha\ge0\). In a nonparallel petal,
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md gives its own root concurrence
\[
                         q_0=-t\frac M{|M|},\qquad t>0,
\tag{19}
\]
and each actual petal application p has the proper form
\(p=q_0+a w\), \(a\ge0\), where w is its actual outward H
normal. By (17), \(q_0\) is strictly northeast, so
\(q_0\cdot(-e)<0\). All H points have nonnegative \(-e\)-coordinate.
Thus a is positive and \(w\cdot(-e)>0\) for both petal ports.
Since e is an H side axis, both actual ports lie on its left side,
whose outward support height is \(1-\alpha\ge1\).
For a parallel petal, its common outward normal is \(M/|M|\),
which also has strictly positive \(-e\)-component; the same actual
left-side conclusion holds directly, including coincident means.

If H does not own e, P is its rightmost vertex. Its two inward side
axes can be labeled
\[
 u=(-a,b),\qquad v=(-b,-a),\qquad
 a,b>0,\quad a^2+b^2=1,\qquad
 H=P+[0,1]u+[0,1]v.
\tag{20}
\]
There is no ordering assumption on a,b. By (17),
\[
                  \min_{p\in H}v\cdot p
                    =v\cdot P=-b\alpha-a y_0>0.
\tag{21}
\]
The northeast point \(q_0\) in (19) has negative v-coordinate.
The proper-port relation again forces both actual outward petal normals
to have positive v-coordinate, hence both actual applications lie on
the far-v side of H. Its height is
\[
                           h_H(v)=1-b\alpha-a y_0>1.
\tag{22}
\]
For a parallel petal, its southwest common normal \(M/|M|\) has
positive v-coordinate and gives exactly the same far-side conclusion.

In all cases both original petal applications have been placed on one
actual H side of height at least one. The complete all-mask theorem
END_TRIANGLE_HIGH_FACE_EXCLUSION.md excludes even height \(39/40\).
This contradiction proves (18). Every zero proper-length endpoint
in the nonparallel petal is explicitly excluded by the opposite strict
signs in (19)--(21); none was silently discarded.

## 5. The whole return square exceeds its permitted angular shadow

Combining (6),(18) gives
\[
             0<\alpha\le\delta<\frac1{60},
                   \qquad R>\frac{\sqrt{17}}2.
\tag{23}
\]
Every point of B has x-coordinate at least \(\alpha+1>1\).
The all-frame narrow-cap Lemma 1.1 of
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md therefore gives
\[
                   \angle(e,T)<\beta:=\arctan\frac{13}{20}
                       \qquad(T\in B).
\tag{24}
\]
That lemma only requires the weaker floor \(59/60\), and does not
use a radial-leaf or central-root premise.

Choose any actual point \(T\in A\cap B\), and retain the original
\(Q\in A\cap H\). The loaded square A contains a physical circle
corner, so its unit diameter gives
\[
                  |Q|\ge R-\sqrt2>\frac35.
\tag{25}
\]
Since \(Q_x\le\alpha<1/60\),
\[
          \frac{Q_x}{|Q|}<\frac1{36},
                   \qquad\angle(e,Q)>\arccos\frac1{36}.
\tag{26}
\]
For the full radius domain in (23), every circle-touching unit has
angular shadow strictly shorter than
\[
                              \omega=\arctan\frac{23}{16}.
\tag{27}
\]
This is the local, orientation-uniform Section 2 theorem of
BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md; no seven-cycle premise is
needed for that local statement. Both Q,T are points of the same
circle-touching A, so (24),(27) and the angular metric inequality give
\[
                         \angle(e,Q)<\beta+\omega.
\tag{28}
\]
But
\[
 \tan\beta\tan\omega=\frac{299}{320}<1,
 \qquad \cos(\beta+\omega)=\frac{21}{\sqrt{446665}}>
                      \frac1{36},
\tag{29}
\]
where the final exact comparison is \(756^2=571536>446665\).
Thus \(\beta+\omega<\arccos(1/36)\), contradicting (26),(28).

## 6. Scope of the complete exclusion

The original reserve-one channel, actual bypass contact, genuine
degree-two boundary concurrences and the intact opposite petal supplied
every step. The whole low-radius domain is excluded by (18),(6);
the whole remaining high-radius domain is excluded by Section 5.
Parallel H reactions, all point and shared-side owners, coincident
mean limits and every physical circle mask were retained.

The root H never receives a degree-two equation or a fictitious radial
leaf. In particular no theorem placing H near the circle origin was
assumed. Its support height \(\alpha>0\) was derived from its actual
two blocks and the complete petal high-face theorem.

This excludes the entire AB/BC graph-load orbit of the C4 attachment
inside C2.34.b0, with all three arbitrary other squares still present.
It does not close the opposite-load AC or all-three-load ABC orbit,
the diamond-hub layout, or the whole coarse cell. No square movement,
new normal selection, numerical sample, Lean compilation or CI is used.
