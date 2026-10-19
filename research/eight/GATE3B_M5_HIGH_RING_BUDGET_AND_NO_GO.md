# Gate 3B.2 / HIGH: exterior orientation budget and a sharp limitation

2026-10-13. This is a full-M5 structural theorem, and an explicit obstruction to charging HIGH's complete-pair surplus to exterior-neighbor widths alone. It is NOT a disk radius exclusion and does not close HIGH.

## Theorem A: every seven-frame tour has an excess-width budget

Let T=pi/2 and h=T/2. M5 means no CLOSED h-window contains more than five of the eight frames theta_i, modulo T. Remove ANY one label c, leaving seven labels O; in a disk application c may be the central square. Set

    z_i=(cos(4 theta_i),sin(4 theta_i)).

No closed semicircle can contain the seven z_i for i in O: otherwise seven original orientations would lie in a closed h-window, contradicting M5. Their convex hull therefore contains the origin in its interior.

For ANY cyclic ordering i_1,...,i_7 of O (not necessarily the angular ordering), put i_8=i_1 and denote actual true-side-normal square-pair support widths by

    w_ij = (1+|cos(theta_i-theta_j)|+|sin(theta_i-theta_j)|)/2.

Then

    sum_k |z_(i_(k+1))-z_(i_k)| >= 4,
    sum_k |sin(2(theta_(i_(k+1))-theta_(i_k)))| >= 2,
    sum_k (w_(i_k,i_(k+1))-1) >= sqrt(2)-1.       (A)

This includes all frame coincidences, orientation boundary ties, and cyclic orders, with no center, separator, radius, or contact assumptions.

### Proof

Discard duplicate points for the perimeter argument. Order the distinct z_i around the unit circle and let Delta_j in (0,pi) be the successive gaps. A gap >=pi would place all the points in the complementary closed semicircle, impossible. The gaps sum to 2pi. The convex-hull polygon has perimeter

    P=2 sum_j sin(Delta_j/2) >= (2/pi) sum_j Delta_j =4,

because sin t >= 2t/pi for 0<=t<=pi/2. Any closed tour through all the points has length at least this perimeter: repeatedly uncross intersecting tour edges using the triangle inequality; a crossing-free tour of points in convex position follows their cyclic order. Coincident points may be inserted at zero cost.

Now |z_i-z_j|=2|sin(2(theta_i-theta_j))|. For t=|sin(2(theta_i-theta_j))| in [0,1], the actual support sum satisfies

    w_ij-1=(sqrt(1+t)-1)/2 >= ((sqrt(2)-1)/2)*t,

by the chord bound for concave sqrt(1+t). Summing proves (A). The lower bound is strict for a fixed finite M5 configuration but admits no uniform improvement. QED.

## Theorem B: HIGH does not force an increased ring budget

Let c=(sqrt(2)-1)/2 and W0=28+15c. Define the full-pair M5 surplus

    E = sum_(i<j) w_ij-W0.

HIGH is E>3/1000. For EVERY beta>0, the proposed uniform implication

    HIGH => sum_ring(w_ij-1) >= (sqrt(2)-1)+beta*E

is FALSE for M5 frame data (without disk constraints).

Take folded word I = L H L H L H L L, h=pi/4, and 0<epsilon<h/8. Set

    x_0=0,  x_i=h-(8-i)*epsilon for 1<=i<=7,
    theta_i=x_i+h*1_(word_i=H)  modulo pi/2.

The folded positions are strictly ordered, and word I is one of the exact bounded-occupancy M5 walks. Every positive epsilon in the stated range gives a genuine M5 orientation multiset.

As epsilon tends to zero, the frames form two limiting phases of size four:

    phase 0: labels 0,1,3,5;
    phase h: labels 2,4,6,7.

Exactly 16 of the 28 pairs cross the two phases, so

    E -> 16c-15c=c >3/1000.

Remove label 0 and use the seven-label cyclic tour

    (1,3,5,2,4,6,7).

Exactly two of its seven consecutive pairs cross the two limiting phases. Thus

    sum_ring(w_ij-1) -> 2c=sqrt(2)-1.

For small positive epsilon, E remains bounded away from zero while the proposed extra beta*E does not; the inequality fails. This construction is exclusively orientation data, NOT a packing in the research disk. QED.

## Consequence for the next gate

The M5-HIGH domain includes arbitrarily close **4+4** two-frame degenerations (unlike LOW, whose earlier complete certificate concerned **3+5** near-cuts). HIGH's W surplus cannot simply be added to the exterior-neighbor width total in a marker budget. A correct closure must use the disk, whole-square separator constraints, or an additional geometric link between the full-pair surplus and the exterior ring.

The genuine equality packing and its sliders are untouched. M5-HIGH, M5, and unrestricted R_8>=R_* remain OPEN. No Lean, CI, or numerical certificate is a premise in these two proofs.
