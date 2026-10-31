# Independent review of the opposite-port inner-circle gap and complete C6 pocket-2 join

Date: October 26, 2026. Reviewer: C6 completion agent.

**Verdict: PASS for both complete saved sources and their stated scopes:**

- RADIUS_TWO_OPPOSITE_PORT_INNER_ARC_GAP.md;
- SIX_CYCLE_REMAINING_CAP_2_CAPACITY_ONE.md.

I read both sources end to end and checked their actual-coordinate,
face-order and full-pocket routing dependencies. I also read the relevant
parts of SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md,
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md and
RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO.md. The sharp full-arc theorem
was separately audited in
REVIEW_RADIUS_TWO_CAP_ARC_SHARP_BOUND_C6_2026_10_26.md, and the
actual channel-2 height theorem in
REVIEW_C6_CHANNEL_2_HEIGHT_C6_2026_10_26.md.

## 1. Complete scalar projection theorem

The domain \(a\ge b\ge1/2,\ a^2+b^2=R^2,\ 79/40\le R\le2\)
is retained, including the weak \(b=1/2\) endpoint. The minimum
of \(a+b\) at fixed R is correctly at \(b=1/2\); its resulting
opposite-port norm bound increases with \(R^2\). This proves
\(0<a-1<t<a\) and the signs of F,G before those signs are used.

At \(g=\Lambda\), the coefficient of a is positive on both signs
of w. Thus replacing a by \(\sqrt{(79/40)^2-(w+1)^2}\) enlarges
the domain without reversing the inequality, even when that
comparison a is smaller than \(w+1\).

I independently differentiated the complete expression and obtained
exactly the U,V formulas in (10). All three ordinary curvature
ranges have the stated signs. In particular:

- On \([-1/2,0]\), the cross term is bounded below by
  \(-1/(2at)\), and the factor multiplying w in V is nonpositive;
  this gives the stated positive V bound without discarding a
  term of the wrong sign.
- On \([0,1/4]\), only nonnegative terms are discarded.
- On \([1/4,\sqrt2-1]\), the positive cross term in U and the
  positive \(K^2w/a^3\) term in V have their correct lower
  denominators and endpoint directions.

The resulting \(U>-1/5,\ V>1/2\), together with \(0<u<3/4\),
give \(f''>19/125>3/20\) throughout the entire interval.
The formulas are smooth across the two joining points.

I reconstructed every displayed curvature reserve from fresh exact
Fraction arithmetic:
\[
 \frac{23186977239}{9440026073120},\quad
 \frac{2611}{23040},\quad
 \frac{331}{13824},\quad
 \frac{59903451}{566100920},\quad
 \frac{20477343}{81746504}.
\]
All agree with the source.

The fixed tangent at \(w=1/8\) uses the correct radical values
\(\sqrt{1054}/20,\sqrt{99}/8,4\sqrt{21}/25\).
All six squared endpoint comparisons in (17) agree independently.
The signs in both derivative enclosures in (19) are correct.
Fresh exact arithmetic reproduces the value reserve
\(265131/625000000\), the lower derivative reserve
\(37584071/84057875000\), and the upper derivative reserve
\(662757413/18038000000\).
Integrating strong convexity gives the stated quadratic minimum
and the strict uniform value \(f>1/2+11/3000\).

At \(g=\pi/2\), the derivative of F with respect to b is negative.
For \(w\le0\), \(a-1<t\) bounds its only positive term.
For \(w\ge0\), the multiplication by the positive at and the
inequality \(2at\le a^2+t^2\) give \(t^2-aw>0\).
On the diagonal, \(w(t+w)/\rho\) increases with w over the full
positive interval. I reconstructed the two final square reserves
\(2993/2000000,\ 1459/1000000\), and the value reserve
\(269/312500\).

Finally, the sign of G gives exactly the stated monotonic or
concave dependence on g. Thus the full projection inequality
holds on every \(g\in[\Lambda,\pi/2]\); it is not a statement
about sampled angles.

## 2. Geometric gap identity

For \(P=(a-1,w)\), \(Q=(t,w)\), the actual dot products are
\[
 P\cdot Q/\rho=F,\qquad P\cdot JQ/\rho=G
\]
in a positively oriented own frame. Reversing that frame reverses
only the G sign. This proves both identities in (24), retaining
the actual application vertices.

For an actual gap centered on the upper vertical, its right
endpoint has unit direction \((\sin g,\cos g)\), while its left
endpoint has \((-\sin g,\cos g)\). Substituting the two
orientation signs gives exactly the horizontal difference in
(25). Therefore \(\Gamma\ge2\Lambda\) would make that
difference greater than one, contrary to the original reserve
\(|P_--P_+|=1\). The strict gap conclusion is valid, provided
the stated actual face and interval-order hypotheses hold.
The generic source correctly leaves those physical hypotheses
to its application rather than asserting arbitrary-subgraph routing.

## 3. Original C6 port coordinates and face order

For the retained original corner word 110 and sole outgoing
share at unit 0, the unchanged incoming unit-0 endpoint is
\((1-a,1-b)\). The original torque/share identity gives
\(a>b>1/2\); no own-axis swap is made to obtain this order.

At unit 2, I independently derived
\[
 f_2\cdot v_2=-\eta K_2,\qquad
 f_1\cdot v_2=\eta(L_2-K_2)
             =p(c_1N+s_1M)>0.
\]
Thus \(L_2>K_2>1/2\) is its actual coordinate ordering.
The stated opposite port
\(z_2+u_2-v_2\) has exactly the own coordinates
\((L_2-1,K_2-1)\) in the frame \((v_2,-u_2)\).
That frame has determinant \(-1\), while the unit-0 frame has
determinant \(+1\).

The lower-small-coordinate face crossings in (11) are actual
interior points of those sides, since \(a-1<t<a\) and the
analogous unit-2 inequalities hold. These are not intersections
with side extensions. The proof needs neither small coordinate
to be at least one.

The channel-height increase from each P to its Q is positive:
both large-axis projections onto the actual outward normal m
are positive. Hence both facing Q points lie above \(H_2>0\)
on the same short outward inner-circle cap.

I checked the complete face-order argument directly. In a
positively oriented own frame, at \(Q=(t,w)\) the derivative
of the small coordinate under counterclockwise circle motion
is \(t>0\). Thus the interior arc begins at Q. In a negatively
oriented frame, the interior arc ends there. This remains true
when w is negative. The two endpoint-center angles have the
actual right-before-left order supplied by the endpoint theorem.
Connected occupied arcs containing those center directions
therefore leave either no interval or exactly
\(Q_-\) followed counterclockwise by \(Q_+\). A reverse order
would produce an open overlap of the two actual units; a
coincident endpoint produces an empty gap. The claimed
\(0<\Gamma<\pi\) in the nonempty case is justified.

## 4. Entire physical pocket and allocation scope

The whole positive component is the original simple six-cycle,
so its actual occupied-crosscut and outward-cap theorem applies.
The height \(H_2>1/4\) and the complete common-point radius
bound \(R<2\) give every pocket extra a connected open-interior
inner-circle arc of length at least \(\Lambda\).

I checked the cited full routing argument in Section 2 of
RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO.md. It routes every point
of the entire extra arc between the actual endpoint-center
directions by escape paths avoiding the occupied crosscut.
Removing the two complete connected occupied endpoint intervals
leaves exactly the gap identified above. This is stronger than
a statement about extra centers and is sufficient for the
present application.

Every premise of the generic opposite-port projection theorem
is therefore met by the original pair. Its strict
\(\Gamma<2\Lambda\) bound excludes two disjoint extra arcs,
even if each has exactly the minimum permitted length.
The limiting physical argument retains original mean endpoints,
junction coincidences and all zero-weight contacts.

I accept the full whole-pocket conclusion \(n_2\le1\).
Together with the previously accepted capacities, it leaves
precisely \((n_c,n_0,n_2)=(1,1,1)\) and removes precisely
\((0,1,2)\) and \((1,0,2)\) from the preceding allocation list.
This conclusion is a complete conditional capacity theorem on
the entire stated original orbit. It does not by itself exclude
the last allocation, the all-unique parent, any radial family
or the global nine-square problem.

The newer independent global radius lower bound may separately
close the all-unique parent when joined with \(R<2\); that
different gate join is neither a premise nor a claimed
consequence of this review. The two reviewed sources remain
valid reusable hand theorems without that newer result.

