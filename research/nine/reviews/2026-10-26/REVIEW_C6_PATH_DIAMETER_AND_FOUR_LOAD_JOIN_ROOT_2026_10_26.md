# Root review of two shared path bounds and both four-load C6 central joins

Date: October 26, 2026.

Reviewer: root, separate from the author and independent certificate reviewer.

**Verdict: PASS for both complete local diameter theorems and the full
stated central-capacity join across both four-load C6 orbits.** No
four-load completion parent or cap gate is closed by this result.

## 1. Current sources and dependency audit

I read the following sources in full.

| Source | SHA256 at this review |
| --- | --- |
| TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md | 7de5d4129b48250f9c11fbff9b77e362263633f6390ddf8d9ebd8534f708d30a |
| LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md | 2b5684f6052f085c554f8cb901d9baeeb216ccbd363d3a2de311710235dac09a |
| SIX_CYCLE_FOUR_LOAD_DIAGONAL_CENTRAL_CAPACITY_ONE.md | c518b14449fe2a83367b1699d263e12624b3c59c98017932114a270bf710b041 |

Acceptance-header and review-citation changes preserve this reviewed
mathematics. Substantive changes require a fresh review.

I read the complete inherited BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md,
including both shadow-width cases, the endpoint-sector comparison,
the full auxiliary interpolation and both derivatives. The actual
channel, endpoint-height and proper-concurrence hypotheses were checked
against SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md,
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md and
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma 1.1.
The central join uses the separately reviewed generic actual-ring
capacity theorem and the unchanged full physical routing in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md.

## 2. Removing endpoint circle contacts from the path theorem

Every contained endpoint has
\[
r^2+2rh+1/2\le R^2\le Q,\qquad h\ge1/2.
\]
This gives \(r<M=91/60\), and below \(R_0=\sqrt{17}/2\) it gives
\(r<3/2\) immediately. In the remaining range, a supposed endpoint
distance at least three forces both endpoint radii above \(m=89/60\).

I checked line by line that Sections 3--4 of the inherited source
need only the displayed containment inequality at an endpoint:

- Its actual four vertex slopes give
  \(t=\arctan(h/(r-k))\), with \(h^2+k^2=1/2\).
- Containment gives \(1/2\le h<11/20,\ 11/25<k\le1/2\), hence
  \(0<w+t<\pi/2\).
- At fixed tilt, increasing the scalar radius to
  \(\bar r^2+2\bar r h+1/2=M^2+M+1/2>Q\) is valid for a
  circle-clear endpoint as well. The interpolation remains in the
  complete declared domain.
- The inherited exact derivatives satisfy
  \(E_r>167/80\) and \(dE/d\psi<-272/675\) on the auxiliary curve.
  Moving along that curve to zero tilt reaches \((M,0)\).
- The resulting common sector disk has radius \(y_0\) with
  \(9/4-y_0^2=20777891/13058946000>0\).

This is a scalar comparison, not a physical motion of either endpoint.
Only the two actual middle boundary squares use the independent
shadow-width bound \(w=\arctan(23/16)\). Their physical circle contacts
ensure that they avoid the origin, so all three contact directions exist.

The ordinary minor angular distance gives
\[
d_{\mathbb S^1}(c_0,c_3)<t_0+2w+t_3<\pi
\]
by the triangle inequality through the three actual contact points.
It requires no increasing lift or angular order for the arbitrary
endpoints. Splitting this distance between two capacities
\(w+t_0,\ w+t_3\) puts both centers in the same sector disk.
Their distance is at most \(2y_0<3\), the required contradiction.

Thus arbitrary endpoint degrees, masks, circle-clear endpoints and
additional contacts are genuinely covered. Neither middle body may
be replaced by a circle-clear body without another argument.

## 3. Actual loaded-intermediate diagonal path

The second theorem retains the entire selected multi-load simple cycle
and the actual path \(A-B-U-C\). The diagonal transmitter supplies the
exact common-axis endpoint geometry, the gap \(1+\sqrt2\), and the
positive channel height. The endpoint-height theorem gives
nonnegative vertical center coordinates.

Under a supposed distance at least three, the far right endpoint has
radius greater than \(m\). Its physical circle equality gives
\[
x+y<Q-1/2-m^2<13/8.
\]
The complete convex quadratic comparison on
\(3/20\le y\le89/120\) forces \(y<3/20\), and then \(x>22/15\).
This includes the height-zero physical radial tie at \(C\).

I rederived the opposite-endpoint dot-product bound
\(-c_A\cdot c_C>(9-2M^2)/2\). For
\(X=-(c_A)_x\le11/8\), the whole-interval increasing upper bound
\[
MX+(3/20)\sqrt{M^2-X^2}
\]
falls short by \(103/7200\). Hence
\((c_A)_x<-11/8,\ |(c_A)_y|<2/3\), and the actual square halfwidth
gives the whole-body inclusion \(A\subset\{x<-2/3\}\).

The actual intermediate corner satisfies
\[
z_B=(-a,b),\qquad 167/120<a<29/20<b<31/20.
\]
Thus \(B\) is physically unique in this hypothetical distant
configuration. Its original true degree two and proper concurrence
give \(q_B=(h/b)z_B\), with \(h/b<13/29\). Its positive circle load
and other horizontal pair force force the original \(A\)-support
normal downward.

The support-owner cover is exhaustive: the whole bottom side and its
mean endpoints, the strict bottom-right vertex, or the strict
bottom-left vertex. The first two give a common application with first
coordinate greater than \(-2/3\), contradicting the whole-body inclusion.
For the last, the actual outward normal of \(A\) is proportional to
\[
v=q_B-P,\quad P=(-a,b-1),\quad
v_1>334/435>3/4,\quad 0<v_2<1/5.
\]
The component upper bounds on \(P-c_A\) give
\[
v\cdot(P-c_A)/v_1<1/8+(4/15)(5/4)=11/24<1/2.
\]
This contradicts the support equality
\(v\cdot(P-c_A)=H_A(v)\ge |v|/2\ge v_1/2\).
The positive coefficients justify the upper comparison even when
one actual coordinate difference is negative.

No extra force is erased at \(B\). This argument requires its real
proper concurrence and does not assert a force-free mixed-path bound.
The source correctly states that the equation at \(A\) is unused;
any wider local application must independently supply all remaining
channel and intermediate-force premises.

## 4. Every center pair in both four-load orbits

In either six-cycle, exactly twelve unordered pairs have one- or
two-edge paths and therefore distance at most \(\sqrt2\) or
\(2\sqrt2<3\). I checked every remaining pair against the actual
cycle order.

For \(U-A-V-B-D-C-U\), the three opposite pairs are
\((U,B),(V,C),(A,D)\). The first two use respectively
\(U-C-D-B\) and \(V-B-D-C\), with two boundary middle bodies.
The last uses \(D-B-V-A\) when \(V\) is diagonal or \(D-C-U-A\)
when \(U\) is diagonal.

For \(U-A-B-V-C-D-U\), the opposite pairs are
\((U,V),(A,C),(B,D)\). The first uses \(U-A-B-V\).
If \(V\) is diagonal, the other two use \(A-B-V-C\) and
\(D-C-V-B\). If \(U\) is diagonal, they use \(C-D-U-A\)
and \(B-A-U-D\).

Every listed loaded intermediate is an original degree-two loaded
body with its unchanged positive forces. At least one real diagonal
supplies the entire needed pair cover. No circle contact is imposed
on either unloaded endpoint. Thus all fifteen pair distances are
strictly below three in each stated family.

## 5. Whole central union, allocations and exact checks

The original simple-cycle routing gives the central free union and
the two actual exterior channel unions, and makes the direct
boundary-pair exterior pockets empty. Every central extra has the
original winding-one enclosure, including compact-interior limits
at weak junctions. The generic short-diameter actual-ring theorem
therefore applies to the same six physical bodies and gives
\(n_{\rm in}\le1\). It permits a nonconvex center chain.

All three original extras remain, so
\[
n_{\rm in}+n_U+n_V=3.
\]
The four displayed allocations for \(n_{\rm in}=0\) and three for
\(n_{\rm in}=1\) are exhaustive. No cap occupancy was assumed to
derive the diameter. The separate range \(R<R_0\) gives the same
central result for either width pattern directly from the strict
radius bound on every center. Equality \(R=R_0\) is included
where the proved diagonal path theorem applies.

An independent Fraction reconstruction confirmed every displayed
metric reserve, including \(31/57600\), \(511/57600\),
\(31/14400\), \(12527/14400\), \(2/75\), \(103/7200\),
\(143/2880\), \(167/4800\), \(239/14400\), \(1/144\),
\(9/200\), \(263/11520\), \(31/1740\), \(1/24\), and the
three inherited sector values recorded above.

The seven allocations still need the appropriate joint exterior
obstruction. The all-side high-radius family still needs its
remaining metric work. Both original FOUR_ZERO_DISTANCE2 and
FOUR_ZERO_DISTANCE3 parents and their cap gates remain open.
The join retains all four circle loads, individual zero weights,
physical masks, owners, original means and all three extra units.
No Lean compilation, CI, numerical sample or new coefficient
certificate was used.
