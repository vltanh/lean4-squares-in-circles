# A radial side channel ending next to an actual circle corner has an empty exterior cap

Date: October 26, 2026.

**Status: accepted complete local hand theorem after independent source
and physical-scope review.** See
REVIEW_C6_RADIAL_ADJACENT_CAP_ROOT_2026_10_26.md.
The theorem excludes an entire actual
exterior pocket from a geometric contact feature. It leaves every
original normal, circle weight, application mean, transmitter position,
and completion square unchanged. It does not itself close the whole
strictly obtuse one-radial alternating C6 family or a roadmap gate.

**Current full subfamily conclusion:** the independently reviewed
SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md now
classifies the whole both-adjacent family into the already excluded
right-turn three-slider family. Its Section9 also excludes the entire
both-near-corner distance family. The local geometry and capacity
lemmas below remain valid, but their earlier partial allocation
conclusion is superseded by that full classification and completion
join. The general one-radial parent still has other open port types.

Work throughout the original radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad K=\sqrt{R^2-\frac14},\qquad d=K-1.
\tag{1}
\]

## 1. The unchanged radial channel and the exact additional feature

Let S be a physically two-circle-corner loaded square in an actual
simple positive cycle with at least three loaded bodies. Let its
channel to a consecutive boundary square B contain exactly one true
unloaded degree-two side-normal transmitter U, of reserve one.

The complete radial support cover of
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`, Section 1, permits
the following actual frame after a possible global reflection:

\[
 S=[d,d+1]\times[-1/2,1/2],\qquad
 P=(d,1/2),\qquad g=(-c,s),
\]
\[
 c=\cos\alpha>0,\quad s=\sin\alpha>0,
 \quad 0<\alpha<\pi/2,
 \qquad Q=P+g=(d-c,1/2+s).
\tag{2}
\]

Here P and Q are the original force applications on S and B.
Their displacement is exactly g by the real transmitter equations.
The actual outward channel normal and positive height are

\[
                        N=(s,c),\qquad h=N\cdot P=ds+c/2.
\tag{3}
\]

Assume the following extra physical feature:

**The application Q is a vertex of B adjacent to an actual circle
corner z of B.**

Thus there is an actual unit side vector v of B such that

\[
                          z=Q+v,\qquad |v|=1,\qquad |z|=R.
\tag{4}
\]

The premise is about the original application, and is not obtained by
moving a mean to a preferred endpoint. A genuine shared-side mean
which already equals this endpoint is included. An opposite vertex,
a general side-interior mean, or merely an unmarked nearby point is
outside this premise. Neither individual radial circle weight is
required to be positive.

**Theorem.** If z is B's unique physical circle corner, then

\[
                                  h>d.
\tag{5}
\]

Consequently the whole actual S-U-B exterior pocket is empty.
The pocket is also empty if B has two physical circle corners;
the weak equality case is treated in Section 3.

## 2. The circle equation gives the strict support gap

Choose the other actual unit side-axis vector w of B so that its
other vertex adjacent to z is z-w. Containment gives

\[
 |z-w|^2\le |z|^2=R^2,
             \qquad z\cdot w\ge\frac12.
\tag{6}
\]

The vectors v,w are perpendicular; their signs are immaterial in the
following square identity. If z is physically unique, the first
inequality in (6) is strict, and hence

\[
                 (z\cdot v)^2
                 =R^2-(z\cdot w)^2<R^2-\frac14=K^2.
\tag{7}
\]

On the other hand the actual coordinates in (2) and (4) determine
the same scalar product without choosing a force magnitude. Since
\(R^2=(d+1)^2+1/4\),

\[
 |Q|^2=R^2-2d(1+c)+s,
\]
\[
 z\cdot v
 =\frac{R^2-|Q|^2+1}{2}
 =d(1+c)+\frac{1-s}{2}>0.
\tag{8}
\]

Equations (7)--(8) therefore imply

\[
 d(1+c)+\frac{1-s}{2}<d+1,
                  \qquad 2dc<1+s.
\tag{9}
\]

Both c and \(1-s\) are positive, and
\((1+s)(1-s)=c^2\). Multiplying the second inequality of (9)
by \((1-s)/c\) gives

\[
                         2d(1-s)<c,
                    \qquad ds+\frac c2>d.
\tag{10}
\]

This proves (5) over the entire angle and radius domain. No angle
subdivision or coefficient certificate is used.

The full pocket-routing theorem in
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md` puts every whole exterior
extra square in the cap \(D_R\cap\{x:N\cdot x\ge h\}\).
The exact unit-square support threshold of
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1, is d:
no contained unit square can lie wholly beyond a line of height
strictly greater than d. Thus (5) excludes every extra from this
entire actual pocket, regardless of its own circle-contact mask.

## 3. The physical two-corner equality case is also blocked

If B has a second physical circle corner, (6)--(7) remain weak.
The same computation gives \(h\ge d\). If the inequality is strict,
Section 2 still applies. Suppose instead \(h=d\).

Every displayed weak inequality is then an equality. In particular

\[
 z\cdot v=K,
       \qquad |Q|^2=|z-v|^2=R^2-2K+1=d^2+\frac14.
\tag{11}
\]

The radial application P has the same squared norm. Both P and Q
lie on the actual line \(N\cdot x=d\), and their displacement
has length one in its unit tangent direction g. Their tangential
coordinates therefore have absolute value one half and opposite
signs. Their segment is exactly

\[
                     [P,Q]=dN+[-1/2,1/2]g.
\tag{12}
\]

The equality case of the exact support threshold says that any unit
square wholly in \(D_R\cap\{N\cdot x\ge d\}\) is the unique
radial square

\[
                     E=[d,d+1]N+[-1/2,1/2]g.
\tag{13}
\]

Its inner side is the segment (12). The original radial application
P lies in the strict relative interior of U's side, by the complete
radial support cover. The opposite transmitter side has the same
transverse coordinate interval and contains Q at that same strict
coordinate. Consequently the midpoint of [P,Q] lies in \(U^\circ\).
The open transmitter contains points immediately beyond the line
\(N\cdot x=d\) near this midpoint. Those points are also in
\(E^\circ\), contradicting physical nonoverlap. Thus the equality
case has no exterior extra either.

This is the same actual occupied-midpoint obstruction used for the
radial/radial channel theorem. It uses no chosen transmitter slider
and retains every originally permitted mean endpoint.

## 4. Whole one-radial subfamily consequence and exact remaining scope

In an alternating all-side C6 with exactly one radial loaded square
S and two unique loaded squares B,C, suppose both S-incident
applications on B,C are their actual vertices adjacent to their
respective circle corners. Applying the theorem separately to the
two original channels proves that both radial-incident exterior
pockets are empty.

This full geometric subfamily also meets the near-corner premise of
`SIX_CYCLE_RADIAL_INCIDENT_NEAR_CORNER_ANGLE_BOUND.md` on both
channels. In the strictly obtuse radial-turn branch, its complete
corollary proves that every loaded turn is strictly greater than
\(\pi/2\), that the original loaded ports are distinct points on
one actual inner side, and that the entire central free union has
capacity at most one. The right-turn endpoint retains its separate
complete classification and completion exclusion.

Thus every putative strictly obtuse three-extra completion in this
subfamily must put at least two actual extra squares into the one
remaining B-to-C exterior pocket. This is a necessary allocation
condition, not a completed bound for that remaining pocket. No
capacity for that pocket or full three-extra exclusion is inferred
without an additional whole-domain argument.

Both original radial corner weights, including either zero endpoint,
the full true transmitter equations, all genuine shared means and
side endpoints satisfying (4), all physical zero-weight contacts,
and all nine physical squares remain present. No radial concurrence
is assumed to lie inside S. No full one-radial gate, global sharp
bound, equality classification, or prerequisite-chain audit is
closed by this local theorem. No Lean compilation or CI was run.
