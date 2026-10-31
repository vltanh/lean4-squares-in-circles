# Two side-normal transmissions cannot close the mixed five-cycle

**Status:** independently reviewed exact conditional hand proof.
This short geometric reduction does not require C to have a unique
circle vertex.

Consider the whole positive component A-U-C-V-B-A, with precisely A,B,C
loaded and U,V unloaded degree-two transmitters, in
\(79/40\le R\le3/\sqrt2\).

**Theorem.** The two transmission directions cannot both be normal to
sides of C. In particular, both C contact points cannot lie in relative
interiors of sides.

If the two directions are parallel, apply
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md).
Otherwise they are perpendicular. Translate and rotate the coordinates
so that C is \([-1/2,1/2]^2\), the first transmission points left, and
the second points down. These coordinates need not put the disk center
at the origin; the following argument is purely about relative positions.
Write their contact points as

\[
             P=(-1/2,s),\qquad Q=(t,-1/2),\qquad
             -1/2\le s,t\le1/2.
\]

Let W_1,W_2>=1 be the transmission widths. The endpoint support points
are

\[
                    P_A=(-1/2-W_1,s),\qquad
                    P_B=(t,-1/2-W_2).
\]

A unit square supported at a point can extend at most one in either
tangential direction from that point. For vertex support, the two incident
unit edges have tangential components of opposite signs, so either
one-sided tangential extent is at most one. For side support, the unit
side has length one and the normal translation has no tangential component.

Consequently

\[
 \begin{aligned}
 \max_x A&\le-1/2-W_1,&\qquad \min_y A&\ge s-1,\\
 \max_y B&\le-1/2-W_2,&\qquad \min_x B&\ge t-1.
 \end{aligned}
\]

If A and B touch, their horizontal and vertical projections overlap.
Thus

\[
                     t\le1/2-W_1\le-1/2,
 \qquad              s\le1/2-W_2\le-1/2.
\]

The contact coordinate bounds force W_1=W_2=1 and s=t=−1/2. Both
transmissions then start at the same corner of C, a case excluded by
[COMMON_CORNER_SIDE_TRANSMISSIONS.md](COMMON_CORNER_SIDE_TRANSMISSIONS.md).
This proves the theorem.

Together with
[VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md),
when C has a unique circle vertex the only remaining contact pattern
has exactly one vertex contact and one side-interior contact. The force
at the vertex contact must lie strictly inside that vertex's normal cone:
a boundary normal would make both directions side normals, contrary to
the theorem above.

## The remaining unique-circle-vertex contact form

The side containing the interior contact must be incident to the other
contact vertex. To see this, suppose for example the vertex is on C's
bottom edge and the side-interior contact is on its top edge. The endpoint
reached from the top side lies at least one above that side. The endpoint
reached from the bottom vertex can rise at most one above that vertex,
because its inward normal has nonpositive vertical component: at most one
incident unit edge can point upward, or a supported side contributes at
most one while inward normal translation does not rise. Its transmission
direction also has nonpositive vertical component. Their
vertical projections are separated by at least one. The other nonincident
vertex/side pairs are the same argument after rotation.

Now use C's own axes and reflect so its center is (a,b), a,b>0, and its
unique circle vertex is (a+1/2,b+1/2). The interior side contact must be
on the bottom or left side: for an incident vertex/top-side pair both
outgoing vertical force components are nonnegative, contradicting the
negative vertical component required by C's circle load. The right-side
case is analogous. If the interior contact is on the bottom side, the
vertex contact must be its left endpoint; the right endpoint would give
only nonnegative outgoing horizontal components. Exchange the axes to
handle the left-side alternative.

Thus, after at most exchanging C's axes, the remaining contact points and
outgoing forces have the form

\[
 P=(a-1/2,b-1/2),\quad f_P=(-u,-v),\qquad
 Q=(a+t,b-1/2),\quad f_Q=(0,-z),
\]

where \(-1/2<t<1/2\), u,v,z>0. Define lambda by writing C's radial
circle force as \(-\lambda(a+1/2,b+1/2)\). Force and torque balance give

\[
 u=\lambda(a+1/2),\qquad
 v+z=\lambda(b+1/2),\qquad
 z(t+1/2)=\lambda(b-a).                                    \tag{1}
\]

In particular b>a. Subtracting the first two force components and using
the torque identity also yields

\[
                            u-v=z(1/2-t)>0.                \tag{2}
\]

Therefore the vertex transmission points more horizontally left than
vertically down. Equations (1)--(2) give a precise remaining local form;
they do not themselves exclude its completion.
