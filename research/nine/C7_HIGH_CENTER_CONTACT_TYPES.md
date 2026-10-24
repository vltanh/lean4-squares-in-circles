# Complete contact types at a high-center body of an all-owned C7

**Status: complete local hand lemma; independent hand audit passed.**
This manuscript retains every owner transition in an all-owned positive
C7. It proves that a body whose center has radius at least three-halves
has only the transverse-face and inner-vertex contact alternatives
listed in Section 4. A positively loaded body owning both its incident
normals has center radius strictly below \(23/16\) and contributes a
right-angle turn to the force polygon. An unloaded body has turn zero.

These are local restrictions, not a proof of the remaining C7
two-square completion bound. In particular they do not exclude all
zero-owner or one-owner high-center bodies, nor do they imply that
every center lies in a disk of radius less than three-halves.

Throughout,

\[
 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16},
 \qquad q=R^2,\qquad Q=1105/256.
 \tag{1}
\]

Choose a circle corner of a physical boundary square and rotate or
reflect its side frame so that

\[
 S=[a-1,a]\times[b-1,b],\qquad
 a\ge b\ge1/2,\qquad a^2+b^2=q.
 \tag{2}
\]

If \(b>1/2\), its unique circle corner is \((a,b)\). If
\(b=1/2\), it is radial and its two circle corners are
\((a,\pm1/2)\). Its center C satisfies

\[
                         |C|^2=q+1/2-a-b.
 \tag{3}
\]

## 1. A long-coordinate inner face cannot own a circle-touching neighbor

**Face lemma.** If \(a-b>1\), no unit square contained in
\(D_R\cap\{x\le a-1\}\) can both meet the face
\(\{a-1\}\times[b-1,b]\) and touch the containing circle.

This excludes that face as an owned separating face. It does not
exclude contacts at its two endpoint vertices with a different,
neighbor-owned normal.

Put \(x=a-1\). A unit T with the stated contact has a vertex
\(p=(x,y)\), \(b-1\le y\le b\), on that face. If T's x-support
is a point, this is immediate. If it is a side, the two parallel
unit-length supporting intervals overlap, and an endpoint of T's
interval belongs to S's interval. Thus this also covers shared sides.

At p, write the two inward side directions of T as

\[
 v=(-\cos\theta,\sin\theta),\qquad
 w=(-\sin\theta,-\cos\theta),
 \qquad 0\le\theta\le\pi/2.
\]

Every orientation at an x-maximal vertex has this form after labeling
the two sides. Since \(|y|\le b\) and \(x>b\), each of the two
adjacent corners satisfies

\[
 |p+v|^2,\ |p+w|^2
       \le x^2+b^2+1+2b
       =(a-1)^2+(b+1)^2
       =q-2a+2b+2<q.
 \tag{4}
\]

For the opposite corner, use

\[
 p\cdot(v+w)
 =-x(\cos\theta+\sin\theta)
       +y(\sin\theta-\cos\theta)
 \le-x+|y|.
\]

It follows that

\[
 |p+v+w|^2
       \le x^2+b^2+2-2x+2b
       =(a-2)^2+(b+1)^2
       =q-4a+2b+5<q.
 \tag{5}
\]

Indeed \(4a-2b-5>2b-1\ge0\), since \(a>b+1\).
The original vertex p also has norm below R. Hence every corner of
T is strictly inside the containing circle, proving the lemma.

## 2. The outer adjacent vertex cannot have a neighbor-owned point contact

Suppose \(b\le1\), and consider

\[
                             p=(a,b-1).
 \tag{6}
\]

If p is a genuine point contact owned by the other unit T, p is in
the relative interior of a side of T. Its inward normal, pointing
from S into T, belongs to S's outward vertex cone, so it has the form

\[
                n=(s,-t),\qquad s,t\ge0,
 \qquad s^2+t^2=1.
\]

Because T is a unit square and p lies on one of its sides, the point
\(p+n\) belongs to its opposite side. But

\[
 |p+n|^2-q
      =2\bigl[(1-b)(1+t)+as\bigr].
 \tag{7}
\]

For \(b<1\), this is strictly positive. If \(b=1\), it is positive
unless \(s=0,t=1\); in that case it is zero, but \(p+n\) would be
in the relative interior of T's opposite side and on the containing
circle. Strict convexity of the disk excludes that possibility as
well. Thus (6) cannot be such a contact.

This argument concerns a point contact owned by the neighbor. A
point-only vertex/vertex contact is already absent after the complete
free-normal selection. A shared side is handled by its actual side
axis, not by assigning a fictitious interior application.

## 3. A center at radius at least three-halves is uniformly near radial

If \(|C|\ge3/2\), then

\[
                         b<3/5,
 \qquad                     a-b>27/20>1.
 \tag{8}
\]

To prove the first assertion, suppose \(b\ge3/5\). The function
\(b\mapsto\sqrt{q-b^2}+b\) increases on \([3/5,\sqrt{q/2}]\),
so (3) gives

\[
 |C|^2\le g(q):=q-1/10-\sqrt{q-9/25}.
\]

The function g increases throughout (1). Moreover

\[
 Q-9/25-(79/40)^2=357/6400>0.
\]

Consequently

\[
 |C|^2\le g(Q)<Q-83/40
       =\frac94-\frac{11}{1280}<\frac94,
\]

a contradiction. Now \(b<3/5\) and \(q\ge17/4\) imply

\[
 a>\sqrt{17/4-9/25}=\frac{\sqrt{389}}{10}
     >\frac{39}{20}.
\]

Subtracting \(b<3/5\) proves the second assertion in (8).

## 4. Every contact alternative at a high-center C7 body

Use the complete all-owned selection from
`C7_MIRROR_VERTEX_EDGE_EXCLUSION.md`, and suppose \(|C|\ge3/2\).
Both incident physical neighbors touch the containing circle. The
following list is exhaustive.

The outer vertical face \(x=a\) cannot own a neighbor: a unit on its
outer side has x-width at least one, so reaches beyond \(a+1>R\).
The inner vertical face cannot own a circle-touching neighbor by
Sections 1 and 3. The corner \((a,b)\) is on the circle and cannot
be shared. The other outer vertex \((a,b-1)\) is excluded by
Section 2; when \(b=1/2\), it is itself the second circle corner.

Thus an incident contact is either on a horizontal side, with the
horizontal side's actual normal, or at one of the two inner vertices

\[
                p_+=(a-1,b),\qquad p_-=(a-1,b-1),
 \tag{9}
\]

with a normal owned by the neighbor. Positive-length shared sides
are allowed in the horizontal-side alternative, with their full
application intervals.

There must be one upper and one lower contact. To see this directly,
every genuine outward normal at the upper side or its inner vertex
has strictly positive origin moment: at the vertex it is

\[
 \det\bigl((a-1,b),(-s,t)\bigr)=(a-1)t+bs>0.
\]

Every genuine outward normal at the lower side or its inner vertex
has strictly negative origin moment, since \(b<1\):

\[
 \det\bigl((a-1,b-1),(-s,-t)\bigr)
          =-(a-1)t+(b-1)s<0.
\]

Here \(s,t\ge0\) are not both zero. On the relative side interiors
the same signs are immediate. Circle forces have zero origin moment,
so two positive contact forces on the same side of this list could
not balance torque.

Orient the C7 so the lower contact is incoming and the upper one is
outgoing. The possibilities are therefore exactly:

| Contact | S owns the normal | The neighbor owns the point contact |
| --- | --- | --- |
| Lower, incoming | \(n_-=e_y\), application on \(y=b-1\) | application \(p_-\), \(n_-=(s,t)\), \(s,t>0\) |
| Upper, outgoing | \(n_+=e_y\), application on \(y=b\) | application \(p_+\), \(n_+=(-s,t)\), \(s,t>0\) |

For a neighbor-owned point contact the components are strict. A
horizontal radial normal would make the excluded inner vertical
face a separator. A vertical normal is also an axis of S and
belongs to the horizontal-side alternative; at a neighbor's
side-interior contact it would give a positive-length shared side.

Let m be the nonnegative circle resultant. Its first coordinate is
positive exactly when the total circle load is positive: it equals
\(a\lambda\) for the unique-corner case, and
\(a(\lambda_++\lambda_-)\) in the radial case. Force balance is

\[
                    2m=\mu_-n_- -\mu_+n_+.
 \tag{10}
\]

If either contact is neighbor-owned in the strict point alternative,
the right side of (10) has strictly positive first coordinate.
Thus the body is loaded. A loaded high-center body consequently
owns either zero or one of its incident normals.

If both contacts have the vertical normal, the first coordinate of
(10) vanishes. Both circle weights, if there are two physical
corners, are then zero. The two magnitudes are equal. Torque also
forces the two actual application means to have the same
x-coordinate, so the body transmits a straight vertical force line.
Its turn in the convex force polygon is zero. Point contacts and
shared-side means are both retained in this transmission case.

## 5. Every positively loaded two-owned body is low and turns by ninety degrees

Now drop the high-center assumption. Suppose both incident edge
normals are side axes of S and its total circle load is positive.

First S cannot be radial. In that case any nonzero radial component
of the resultant would require an inner radial-face contact; the
outer radial face is impossible by width. But the inner radial face
is excluded by Section 1, since
\(a-1/2\ge3/2>1\). Two transverse contacts have zero radial
component and would force all circle weights to vanish.

Thus S has a unique circle corner \((a,b)\) and positive multiplier.
Translation balance with two positive axis-normal contacts forces
their outward normals to be exactly \(-e_x\) and \(-e_y\).
Parallel normals cannot balance a vector with both coordinates
positive; the other choices of nonparallel signs cannot balance it
either. In particular the inner x-face owns a circle-touching
neighbor, so Section 1 gives

\[
                              a-b\le1.
 \tag{11}
\]

Since \((a+b)^2=2q-(a-b)^2\), equations (3) and (11) imply

\[
 |C|^2\le f(q):=q+1/2-\sqrt{2q-1}.
\]

The function f increases throughout (1). At the upper endpoint,

\[
 2Q-1=977/128>(11/4)^2=968/128.
\]

Therefore

\[
                    |C|^2\le f(Q)
                       <Q-9/4=529/256,
 \qquad             |C|<23/16<3/2.
 \tag{12}
\]

The directed incoming and outgoing force normals are perpendicular.
The force polygon is convex and its loaded turn is positive, so the
turn at this body is exactly \(\pi/2\).

Conversely, at any zero-circle-load degree-two body, translation
balance makes the directed normals equal and their magnitudes equal;
the force polygon has turn zero. No positivity of an individual
physical circle-corner multiplier is assumed in this observation.

The global center-cover or direct two-square capacity inequality
must still combine the permitted zero-owner and one-owner high
bodies with these low right-angle turns and possible unloaded
transmitters. The present lemma makes those local alternatives
explicit; it does not close that global implication. \(\square\)
