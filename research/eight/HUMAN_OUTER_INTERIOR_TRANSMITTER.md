# Sufficiently outer interior squares are actual two-contact transmitters

## Theorem

Choose a radius-minimizing packing with the fewest actual contacting pairs.
Suppose its radius satisfies

    sqrt(2)+1/2 < R <= sqrt(9789)/50.

Let S be a packed unit square strictly inside the containing circle, and
put

    q=R^2,        r_c=sqrt(q-1),        d_*=r_c-1.

If its distance D from the disk origin satisfies D>d_*, then S has
exactly two actual neighbors. Its nearest point to the origin lies in the
relative interior of one side. The two contacts are on the two sides
perpendicular to that side, with opposite separating normals belonging
to S's own frame.

This is a statement about all actual contacts, not only positive stress
edges. Additional zero-weight neighbors are excluded by the same proof.
No assumption about either neighbor's orientation or circle contact is made.
The result is conditional on the displayed distance; it does not assert
that every circle-free exterior square satisfies that distance bound.

## 1. Contact points and square centers

Every actual contact point z of two packed unit squares satisfies

    |z|^2<=q-1=r_c^2.                                      (1)

Here is the geometric proof. Choose a separating side normal n owned by
one square, directed toward the other. The first square contains z-n.
If z dot n<=0, its containment proves (1). If z dot n>0 and the second
support face is an edge, the second square contains z+n, again proving
(1). Otherwise its support face is the vertex z. Let u,v be its orthogonal
unit edge directions into that square. Since n dot u,n dot v>=0 and

    z dot n=(n dot u)(z dot u)+(n dot v)(z dot v)>0,

at least one of z dot u,z dot v is positive. The corresponding vertex
z+u or z+v has squared norm greater than |z|^2+1, proving (1).
This is also the contact-point lemma in HUMAN_GLOBAL_CYCLE_CLOSURE.md.

For any square center p with orthonormal frame e,f, exact containment gives

    |p|^2+|p dot e|+|p dot f|+1/2<=q.

Using |p dot e|+|p dot f|>=|p| and putting rho=sqrt(q-1/4),

    |p|<=rho-1/2,       |p|^2<=q-rho.                      (2)

We will use both bounds without assigning stress weights.

## 2. The nearest point is on a side

If the nearest point were a corner, choose signed square coordinates to
write S=[a,a+1] times [b,b+1], with a,b>=0 and D^2=a^2+b^2.
Farthest-corner containment gives

    q>=D^2+2(a+b)+2>=D^2+2D+2,

and hence D<=sqrt(q-1)-1=d_*, contrary to the hypothesis. This includes
the endpoint case where one coordinate is zero.

Thus the nearest point is in a side's relative interior. Choose orthogonal
coordinates about the unchanged disk origin so that

    S=[h-1,h] times [D,D+1],       0<h<1.                  (3)

Its top edge has y=D+1>r_c. By (1), no point on that edge, including
its two endpoints, can be an actual contact point.

## 3. Only horizontal contact normals can remain

At every other boundary point of S, every outward support normal has
nonpositive vertical component: the possibilities are its bottom edge,
bottom corners, and the relative interiors of its vertical sides.
Choose a separating axis for each actual contacting pair involving S.
If any of those normals had negative vertical component, translating S
slightly upward would preserve every selected separator and make that
pair strictly separated. S has strict circle slack; its distances from
all originally noncontacting squares are positive. These remain valid
for a sufficiently small translation. No contact is added and at least
one is removed, contradicting the minimum number of actual pairs.

Consequently every available separating normal at every contact is
horizontal. Each neighbor is wholly to the right of x=h or wholly to
the left of x=h-1, tangent to that line at some height at least D.
Both sides have neighbors: if all neighbors were on one side, translate
S horizontally away from them to remove all contacts. If there were no
neighbors at all, the theorem's conclusion would not follow from this
argument alone; section 6 below addresses that case explicitly.

## 4. An opposite neighbor forces a positive cap threshold

Assume for now that both sides have neighbors. We show h>1/10 and,
by horizontal reflection, 1-h>1/10.

Choose a neighbor A on the left. Its rightmost face lies on x=h-1 and
meets S at height at least D. Its center satisfies

    (p_A)_x<=h-3/2,       (p_A)_y>=D-1/2>0.               (4)

To justify the second inequality for arbitrary orientations: a vertical
support face is either an edge of a parallel square, whose endpoints
differ from its center in height by 1/2, or the single rightmost vertex
of a nonparallel square. In an unsigned frame angle t in [0,pi/4], that
vertex's vertical displacement from the center has absolute value
|cos(t)-sin(t)|/2<=1/2. Thus a support point of height at least D
always gives (4).

If h<=1/10, (2)--(4) would give

    q-rho >= |p_A|^2
       > (7/5)^2+(sqrt(q-1)-3/2)^2,

or equivalently

    321/100+sqrt(q-1/4)-3sqrt(q-1)<0.                     (5)

The expression on the left strictly decreases with q. At q_+=9789/2500,

    sqrt(q_+-1/4)>19145/10000,
    sqrt(q_+-1)<170752/100000,

as is checked by the positive squared differences
1159/4000000 and 959/39062500, respectively. Therefore the left side of
(5) is greater than

    321/100+19145/10000-3(170752/100000)=97/50000>0,

a contradiction. This proves h>1/10. The reflected argument proves the
opposite threshold bound.

## 5. A side cannot have two different neighbors

Suppose A and B were distinct right-hand neighbors. Both are tangent to
x=h and lie in x>=h. Consider their chords on x=h+1/2.

Each chord has length at least one. Indeed, for an unsigned frame with
c>=s>=0 and c^2+s^2=1, the chord length at depth 1/2 from the leftmost
support line is

    1/c                    if s<=1/2,
    1/(2cs)                if s>=1/2.

These follow by intersecting the vertical line with the four edges, and
both are at least one. A parallel square is included in the first case.

The upper endpoint of each chord has height at least D. For a parallel
square this follows from its near edge meeting S at height at least D.
For a nonparallel square its leftmost vertex has height Y>=D. The top of
the chord is above that vertex: along an upward shallow edge the increase
is s/(2c); along an upward steep edge it is c/(2s) when s>=1/2,
and c-(s/c)(1/2-s)=(1-s/2)/c when s<1/2. All are nonnegative.

The relative interiors of the two chords are disjoint, because those
interiors belong to the open square interiors. Order them vertically.
The lower endpoint of the upper chord is at least the upper endpoint of
the lower chord, and thus at least D>d_*.

Apply HUMAN_HIGH_SLICE_BOUND.md to the square owning that upper chord,
with cap threshold h>1/10 and d=d_*. The radius assumptions ensure

    63/100<d_*<71/100.

For the lower comparison use sqrt(2)>141/100 and
9/4+141/100>1+(163/100)^2. The upper comparison follows from
q_+-1<(171/100)^2. The slice lemma produces a vertex with squared norm
strictly greater than

    1+(d_*+1)^2=q,

contradicting containment. Hence there is at most one right-hand neighbor.
Reflection gives at most one left-hand neighbor. Whenever S is nonisolated,
sections 3--5 prove that it has exactly those two neighbors.

## 6. Correct treatment of isolated squares

Minimum contact count does not prohibit an isolated square. Therefore the
precise conclusion proved without an extra hypothesis is the following:

> A strictly contained square at distance D>d_* is either isolated in the
> actual-contact graph, or has exactly two actual neighbors on opposite
> sides perpendicular to its nearest-point side.

If S belongs to any actual contact cycle, it is automatically nonisolated
and the degree-two conclusion applies. The same holds if it has any
positive stress edge. The initial theorem is to be read with this necessary
nonisolation hypothesis; no argument here removes isolated packing units.

To avoid ambiguity in later use, the formal statement used by this note is:

**Outer transmitter theorem.** Under the stated radius and minimum-contact
hypotheses, every nonisolated, strictly contained square S with
D>sqrt(R^2-1)-1 has exactly two actual neighbors, in the configuration
proved above. All additional actual contacts, including zero-weight ones,
are excluded.

In particular, a strictly interior vertex on an exterior moment cycle
is an actual degree-two transmitter whenever it satisfies this explicit
distance bound. Nearer interior vertices and isolated squares remain
separate cases in the sharp eight-square proof.
