# Upper angular bound and equality classification for contacting outer squares

## Theorem

Let two unit squares S,T have disjoint open interiors and intersect in
at least one point. Suppose their center norms about the disk origin
are at least one. Their smaller center-direction angle delta obeys

    delta <= pi/2.                                      (1)

If delta=pi/2, then after a rotation and possibly relabeling, their
centers are (1,0) and (0,1), both square frames are axis-parallel,
and their intersection is the single point (1/2,1/2).
This equality pair fits already in the disk of squared radius 5/2.

No containing-circle hypothesis is needed for the inequality.
The result applies to **actual touching squares**, not merely pairs
with an available separating axis.

## Proof

Let p,q be the centers, r=|p|>=1 and s=|q|>=1. Every point of a unit
square lies within its circumradius 1/sqrt(2) of its center. Choosing
z in S intersection T yields

    |p-q| <= |p-z|+|z-q| <= sqrt(2).                    (2)

The cosine law is

    |p-q|^2=r^2+s^2-2*r*s*cos(delta).

If delta>=pi/2, its cosine is nonpositive, so the right side is
at least r^2+s^2>=2. Comparison with (2) forces equality
throughout: delta=pi/2, r=s=1, and |p-q|=sqrt(2).
Equality in both triangle inequalities in (2) then forces
z=(p+q)/2 and

    |p-z|=|q-z|=1/sqrt(2).

Because this distance is the square circumradius, z is a vertex
of each square. Rotate so p=(1,0),q=(0,1), hence z=(1/2,1/2).
For a unit square, a center-to-vertex direction of angle 135 degrees
(or -45 degrees) forces its edge frame to be horizontal and vertical
(up to sign and quarter-turn). Thus both squares are axis-parallel.
They have bounds

    S=[1/2,3/2] times [-1/2,1/2],
    T=[-1/2,1/2] times [1/2,3/2],

so their intersection is exactly z. Their largest squared vertex
norms are 9/4+1/4=5/2, proving the stated equality realization.

## Corollary in the eight-square search region

Combine with HUMAN_STABLE_OUTER_ANGLE.md. At squared radius
q<=9789/2500, every pair of **touching outer squares** has center
angular separation in

    pi/4-1/500 < delta <= pi/2.                         (3)

For noncontacting outer squares the upper bound does not apply.
The lower bound alone does not force a seven-outer contact cycle
to be impossible, and (3) does not establish the five-corner chain.

## Limits

The cyclic seven-outer-cycle and outer-path-with-inner-attachment
branches in HUMAN_OUTER_GRAPH_REDUCTION.md survive the present bound.
No statement about an inner square's center angle is inferred.
