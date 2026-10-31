# Two actual near units at one corner of an origin-containing square

Date: October 27, 2026.

**Status: complete proposed physical lemma and conditional contact-owner
reduction, frozen for full root and separate independent review.** No
original graph, certificate, force, mean, mask, ledger or remote file is
changed. Sections 1--3 are self-contained Euclidean geometry; Section 4
uses one explicitly pinned accepted physical kernel.

## 1. Physical theorem, including closed-disk and side-endpoint contact

Let H, X and Y be three distinct actual unit squares with pairwise
disjoint open interiors. Let O belong to closed H. Suppose an actual
vertex P of H belongs to both X and Y, and each of X and Y meets the
closed disk D_epsilon centered at O, where epsilon>=0.

Use the two inward orthonormal own axes i,j of H at P, and write

    H=P+[0,1]i+[0,1]j,
    O=P+a*i+b*j, 0<=a,b<=1.

Then

    a<=epsilon, b<=epsilon,
    |P-O|<=sqrt(2)*epsilon.                         (1)

No force, selected normal, degree, circle load, origin-avoidance of X
or Y, or condition on where their disk points occur is required. In
particular those disk points may be only boundary points of the units
or only boundary points of the closed disk.

We use two elementary facts about actual squares. First, no point of
one closed square can belong to the open interior of another square
with disjoint open interior: a small open neighborhood in the latter
would contain an interior point of the former. Second, at any boundary
point of a square, its tangent directions form a closed angular sector
of angle pi/2 at a vertex, or pi at a relative-side-interior point.
Every direction strictly inside that sector enters the actual open
square for all sufficiently small positive displacements.

Suppose, to obtain a contradiction, that a>epsilon. Choose actual
points q_X in X intersect D_epsilon and q_Y in Y intersect D_epsilon.
For Z equal to either X or Y,

    (q_Z-P).i=a+(q_Z-O).i>=a-epsilon>0.             (2)

The point P cannot be in int Z, since every neighborhood of the
actual H vertex P contains points of int H. Therefore P is a boundary
point of Z with one of the two tangent sectors just described.
Convexity and P,q_Z in Z show that the direction q_Z-P belongs to
that actual sector.

No nonzero direction in this sector can have both positive i and
positive j coordinates. Such a direction would put a point of closed
Z in int H after a sufficiently small displacement from P, contrary
to disjoint interiors and the first elementary fact above. In
particular, (2) implies

    (q_Z-P).j<=0.

Measure angles in the (i,j) plane with i at angle zero and j at pi/2.
The direction q_Z-P consequently has an angle

    theta_Z in (-pi/2,0].                           (3)

The entire actual closed tangent sector of Z avoids the open first
quadrant (0,pi/2). Take its angular lift containing theta_Z inside the
closed complementary interval [-3*pi/2,0], and denote it [alpha_Z,
beta_Z]. It has length at least pi/2. Since it contains (3),

    beta_Z>=theta_Z>-pi/2,
    beta_Z<=0,
    alpha_Z<=beta_Z-pi/2<=-pi/2.                    (4)

Thus the nonempty open interval

    (-pi/2, beta_Z)

consists entirely of interior tangent directions of Z. Both X and Y
therefore contain, in their open tangent sectors at the same P, every
direction in the nonempty interval

    (-pi/2, min(beta_X,beta_Y)).

Choose any one such direction. A sufficiently small positive
displacement of P along it belongs simultaneously to int X and int Y.
This is the required contradiction. It proves a<=epsilon. Interchange
i and j and repeat the same argument to obtain b<=epsilon. Equation
(1) follows from the orthonormal coordinates of O-P.

This proof treats a disk point lying on an H side by allowing
theta_Z=0. It treats an actual side-interior point P of X or Y by using
its full angle pi sector. No point is moved into the open disk, and
no endpoint is replaced by an arbitrarily chosen side mean.

## 2. Two unchanged non-owned small ports give the same actual corner

Now assume 0<=epsilon<1/60. Keep the physical premises that O belongs
to closed H and that the two actual distinct units X and Y each meet
D_epsilon. Suppose actual contacts HX and HY have respective actual
applications p_X,p_Y and separating normals f_X,f_Y from H, with

    |p_X-O|<3/8, |p_Y-O|<3/8.

If neither f_X nor f_Y is an own axis of H, each strictly exposes
one actual H vertex. Its application is necessarily that vertex.
Distinct vertices of a unit square have distance at least one, whereas

    |p_X-p_Y|<=|p_X-O|+|p_Y-O|<3/4<1.

Consequently p_X=p_Y=P is the same actual H vertex. The contacts are
physical, so P belongs to both original units X,Y. Section 1 applies
at those unchanged applications and gives

    |P-O|<=sqrt(2)*epsilon<1/40.                    (5)

The last strict comparison follows from 2/3600<1/1600. This deduction
does not replace either original normal by an incident own axis.

## 3. Complete owner alternatives under shallow original supports

Suppose in addition O belongs to int H, and the same actual contact
normals have the original support bounds, in coordinates with O=0,

    0<h_H(f_X)<=epsilon,
    0<h_H(f_Y)<=epsilon.                            (6)

Keep the actual applications and the bounds in Section 2, including
applications that are endpoints of an owned side. The following
alternatives exhaust the original normals.

* If neither normal is owned by H, Section 2 gives the actual small
  corner (5).
* If both normals are owned by H, they cannot be opposite own axes:
  their two support heights would add to the actual unit width one,
  whereas (6) bounds their sum by 2epsilon<1. If they are different
  adjacent axes, their two actual support lines meet at an H corner
  with inward margins h_H(f_X),h_H(f_Y). This again gives (5).
  Otherwise they are precisely the same original H-owned side normal.
* If exactly one normal is owned by H, let its actual shallow side
  be F, with support height h in (0,epsilon]. The non-owned contact
  is an actual H vertex P with |P|<3/8. The opposite H side has
  distance 1-h>=1-epsilon>59/60 from O, so P cannot belong to that
  opposite side. It therefore belongs to F itself.

The last mixed case does **not** assert that the H-owned contact
application equals P, that its other unit contains P, or that the
non-owned-contact unit is wholly beyond F. Those stronger premises
are not consequences of the theorem proved here. In particular an
actual H vertex can lie in the relative interior of the other unit's
owned contact side. The theorem retains that original interface.

## 4. Consequence when two actual boundary neighbors touch each other

Also keep the circle range

    sqrt(17)/2<=R<=sqrt(1105)/16.

Suppose H has two distinct actual physical boundary neighbors K,T
that physically touch one another. Section 2 of the accepted source

    GENERAL_SMALL_ORIGIN_CORNER_CONTACT_KERNELS.md
    SHA256 b977be65217728c0363e8bab030bdb3d11b1b8ef75cc32d295a8337c4ea01477

excludes every actual H vertex of norm less than 1/40. Its complete
physical feature proof requires no degree or positive circle force
at either K or T; it includes physical circle corners with individual
zero weights.

Therefore, in the shallow-port setting (6), the only retained owner
interfaces in Section 3 are:

1. both original normals are owned by the same H side;
2. exactly one original normal is owned by H, and the other actual
   H-vertex contact lies on that same shallow H side.

This is a conditional owner reduction. It does not exclude either of
these retained interfaces. In particular it does not declare an
original fine cell or coarse cell closed. An application to an actual
D_ht block must retain its true positive degrees and separately check
the original small-port and shallow-support hypotheses; the theorem
does not manufacture them from a shortened star.

The pinned geometric source in this section exists unchanged at
publication boundary 8304072dbc91bcbe726d651c10403351f9566853. Its own
operative input is the unchanged physical theorem
ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md, SHA256
6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467.
Sections 1--3 above need neither source.

No sampling, numerical pose, equilibrium modification, Lean run,
workflow, shared-ledger change or remote action is asserted here.
