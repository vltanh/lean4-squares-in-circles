# Near-antipodal square endpoints have protected outward rays without circle contact

Date: October 30, 2026 UTC.

**Status: complete proposed force-free hand lemma, awaiting independent
review. No original graph or roadmap flag is changed here.**

## 1. A single endpoint's entire outward ray is free of all other units

Let actual unit squares have pairwise disjoint open interiors and lie
in the disk centered at O of squared radius at most Q=1105/256. Put

    M=91/60, L=89/60, sigma=1/sqrt(2).

As follows from the farthest-corner identity, every actual center c
satisfies

    |c|<M,
    M^2+M+1/2-Q=31/57600>0.                              (1)

Let A be one actual square, c_A its center, and n any unit direction
such that

    c_A.n >= L.                                         (2)

**Protected-ray theorem.** The entire closed ray

    {c_A+t*n : t>=0}                                    (3)

is disjoint from every other actual closed square. No circle contact,
stress, own-axis or endpoint-degree premise is needed.

For 0<=t<1/2 the point in (3) belongs to the open radius-1/2
incircle of A and hence to int(A). Another closed square cannot meet
int(A): interior points of that square arbitrarily near such a point
would overlap int(A).

For t>=1/2 suppose p=c_A+t*n belongs to another actual square E.
Since every point of a unit square is within sigma of its center,
write c_E-c_A=xi*n+eta*n_perp. Equations (1),(2) give

    xi < M-L=1/30,
    xi >= t-sigma >= 1/2-sigma > -1/4,
    |eta|<=sigma.                                      (4)

The exact comparison sigma<3/4 follows by squaring. Therefore

    |c_E-c_A|^2 < 1/16+sigma^2=9/16<1.                  (5)

But two distinct actual square centers have distance at least one,
because their open radius-1/2 incircles are disjoint. This proves
the theorem, including t=1/2 and all closed physical contacts.

## 2. Application to any long supported gap

Let A,B be actual squares and d a signed unit direction such that

    d.(c_B-c_A) >= 2+h_A(d)+h_B(d) >=3.                 (6)

Here h denotes the actual square support halfwidth, and h>=1/2.
The center bounds imply

    d.c_A < M-3=-L,
    d.c_B > 3-M=L.                                     (7)

Apply Section 1 to A with n=-d and B with n=d. Both outward
center rays are protected from **every** other actual square, not
merely from the positive-stress neighbors. Each ray can be continued
to the containing circle or the fixed circle of squared radius Q
without crossing any other physical unit.

This supplies actual exterior access even for an endpoint that is
physically circle-clear or has zero selected circle load. Its center
and every application mean remain unchanged.

## 3. Quantitative angular control of the outward spokes

Use an endpoint's outward n as the horizontal axis and write
c=X*n+Y*n_perp. From (1),(2),

    X>=89/60,
    |Y|^2<M^2-(89/60)^2=1/10,
    |Y|<1/3.                                          (8)

Consequently its center direction is within pi/12 of n:

    |Y|/X < 20/89 < 1/4 < tan(pi/12)=2-sqrt(3).         (9)

The last inequality follows from sqrt(3)<7/4. Along the whole
outward ray, the signed angle relative to n is atan(Y/(X+t)). It
stays between its actual starting angle and zero. Thus the center
direction, the entire finite spoke, and its circle-exit direction
all lie in the same open angular interval of width less than pi/12.

In particular, if four such endpoints have pairwise minor center
angular separation greater than pi/6, their outward spokes lie in
disjoint angular neighborhoods of halfwidth pi/12, and their exits
retain the centers' cyclic order. A separate caller must supply that
separation and the actual long paths before using a crossing theorem.

## 4. Scope for physical path crossings

For an actual contact path, a route through successive centers and
original application means has its open center-to-mean segments in
the respective original square interiors. This is preferable to
using a force line that may lie along an internal square's boundary.
Combined with the protected rays, such routes can be extended to
the circle while preserving all physical squares.

This manuscript does not infer two-path alternation or a four-square
junction without a complete caller. It does not assume that a
translational planar stress is also torque-balanced. The protected
ray is a physical geometric fact independent of either certificate.
No compilation, numerical pose search, new computational certificate,
original-ledger mutation or remote write occurs here.
