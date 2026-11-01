# Every parallel-frame unloaded three-force triangle requires R squared greater than nine halves

Date: November 1, 2026 UTC. Constructor: module_universal continuation.

**Status: complete hand proof for the entire parallel-core-frame feature,
frozen for clean independent review.** All positive-length internal
contacts and both zero-length corner endpoints are included. Exterior
unit frames, original means, loads and degrees are arbitrary.

## 1. Complete local theorem

Let A,B,C be three distinct actual closed unit squares with pairwise
disjoint open interiors. Their frames are parallel modulo quarter turns.
Their original positive graph contains the triangle AB,BC,CA. Each is
unloaded and has true FULL positive degree three: its other positive
neighbor is one actual outside square, with its original positive force.
The three outside neighbors may coincide. All other actual units and
their full original equations remain unchanged.

Retain every original unit support normal, force magnitude, application
or full shared-side mean. At an internal vertex/vertex singleton contact,
retain the original strict common normal convention. In particular, at
a diagonal corner contact of two parallel units, both components of the
normal in their common frame have the required strict signs. No normal
is reselected in the proof.

Suppose all these actual units lie in one disk of radius R. Then

    R^2 > 9/2.                                      (1)

Consequently this entire physical feature is impossible in the original
nine-square research window R^2<=1105/256, since

    9/2 - 1105/256 = 47/256 >0.

Only the three core frames are parallel. The outside squares may have
independent arbitrary frames and arbitrary loads, degrees, physical
circle masks and zero coefficients. The theorem uses the complete
translations of the core squares; it does not impose any unloaded
equation on an outside neighbor. Original torque equations are retained
but are not needed for this feature exclusion.

## 2. The full parallel physical triangle has one closed T chart

Rotate to the common core frame. Two parallel unit squares that touch
and have disjoint open interiors have center-coordinate differences
with absolute values at most one, and at least one absolute difference
equal to one. Thus every pair of the three actual centers has
L-infinity distance exactly one. The total range of each center
coordinate is consequently at most one.

For each of the three unordered pairs, choose a coordinate in which
its absolute difference is one. At least two pairs choose the same
coordinate, and those pairs share a vertex. The other two centers
must have the SAME coordinate: they cannot lie on opposite sides of
the shared center, because that would give coordinate range two.
Their other-coordinate difference must then be one in order for their
own actual units to touch without overlap.

After one rigid motion, reflection and relabeling of the same actual
units, the entire physical triple is therefore

    B=[0,1] x [0,1],
    C=[0,1] x [-1,0],
    A=[-1,0] x [s,s+1],        -1<=s<=0.            (2)

The two bounds on s follow directly by requiring A to touch both B and
C. This covers every parallel-frame triangle, including every corner
tie in the coordinate choice. The disk center in this chart is an
arbitrary actual point O=(h,k); it is not moved to a convenient origin.

For -1<s<0 all three internal intersections have positive length.
For s=0, AB and BC have positive length and AC is the actual corner
(0,0). For s=-1, AC and BC have positive length and AB is the reflected
corner. There is no additional parallel-frame contact feature.

## 3. An actual unit step stays in the original outside square

If an actual unit square S has a minimum support point q for a unit
normal u, then

    q+u belongs to S.                               (3)

To check this at every original owner and mean, use S's own centered
coordinates. For each nonzero component u_j, the corresponding
coordinate of a minimizing q is -sign(u_j)/2. Adding u_j moves inward
by at most one and remains in [-1/2,1/2]. For a zero component, the
coordinate remains at its original value. This includes support
vertices, side-interior means and both side endpoints.

At an original contact from a core body to its outside neighbor, the
same original application maximizes u on the core and minimizes u on
the neighbor. Thus (3) always supplies an actual point of that same
outside unit. No fictitious continuation square or contact is introduced.

## 4. A complete three-point arc obstruction

We first prove a geometric statement used for all -1<s<0. Suppose a
disk of radius R contains three actual points of the following forms:

    w_0=(-2,y_0),
    w_+=(1,1)+(alpha,beta),
    w_-=(1,-1)+(gamma,-delta),                     (4)

where y_0 is arbitrary and

    alpha,beta,gamma,delta>=0,
    alpha^2+beta^2=gamma^2+delta^2=1.

Then

    R>=17/8.                                       (5)

The proof includes all closed quarter-circle endpoints. The actual
force caller below has strictly positive arc components.

### Restrict the actual disk center

Suppose instead R<17/8 and write its actual center as O=(h,k). The
point w_0 gives h+2<=|w_0-O|<=R, hence

    h<=R-2<1/8.                                    (6)

If k>=1, the actual w_- has first coordinate at least one and second
coordinate at most -1. Consequently

    |w_--O|^2 >=(1-h)^2+(1+k)^2
                  >49/64+4=305/64>289/64>R^2,

a contradiction. If k<=-1, w_+ gives the reflected contradiction.
Therefore

    -1<k<1.                                        (7)

### Reduce each whole arc to its two endpoints

Both 1-h and 1-k are positive. For every alpha,beta>=0 with
alpha^2+beta^2=1, their sum is at least one. Hence

    (1-h)alpha+(1-k)beta >=min(1-h,1-k).

Expanding |w_+-O|^2 now shows

    |w_+-O|^2 >=min(|(2,1)-O|^2, |(1,2)-O|^2).

Thus at least one of (2,1),(1,2) is within the same original disk.
The same calculation below the horizontal axis, using positive
coefficients 1-h and 1+k, shows that at least one of
(2,-1),(1,-2) is within that disk. These endpoint points are auxiliary
disk points established by their distance inequalities. They are not
asserted to be original contacts or moved physical corners.

The four possible endpoint pairs give the complete finite hand cover:

| Upper endpoint | Lower endpoint | Contradiction under (6)--(7) and R<17/8 |
| --- | --- | --- |
| (2,1) | (2,-1) | Their mean squared distance is `(2-h)^2+1+k^2>(15/8)^2+1=289/64>R^2`. |
| (1,2) | (1,-2) | Their mean squared distance is `(1-h)^2+4+k^2>(7/8)^2+4=305/64>R^2`. |
| (2,1) | (1,-2) | The first squared-distance bound forces `(1-k)^2<1`, hence k>0. The second distance is then greater than `(7/8)^2+4=305/64>R^2`. |
| (1,2) | (2,-1) | Reflection k to -k gives the preceding mixed-pair contradiction. |

Every possible endpoint pair is excluded, proving (5). No force ratio,
sampled angle or choice of a favorable arc point was used. QED.

## 5. Every positive-length internal feature supplies those three points

Assume -1<s<0 in (2). Write the original positive magnitudes of AB,AC,BC
as a,b,c, respectively. The actual positive-length intersections force
their unique original normals to be the common own axes:

    A-to-B = (1,0),
    A-to-C = (1,0),
    B-to-C = (0,-1).

All original application means on those shared segments remain arbitrary.
The COMPLETE unloaded translation at A makes its sole outside force
point West, with magnitude a+b. Its original outside application has
first coordinate -1. By (3), its actual outside neighbor contains a
point w_0 with first coordinate -2. No value of that contact's tangential
mean is prescribed.

The COMPLETE unloaded translation at B makes its outside force vector
(a,c), with both components strictly positive. Its original maximum
support application on B is therefore precisely (1,1). Its actual
outside neighbor contains

    w_+=(1,1)+(a,c)/sqrt(a^2+c^2).

Similarly the COMPLETE unloaded translation at C makes its outside
force vector (b,-c), which strictly exposes the actual corner (1,-1).
Its actual outside neighbor contains

    w_-=(1,-1)+(b,-c)/sqrt(b^2+c^2).

These are exactly the actual points in (4). The arc obstruction proves

    R>=17/8,    R^2>=289/64>288/64=9/2.             (8)

This covers the entire open s interval, all positive original force
ratios, every shared-side mean and all outside support owners. No
assumption that an outside square shares the core frame was used.

## 6. Both corner-contact endpoints have a strict diameter obstruction

Assume first s=0. The original AB and BC normals remain their own axes,
while the actual diagonal AC singleton has, by the retained strict
common-normal convention,

    A-to-C=(rho,-sigma),    rho,sigma>0,
    rho^2+sigma^2=1.

Retain the same positive magnitudes a,b,c for AB,AC,BC. The full A force
sum makes its outside force

    (-(a+b rho), b sigma),

strictly Northwest. Its original application is the actual A corner
(-1,1). The full C force sum makes its outside force

    (b rho, -(c+b sigma)),

strictly Southeast. Its original application is the actual C corner
(1,-1). The complete B star is unchanged, but no shortened B equation
is needed for this argument.

Write these two outside unit normals as (-alpha,beta) and
(gamma,-delta), with all four components strictly positive and each
pair of squared components summing to one. Their immediate actual
outside neighbors contain the points

    x=(-1-alpha,1+beta),
    y=(1+gamma,-1-delta).

Consequently

    |y-x|^2
      =8+4(alpha+beta+gamma+delta)
          +(alpha+gamma)^2+(beta+delta)^2
      >8+8+2=18.                                   (9)

Indeed each positive unit pair has component sum strictly greater than
one, and the last two squares sum to
`2+2(alpha gamma+beta delta)>2`. Both x,y are actual points of the
original disk, so its diameter gives `2R>=|y-x|>3sqrt(2)`. Thus
`R^2>9/2` throughout this entire corner feature.

The endpoint s=-1 is its reflection across y=0, followed by exchanging
B and C. All original magnitudes, normals and force equations are
reflected together. It has exactly the same strict diameter obstruction.

The strict singleton premise is used precisely in this endpoint
argument. A boundary normal with one zero component is not silently
declared strict, and no selected free normal is rotated after extraction.

## 7. Whole-feature conclusion and exact remaining boundary

Section 2 proves that the open interval -1<s<0 and the two endpoints
s=0,-1 exhaust every parallel-core-frame physical triangle. Section 5
gives (8) on the whole open interval, while Section 6 gives (9) at both
endpoints. Hence every such full unloaded three-force triangle requires
`R^2>9/2`, proving (1).

The result applies literally to the entire parallel-frame feature of
the remaining unicyclic full-three-cut row (t,s)=(0,0). It also applies
to any larger original positive graph containing these three full
unloaded stars, with all its other actual units retained. It places no
restriction on how the outside neighbors connect or carry circle load.

The nonparallel core-frame features are not declared closed here.
Neither the remaining direct-triangle row as a whole, an original coarse
parent, the unrestricted nine-square radius theorem nor equality is
inferred from this feature exclusion. No claim that all nine unit frames
are parallel is made or needed.

Every new step is proved above using the actual common-frame contact
chart, complete translations, original support points, a finite exact
four-row inequality cover and the actual disk diameter. No additional
geometric manuscript is imported. The strict-singleton convention is
the one already retained in the unchanged original certificate.

The constructor supplied the chart, actual outside points, arc endpoint
cover and corner span; root independently reconstructed the arc route
during development. The complete source requires a separate clean
noncontributor review. No mathematical script, numerical pose, angle
sample, force deletion, interval certificate, Lean, build, CI, frozen
source edit, ledger mutation or remote write was used.
