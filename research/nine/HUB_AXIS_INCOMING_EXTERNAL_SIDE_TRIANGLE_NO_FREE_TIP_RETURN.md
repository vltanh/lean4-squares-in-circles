# A hub-axis incoming contact and externally owned triangle side admit no free tip return

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed all-physical-mask local hand theorem, submitted for full independent review.** Its literal original consequence removes the entire free-VW feature when UV is the sole U-owned spoke and V is nonparallel to U. The geometric two-circle proof needs no U force or torque equation, no T hypothesis, and no degree or load restriction at W beyond its physical circle contact. The unique-circle proof uses the already common fixed-point normal selection in its exact original radius window.

## 1. Exact local hypotheses and conclusion

Retain actual closed unit squares U,V,W with pairwise disjoint open interiors in the disk D_R centered at the unchanged origin. Assume

    2<R<=sqrt(1105)/16.                                  (1)

The actual V has positive total circle load and exactly two positive pair neighbors, U and W. The actual W physically meets the containing circle; its degree, load, other forces and circle mask are arbitrary. U has arbitrary degree and load. All three actual pair contacts UV,UW,VW are present. Keep every original magnitude, separating normal, application, entire shared-side mean, physical circle corner and individual zero circle coefficient.

Use the same selected certificate as in GENERAL_FIXED_TIP_NORMAL_SELECTION.md, with its original strict normal convention at point-only vertex/vertex contacts. Suppose:

1. The original U-to-V normal is a side axis of U.
2. V is nonparallel to U.
3. The original U-to-W normal is a side axis of W, is not a side axis of U, and its actual U-W singleton lies in the relative interior of that W side.

**Theorem.** The original V-W normal cannot be free, meaning strict in both actual vertex normal cones and owned by neither V nor W.

The relative-interior premise in item 3 is stated, rather than inferred from an arbitrary support normal at a vertex. In the original selected D02 certificate it follows from the existing strict-contact convention and the complete singleton selector, as verified in Section 7.

For the physical-two-circle mask of V, the proof below works for every R>2 without an upper radius restriction or a fixed-tip selector. The upper bound in (1) is retained in the all-mask statement because its unique-circle branch invokes the existing selection theorem.

No force is dropped to make V degree two. No equation at a higher-degree boundary body is replaced by a tip equation.

## 2. The complete actual support chart

Rotate about the circle origin so the U-to-V normal is North. Write the actual U as

    U=[L-1,L] x [H-1,H].

Let m be the original U-to-W unit normal. The radius-free triangle side-normal theorem at U gives North dot m>=0. As m is not a U side axis, this inequality is strict and its horizontal component is nonzero. Reflect the entire packing horizontally if necessary. We then have

    m=(b,a), a,b>0, a^2+b^2=1,
    Q=(L,H),                                           (2)

where Q is the actual U-W application. It is a strictly exposed vertex of U and the given relative-interior point of W's minimum-m side.

Since V is nonparallel to U and lies above U, its minimum-height support is a unique vertex P. The actual UV intersection is therefore the singleton {P}. Write

    P=(L-D,H), 0<=D<=1,
    V=P+[0,1] e1+[0,1] e2,
    e1=(c,s), e2=(-s,c),
    c,s>0, c^2+s^2=1.                                  (3)

These are the actual V axes pointing from its bottom vertex P.

The complete common-point theorem applies at the true positively loaded V2 with physical-boundary W: (1) implies R^2>13/4. It gives

    P does not belong to W.                            (4)

In particular P!=Q, so D>0. If the original VW contact is free, let E denote its actual singleton vertex. Equation (4) gives E!=P. These are two distinct fixed physical singleton applications; no shared-side aggregate has been replaced by a point.

Set

    f=(-a,b).

Since Q lies in the relative interior of W's minimum-m side, the actual W has a unique parameter rho in (0,1) with

    W=Q+[-rho,1-rho] f+[0,1] m.                        (5)

All coordinates in (2)--(5) are coordinates of the unchanged physical units.

## 3. A free return is forced onto that same W side

Let ell be the original unit normal from V toward W, and suppose it is free. Apply the triangle side-normal theorem at W. Its normal toward U is -m, an own W axis, and its normal toward V is -ell. Consequently

    m dot ell>=0.                                      (6)

Equality would make ell parallel to f, hence another W side axis. This contradicts the assumed free normal. Thus

    m dot ell>0.                                       (7)

The contact E is a minimum-ell support vertex of W. In the actual chart (5), the positive coefficient (7) forces E's m-coordinate to be zero. The free normal also has a nonzero f component, so its support is one of the two endpoints of that same side:

    E=Q-rho f   or   E=Q+(1-rho) f.                    (8)

This conclusion concerns the actual common side containing Q. It does not assert that Q equals a vertex, nor does it change the original UW application. The opposite W face and both other W faces are excluded by the original support inequalities, not by a choice of a convenient return owner.

## 4. The complete circle-mask cover

A contained unit cannot share a containing-circle point with another interior-disjoint contained unit. Here is the short strict version used below.

A point Z on the containing circle which belongs to a contained unit must be a vertex: strict convexity of squared norm excludes an interior point of any nontrivial unit segment. Let u,v be its two inward unit edge directions. Containment gives

    Z dot u<=-1/2, Z dot v<=-1/2.

Thus -Z is strictly inside the cone spanned by u,v. For sufficiently small positive epsilon, Z-epsilon Z lies in the open interior of the unit. If a second contained unit also included Z, the same radial point, for sufficiently small epsilon, would lie in both open interiors. That is impossible.

Therefore neither P nor E is a physical circle corner of V, by their actual memberships in U and W.

In any own orthonormal square frame, the farthest-corner set is the product of the farthest choices in its two coordinate intervals. It has one, two adjacent, or four vertices. Four occurs only when the square center is the circle origin, with farthest squared radius 1/2, impossible under (1). Because V has positive total circle load, its physical circle mask therefore consists of exactly one corner or exactly two adjacent corners. This classification is physical; an individual zero coefficient does not remove a physical corner from it.

### 4.1. Exactly one physical circle corner

The two actual V applications P,E are distinct fixed physical singleton points by (3),(4). The common certificate already satisfies GENERAL_FIXED_TIP_NORMAL_SELECTION.md throughout its declared window; (1) lies within that window. That theorem excludes a free incident normal at this true V2.

No new normal is selected after extracting forces. Its coincident radial-D exception is absent by (4), and its variable-mean exception is absent because both actual intersections are singletons. This disposes of every physical unique-corner V, including every permitted circle coefficient endpoint.

### 4.2. Exactly two physical circle corners

The two non-circle vertices of V are adjacent. P and E are distinct and neither is a circle point, so they are precisely those two vertices.

In the own frame (e1,e2) of (3), the positive directions point into V from P. As P is not a circle point, the physical outer face is a positive-coordinate face. Exactly two possibilities remain:

    I.  P=(-1/2,d), E=(1/2,d)=P+e1;

    II. P=(d,-1/2), E=(d,1/2)=P+e2,

    d=sqrt(R^2-1/4)-1>1/2,
    R^2=d^2+2*d+5/4.                                  (9)

The inequality d>1/2 follows already from R>2. These are global-origin own-frame coordinates, not translations of the circle. Both physical outer corners and their full original coefficients remain.

In either case E is globally strictly above P, since both s and c are positive. P and Q have height H. Since f has positive vertical component b, (8) must consequently use its upper endpoint. Put r=1-rho. Then

    0<r<1, E=Q+r f,
    W=E+[-1,0] f+[0,1] m.                             (10)

The strict inequality r<1 is exactly the original side-interior location of Q, not a new selected application.

## 5. The second radial orientation contradicts the actual U-side port interval

In case II of (9), E=P+e2. Subtract Q from this equation and use P-Q=-D East and (10):

    e2-D East=r f.

The vertical and horizontal coordinates give

    r=c/b<1,
    D=(a/b)*c-s.                                       (11)

The first equation implies b>c, and hence a<s because both pairs are positive unit-circle coordinates. Therefore

    (a/b)*c<a<s,

so (11) gives D<0. This contradicts the actual UV point P in (3). Case II is wholly impossible.

This argument includes every physical two-corner coefficient split; it uses no chosen positive endpoint coefficient and no V torque division.

## 6. The first radial orientation puts all four W corners strictly inside

In case I of (9), E=P+e1. The actual endpoint equation becomes

    e1-D East=r f,

hence

    D=c+(a/b)*s, r=s/b.                                (12)

Define

    gamma=b*s-a*c,
    eta=b*c+a*s.                                       (13)

Clearly eta>0. If gamma<=0, then a/b>=s/c and (12) would give

    D>=c+s^2/c=1/c>1,

contradicting D<=1. Consequently

    gamma>0, eta>0, gamma^2+eta^2=1.                   (14)

In the actual V own frame, f=(gamma,eta) and m=(eta,-gamma). The actual W from (10) is therefore

    W=E+[-1,0](gamma,eta)+[0,1](eta,-gamma),
    E=(1/2,d).                                        (15)

Its center has f-coordinate

    E dot f-1/2
       =gamma/2+d*eta-1/2
       =d*eta-(1-gamma)/2>0.                           (16)

Indeed eta>1-gamma for positive gamma,eta satisfying (14), and d>1/2. For each fixed endpoint of the m coordinate, the corner on W's maximum-f face is thus strictly farther from the circle origin than the corresponding corner on its minimum-f face.

It remains to compare the two actual maximum-f vertices E and E+m with the actual radius. From (9),(14),(15),

    R^2-|E|^2=2*d+1>0,

    R^2-|E+m|^2=2*d*(1+gamma)-eta>0.                  (17)

For the second strict sign, 2d>1 and 1+gamma>eta. Equations (16),(17) put both maximum-f vertices and both strictly closer minimum-f vertices inside the open disk D_R. By convexity, the entire actual W is strictly inside the containing circle.

This contradicts W's physical boundary contact. It does not matter which W corner could have carried circle load, how many physical W circle corners were possible, whether its own total load is zero, or how many other forces act on W.

Cases I and II exhaust the physical-two mask, and Section 4.1 exhausts the unique mask. The local theorem follows.

## 7. Literal original sole-UV join

The original row is

    M6.B6.HEXAGON.D02.L01345,

with rim 01,12,23,34,45,50, positive chord 02, and circle-load set {0,1,3,4,5}. Keep the original names

    U=2, V=1, W=0, T=3,
    boundary path V,W,5,4,T.

The actual U is unloaded degree three, V is loaded degree two, W is loaded degree three, and T,4,5 are loaded degree two. All three actual extra units, all additional zero-weight physical contacts, the original embedding and all original forces remain. The same-nine lower-window theorem gives R>2; the declared upper bound is the one in (1).

Take the complete structural cover at its pinned current bytes and suppose UV is the sole U-owned spoke, with V nonparallel to U. UV is then a physical singleton. The other two original U applications are distinct physical singletons by the complete common-point and touching-return separation arguments in that cover. The already common unloaded-three-distinct-singleton selector therefore makes UW and UT externally side-owned.

In particular UW is W-owned and not U-owned. The strict-contact convention makes its actual point a strict U vertex and a relative-interior point of an actual W side. This is exactly hypothesis 3, including its strict side-interior guard. It does not follow merely from selecting an arbitrary endpoint support normal.

Every premise of Sections 1--6 is now literal. The original V is the true V2; W remains the true W3 and physically boundary from its positive circle load. Therefore the entire original free-VW feature is excluded for this nonparallel sole-UV interface.

No assertion is made here about a V-owned or W-owned VW, about parallel V and genuine shared UV, or about the entire original D02 row. Those are separate full-interface obligations. No fine gate, load mask or original graph degree is changed.

## 8. Exact direct sources and preservation

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Radius-free normal inequality at U and W, with all actual triangle contacts |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | The original UV application is not a point of the actual boundary W at true loaded V2 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing common selection, only for the unique physical circle mask after both distinct singleton premises are proved |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original strict point normals, actual applications, physical circle coefficients and true complete neighborhoods |
| D02_ALL_MASK_FREE_UV_EXCLUSION_AND_EXACT_SINGLE_HUB_AXIS_COVER.md | 214475cb4a6fe839b6589a346e12f2aea9be97b958a5229e1c1ff4344740e670 | Complete original sole-UV cover and literal nonparallel singleton entry into the external UW side |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original graph, loads, degrees and three unchanged extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | R>2 for the same original nine units |

The local physical-two proof in Sections 2--6 is printed in full. It does not import a perpendicular-hub chart into this nonperpendicular interface, nor use a boundary-neighbor degree-two equation at W. The unique-circle argument retains the selected-certificate premise and the full radius window of its exact source.

This manuscript is a new complete feature proof. Adoption requires full independent review of its current bytes and the literal original join. No pose sample, angle mesh, computational exclusion certificate, Lean compilation, CI, force deletion, mean change, new normal choice, commit, remote write or whole-row credit is used.

