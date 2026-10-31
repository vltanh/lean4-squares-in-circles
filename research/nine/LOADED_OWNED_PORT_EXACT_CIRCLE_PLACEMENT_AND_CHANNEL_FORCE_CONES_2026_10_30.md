# Exact loaded-square circle placement and full side-channel force constraints

Date: October 30, 2026. **Complete reusable necessary-condition lemma.**
This source supplies the physical-circle placement, signs, force cone and
original full-torque elimination used by the physical-two opposite-return
side-channel calculation. It does not declare that whole feature excluded.
No sampling or changed support mean is used.

## 1. One owned port determines the two possible loaded-square positions

Let an actual unit square B lie in the disk centered at O=0 of radius R.
Let (f,w) be its unchanged orthonormal own axes, with either handedness,
and let K be an actual minimum-f support point or original full side mean.
Its center is

    z=beta*f+zeta*w, beta=K.f+1/2.

The farthest-corner identity is

    max_vertex |vertex|^2=(|beta|+1/2)^2+(|zeta|+1/2)^2.

Assume the actual square is positively circle-loaded. At least one actual
corner is on the circle, so its maximum corner norm equals R. Consequently

    J=R^2-(|beta|+1/2)^2 >=1/4,
    T=sqrt(J)-1/2 >=0,
    zeta=sigma*T for some sigma in {-1,1}.          (1)

Both choices are retained; if T=0 they describe the same physical square.
The original port K must lie on its original side, which is exactly

    |sigma*T-K.w|<=1/2.                            (2)

Equations (1),(2) include every physical-circle mask and every endpoint-valued
shared mean. They do not infer a singleton from an endpoint-valued mean.

For an actual C whose original L is a maximum-cvec point, write its center
as eta*cvec+zetaC*wC. The same calculation has

    eta=L.cvec-1/2,
    TC=sqrt(R^2-(|eta|+1/2)^2)-1/2,
    zetaC=sigmaC*TC,
    |sigmaC*TC-L.wC|<=1/2.                         (3)

## 2. Complete physical circle masks and the exact radial-force cone

Suppose beta>0. The actual outer f-coordinate is B0=beta+1/2>0.

If T>0, the unique physical circle corner is

    Z=B0*f+sigma*(T+1/2)*w.

Every nonnegative circle coefficient is attached to this one physical corner,
and positive total load makes the total circle resultant G a positive scalar
multiple of Z. Therefore

    G.f>0, sigma*(G.w)>0,
    B0*sigma*(G.w)=(T+1/2)*(G.f).                  (4)

If T=0, the physical circle corners are B0*f+w/2 and B0*f-w/2.
Either individual coefficient may be zero. Their complete nonnegative
resultant cone is exactly

    G.f>0, |G.w| <= (G.f)/(2*B0).                  (5)

For the duplicate placement labels sigma=+1,-1 at T=0, choose a label with
sigma*(G.w)>=0. Thus every physical square, including either zero individual
coefficient, satisfies at least one of the two placement-label conditions

    G.f>0,
    0<=B0*sigma*(G.w)<=(T+1/2)*(G.f),              (6)

with equality in the last comparison whenever T>0. This is a necessary union,
not a claim that the weak inequality alone suffices for a physical unique
corner. For beta<0, use the actual outward normal -f. The beta=0 case is the
corresponding physical radial position along sigma*w and must keep its full
two-corner cone; it is not discarded by assuming beta>0.

This proof depends on physical circle membership, not on positivity of both
individual circle coefficients. In particular a two-corner square with one
zero coefficient stays in (5).

## 3. Full true-two endpoint moments eliminate the channel magnitude

Now let an actual unloaded true2 side transmitter N join actual loaded true2
B,C. Retain the original unit channel direction n, original applications T in B
and U in C, and positive common magnitude gamma. The complete N equations give

    T-U=n, |n|=1,
    M=det(T,n)=det(U,n).                           (7)

Suppose B owns bvec at its original minimum-bvec application K, and C owns
cvec at its original maximum-cvec application L. Let their positive original
exterior magnitudes be PB,PC. The complete pair resultants towards their
original circle forces are

    GB=PB*bvec+gamma*n,
    GC=-PC*cvec-gamma*n.                          (8)

All physical circle atoms have zero moment about the unchanged origin
individually, including the atoms with zero coefficients. Thus full B,C torque
is exactly

    PB*det(K,bvec)+gamma*M=0,
    PC*det(L,cvec)+gamma*M=0.                     (9)

In particular the scale-free necessary relation is

    PB*det(K,bvec)=PC*det(L,cvec).                 (10)

No endpoint degree has been shortened, and no N equation is used at a loaded
N. If the original six-unit core full moments already imply (10), it remains
a valid redundant exact interval predicate.

For a unique physical B corner ZB, the full radial force (8) and (9) imply

    M*det(bvec,ZB)-det(K,bvec)*det(n,ZB)=0.        (11)

For a unique physical C corner ZC, they imply

    M*det(cvec,ZC)-det(L,cvec)*det(n,ZC)=0.        (12)

These follow by multiplying original equalities and eliminating gamma; they
do not divide by M or any force determinant. They remain necessary if M=0.
They must not be applied as single-corner equalities to a physical two-corner
mask; Section 2 supplies its proper cone instead.

## 4. Exact component form in the current opposite-return frames

Use the actual frame conventions

    det(bvec,wB)=-1, det(cvec,wC)=1,
    Kw=K.wB=det(K,bvec),
    Lw=L.wC=-det(L,cvec).

Assume the original necessary inequalities Kw>0 and Lw<0 have separately been
proved, or retain only a cell/branch on which these strict signs follow.
Set kappaB=Kw>0, kappaC=-Lw>0 and D=-M. Equation (9), with positive PB,PC,gamma,
forces D>0 and

    PB/gamma=D/kappaB, PC/gamma=D/kappaC.

Writing nb=n.bvec, nw=n.wB, nc=n.cvec, nz=n.wC, the positive rescalings of
the two original resultants have components

    B along (bvec,wB):  (D+kappaB*nb, kappaB*nw),
    C along (-cvec,wC): (D+kappaC*nc, -kappaC*nz). (13)

Suppose also beta>0, eta<0, as established for the particular original chart
or retained branch, and use the placement labels in (1),(3). The complete
physical-circle predicates (6) give

    D+kappaB*nb>0, sigmaB*kappaB*nw>=0,
    (beta+1/2)*sigmaB*kappaB*nw
       <=(TB+1/2)*(D+kappaB*nb),                  (14)

    D+kappaC*nc>0, -sigmaC*kappaC*nz>=0,
    (-eta+1/2)*(-sigmaC*kappaC*nz)
       <=(TC+1/2)*(D+kappaC*nc).                  (15)

The last comparison is an equality if the corresponding TB or TC is strictly
positive. If it is zero, the inequality preserves the entire physical radial
cone and either individual zero circle coefficient. If an interval cannot
establish positivity of TB,TC, using only the weak cone comparison is
conservative. If beta or eta has a different sign, use Section 2 in that
actual outward frame; failing to prove the stated sign does not exclude a
cell.

## 5. Original own-axis channel cases retain the whole support face

When n is off the own-axis sets of B and C, T and U are uniquely exposed actual
vertices, so D=-det(T,n) is determined by the same unchanged physical squares.
When n is an own axis, at least one original application can be a full side
mean. It must remain a variable on the entire actual support face.

Equation (7) first requires the exact normal support gap one. For every actual
T on the minimum-n B face and U on the maximum-n C face, one also has

    D=-det(T,n)=-det(U,n).

Consequently D lies in the intersection of the two closed intervals obtained
by ranging the two original support faces. This preserves every possible
original side mean, including both endpoints; an empty intersection excludes
the case. It is sound to use only this necessary intersection without proving
that every point of the intersection gives the full vector equation.

In the above frame conventions, for T=Tb*bvec+Tw*wB and
U=Uc*cvec+Uw*wC the exact formulas are

    D=Tb*nw-Tw*nb,
    D=Uw*nc-Uc*nz.                               (16)

Because each face is a closed line segment and (16) is affine, its whole range
is obtained at the two actual face endpoints. Intersecting those exact ranges
with D>0 and applying (14),(15) gives a full original-mean necessary condition.
Choosing a fresh mean or a face midpoint would not be justified.

## 6. Literal scope

All conclusions are exact necessary statements for the original physical
units. They can be used with finite outward interval enclosures, because a
strict fixed sign or disjoint exact equality interval then excludes every
original point in the cell. Inconclusive signs, zero denominators or an
unproved physical-mask distinction require retaining the cell.

For D02.L135 the stars at B,C,N are exactly loaded true2, loaded true2,
unloaded true2, so (7)--(16) have their literal full-star premises. The hub
geometry, all original V/A/D forces, all nine actual squares and the
common-selector premises remain the caller's inputs. This lemma does not
close the entire opposite-return side feature or either original D02 load row.
