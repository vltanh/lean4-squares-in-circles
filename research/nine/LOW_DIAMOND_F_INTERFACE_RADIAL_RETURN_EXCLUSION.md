# The entire f-owned/shared HK row has no radial-B diamond return

**Status: complete hand proof; author, root and separate independent full
saved-source and direct-prerequisite review passed. See REVIEW_LOW_F_INTERFACE_2026_10_25.md.
No full remaining LOW parent checkbox changes here.**

Keep the original triangle-attached diamond, its true H5/K3/A2/B2,
the intact HXY petal, all positive pair forces, every original mean and
all three arbitrary completion squares. A and K have one physical circle
corner each; B has two physical circle corners. Thus the physical mask
in the order (K,A,B) is UUS. Either individual B circle multiplier may
vanish, while its original total circle load remains positive.

**Theorem.** The entire f-owned/shared HK row of the negative-A upper-left
chart is impossible for physical radial B. Combined with
LOW_DIAMOND_F_INTERFACE_UNIQUE_RETURN_EXCLUSION.md, this excludes both
physical B masks throughout that whole HK row, with every KB/HB owner
and every original shared mean retained.

## 1. The unchanged force and contact reduction

Use the original positively oriented (f,g) coordinates of the accepted
complete HK fan. Write

    n=(E,-p), j=(p,E), E^2+p^2=1, E>=p>=0,
    U=(X,H0), H=U+[-1,0]n+[-1,0]j,
    K=[X,X+1] x [h,h+1], W=h+1,
    H0=h+zeta, 0<zeta<1.

HK has its actual f normal. For p>0 it is the K-owned singleton at U;
for p=0 it is genuinely shared and its entire original mean interval
is unchanged. The uniform two-corner theorem in
LOW_DIAMOND_F_INTERFACE_ROOT_PROJECTION.md gives

    cn=c_H.n>0.

The actual negative pressure at A and its true A2 force equation give,
exactly as in Section 2 of the unique-return source,

    cj=c_H.j>0, cf=c_H.f>0, cg=c_H.g>0.                  (1)

In particular

    X=cf+(E+p)/2>0,
    H0=cg+(E-p)/2>0,
    0<H0<W.                                            (2)

Let beta,eta,nu be the original positive HA,HK,HB magnitudes, and let
ell be the actual H-to-B normal. The actual H5 equation and the strictly
positive pressure of the intact HXY petal give

    beta n+eta f+nu ell+M=0, c_H.M>0,
    c_H.ell<0.                                         (3)

Every H-owned HB axis is impossible: the physical HKB triangle forces
ell.f>=0, leaving only n,j when p>0, both contradicted by (1)--(3).
At p=0 the additional possible axis -j would put B strictly below K,
because max_B y<=H0-1<h. Thus HB is not H-owned or genuinely shared.

Since B is physically radial, RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md
gives positive H-pressure at each of its two physical circle corners,
irrespective of their individual weights. Hence c_H.F_B>0. With k the
actual K-to-B normal and gamma>0 its original magnitude, the true B2
equation is

    F_B=gamma k+nu ell.

Therefore c_H.k>0. At K, the actual KH normal -f is a side axis.
The physical triangle side-normal theorem then gives k_f<=0. With
cf,cg>0, we obtain the complete two-feature fan

    k=g, or k_f<0<k_g.                                 (4)

The whole k=g alternative is excluded by the purely geometric top-side
proof in LOW_DIAMOND_F_INTERFACE_UNIQUE_RETURN_EXCLUSION.md, Section 5.
That proof explicitly allows either B mask. It covers all tilted B edge
interiors and vertices, the aligned shared means, and the p=0 endpoint.
Thus the original KB application is now the fixed K vertex

    Q=(X,W), k_f<0<k_g.                                (5)

No free normal or radial circle-weight endpoint has been removed by a
unique-tip selection in this argument.

## 2. This K vertex is never a vertex of radial B

Put

    S0=sqrt(q-1/4)>1,
    rho^2=(S0-1)^2+1/4=q+1-2S0.

Every physical radial unit in D_R has its two outer vertices on the
circle and its two inner vertices at squared norm rho^2. Write F=X+1.
The positive f center of K means its physical far corners have f
coordinate F. Consequently

    q=F^2+max(W^2,(W-1)^2).                            (6)

Because K is physically unique, W!=1/2: equality would put both
(F,W) and (F,W-1) on the circle. Also Q is strictly inside the circle,
since (F,W) is a K corner and

    |Q|^2=F^2+W^2-2X-1<q.                              (7)

We claim the sharper comparison

    sign(|Q|^2-rho^2)=sign(W-1/2).                      (8)

If W>1/2, (6) gives q=F^2+W^2. Thus F<S0 and

    |Q|^2-rho^2=2(S0-F)>0.

If 0<W<1/2, use instead q=F^2+(W-1)^2. Direct expansion gives

    |Q|^2-rho^2=2(S0+W-1/2-F)
      =4(W-1/2)(S0+W-1)/(S0+W-1/2+F)<0.               (9)

All denominator factors and S0+W-1 are positive by S0>1, W>0 and F>0.
This proves (8) throughout the original unique-K domain. In particular
|Q|^2!=rho^2. Together with (7), Q is neither an inner nor an outer
vertex of any physical radial B.

The actual KB contact is the singleton Q by (5). Since Q is not a B
vertex, it lies in the strict relative interior of a B side. Hence the
original k is B-owned. This is a physical feature conclusion, without
generic selection or alteration of the normal.

## 3. Every tangential B-owned normal contradicts the true B2 force

Choose B's actual radial frame

    B=[S0-1,S0]e+[-1/2,1/2]t, t=Je,
    z_plus=S0 e+(1/2)t, z_minus=S0 e-(1/2)t.

Here e points radially outward. Applying the radial-neighbor theorem
to both physical circle corners and adding gives

    c_H.e>0.                                           (10)

Because k is a B axis, it is one of e,-e,t,-t. The choice -e contradicts
c_H.k>0 and (10). Suppose k is t or -t. The original radial circle
weights, including either zero individual endpoint, give

    F_B.e=Lambda S0>0,

where Lambda is their positive sum, with the common force normalization
absorbed into Lambda. The e component of true B2 therefore gives

    ell.e>0.

The physical triangle theorem at B, with its B-owned KB axis, gives
ell.k>=0. Since e,k are orthonormal,

    ell=(ell.e)e+(ell.k)k.

Both c_H.e and c_H.k are positive, and the first coefficient is strictly
positive. Thus c_H.ell>0, contradicting (3). This argument includes
every HB owner, free contact and permissible original force ratio.

Only the actual radial side normal k=e remains.

## 4. A radial KB normal forces HB to be B-owned too

For k=e, Q lies in the strict interior of B's inner radial face, so

    Q=(S0-1)e+tau t, -1/2<tau<1/2,
    |Q|^2<rho^2.                                       (11)

All points of H have squared norm at most |U|^2. Indeed its center
coordinates in its own orthonormal frame are cn,cj>0, and the corner
U=c_H+(n+j)/2 is its unique farthest corner. The squared norm is convex
on each edge and throughout the square, so this corner bound applies
to every point, not only to the four vertices.

By (2), (5) and (11),

    max_{z in H}|z|^2=|U|^2=X^2+H0^2
                        <X^2+W^2=|Q|^2<rho^2.          (12)

No point of H can therefore be a vertex of B: its inner vertices have
norm rho, and its outer vertices have norm R>rho. The actual HB contact
cannot be free or H-owned. Shared HB has already been excluded in
Section 1. Hence it is a B-owned singleton with ell a side axis of B.

This is again a conclusion about the physical contact, not a unique-tip
normal selection and not a freezing of an original mean.

## 5. The two actual B-owned faces have incompatible heights

Both k and ell are now B axes. The physical HKB triangle gives
k.ell>=0. The possibility ell=k contradicts their opposite pressure
signs, and ell=-k contradicts the nonobtuse normal condition. The direction
-Jk=(k_g,-k_f) has two positive components and hence positive pressure
by (1). Therefore the only remaining direction is

    ell=Jk=(-k_g,k_f),

with both components negative.

Let I be the actual vertex where B's minimum-k and minimum-ell faces
meet. With the original side coordinates, including their allowed
comparison endpoints,

    B=I+[0,1]k+[0,1]ell,
    Q=I+theta ell, P=I+sigma k, 0<=theta,sigma<=1.

Thus the original HB point P obeys

    P_g-Q_g=sigma k_g-theta ell_g>=0,
    P_g>=W.                                            (13)

But ell.j=p ell_f+E ell_g<0. Every actual maximum-ell support point of
H is U-j, U-n-j, or on their joining side when ell.n=0. All of those
points have g coordinate at most

    H0+p-E<=H0<W,

contradicting (13). This excludes the final radial B-owned KB case and
proves the complete radial-B theorem.

## 6. Whole-row join and exact scope

The unique-return theorem excludes every UUU configuration in this
f-owned/shared HK row. The present proof excludes every UUS configuration
in the same entire row, with both individual radial circle-weight
endpoints retained. These are the two remaining physical B masks.
Therefore the whole f-owned/shared HK row is excluded, including the
genuinely shared p=0 transition and all original means, throughout the
declared radius interval.

The proof uses the real H5 and B2 equations and keeps K's genuine three
forces and all their actual application moments. No circle force is
redistributed and no normal is chosen after extraction. The intact petal
and all three extra physical squares remain. The n-owned and free HK rows remain;
the g-owned parallel row was already excluded. No larger upper-left
parent or global theorem is declared closed by this row alone.

No numerical sample, angle subdivision, coefficient table, Lean
compilation or CI is a proof premise. No roadmap checkbox or accepted
gate count changes here.
