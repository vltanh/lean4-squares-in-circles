# Two radial boundary units have a fixed contact and a uniform transverse return barrier

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed force-free theorem and complete stated
North-roof feature exclusion, awaiting separate full review and root
adoption. No original whole-family gate is changed.**

The main theorem concerns actual physical two-circle unit squares.
It uses no multiplier, force balance, degree, or selected normal
choice. It keeps both physical circle corners even when a later
certificate assigns one of them zero coefficient. The final caller
uses the original full equations only through its already proved
necessary-domain source.

## 1. Exact physical contact of two radial units

Let d>=1, put R^2=(d+1)^2+1/4, and let

    C=[d,d+1]n+[-1/2,1/2]e

be an actual radial unit in the circle of radius R. Any actual unit
with two physical circle corners has this radial shape in its own
frame: equality of the adjacent far-corner radii centers the transverse
interval, and containment selects the positive near support d.

Let B be a distinct such radial unit, with the same d and R, whose
open interior is disjoint from C. Suppose B and C physically touch.
Set

    phi=arctan(1/(2d)),
    U=d^2+1/4,
    c=(d^2-1/4)/U,
    s=d/U,
    c^2+s^2=1.                                     (1)

Then their outward radial axes differ by exactly 2phi in minor
angle. If the physical contact is on the positive-e side of C,
the complete actual geometry is

    n_B=c n+s e,
    e_B=-s n+c e,
    B=[d,d+1]n_B+[-1/2,1/2]e_B,
    P_CB=d n+(1/2)e=d n_B-(1/2)e_B.                 (2)

In particular the physical intersection is the single displayed
point, at the two inner corners. This conclusion does not specialize
the original common normal within its allowed cone.

Here is a complete angular proof. The angular shadow of C is exactly
the closed interval [-phi,phi] about n. At relative angle psi with
|psi|<phi, its actual open interior meets the ray in the nonempty
interval

    d/cos(psi) < r
       < min((d+1)/cos(psi), 1/(2|sin(psi)|)),       (3)

with the second upper bound omitted at psi=0. This interval depends
only on |psi|. If the two radial axes had minor separation theta<2phi,
their bisector ray would have relative angles theta/2 and -theta/2;
the identical intervals (3) would lie in both open squares. This
contradicts disjointness. If theta>2phi, the closed angular shadows
are disjoint, so the actual squares cannot touch. At theta=2phi the
shadows share exactly one ray, and on that ray both units consist
only of their inner corner of radius sqrt(U). The double-angle
identities give exactly (1)--(2). Reflection handles the negative-e
contact. These alternatives exhaust the full physical intersection.

## 2. A uniform transverse barrier for every other actual neighbor

Now assume additionally

    1<=d<=61/60,
    w=-q n+p e,
    0<=q<=9/40, p>0, p^2+q^2=1.                    (4)

Let A be any other actual contained unit touching B at an original
application or mean P_AB. Let G be any nonzero original common normal
directed from A into B, and suppose

    G.w<=0.                                        (5)

Then the actual application satisfies

    P_AB.w>4043/4000>1.                             (6)

No boundary, degree, force balance, singleton or ownership premise
is required for A. Every actual supporting mean on B remains.

First, p>=sqrt(1519)/40>97/100. Also

    U<13/10,
    s=d/U>10/13,
    0<c<1.

Consequently

    n_B.w=s p-c q
       >(10/13)(97/100)-9/40=271/520>0,
    e_B.w=s q+c p>0.                               (7)

Write the components of G in the real B frame as G_n,G_e. If G_n<0,
its minimum-support face on B is on the outer radial side. For
G_e!=0 it is a physical outer circle corner, which no distinct
contained unit can share. For G_e=0 it is the outer radial side
itself. A unit beyond that face would extend to radial projection
at least d+2>R, so it could not be contained. Thus

    G_n>=0.                                        (8)

Equations (5),(7) now imply G_e<0: otherwise both components would
be nonnegative and at least one positive, giving G.w>0. Hence every
point of the original supporting face or mean P_AB has

    P_AB.e_B=1/2,
    P_AB.n_B>=d.

Using (7), its w projection is at least that of the actual inner
upper B corner

    P'=d n_B+(1/2)e_B=N n+E e,
    N=d(d^2-3/4)/U,
    E=((3/2)d^2-1/8)/U=3/2-1/(2U).                (9)

Throughout (4),

    0<N<1/4,
    E>=11/10.

For the upper bound on N, U<13/10 gives
N=d(1-1/U)<(61/60)(3/13)=61/260<1/4. The bound
on E follows from U>=5/4. Therefore

    P_AB.w>=P'.w=p E-q N
       >(97/100)(11/10)-(9/40)(1/4)
        =4043/4000>1.                              (10)

This proves the whole barrier, including q=0, q=9/40, G.w=0,
either physical circle coefficient equal to zero, and every actual
shared mean when G_n=0. A contact normal at a vertex has not been
reselected.

## 3. Literal North-roof data and the exact feature to exclude

Retain the full original chart and equations of
OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md
and the complete positive-transverse feature exclusion of
BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md.
In their notation,

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=1+epsilon, 0<epsilon<1/60,
    F=1-a in (59/60,1),
    0<a<=epsilon, F^2+b^2=d^2,
    sqrt(2 epsilon)<b<31/120,
    k=F t/b in (1/2,1),
    A=Q+[0,1]j+[0,1]w, Q=(k,1-b),
    j=(-C_A,S_A), w=(S_A,C_A),
    Z_A=Q+w is the unique physical A circle corner,
    Q.j<-1/2,
    D C_A=alpha+a+k,
    D S_A=beta-1+b-t,
    0<D<1,
    G.j>0, G.w<=0.                                 (11)

The genuine A3/B2/C2 equations, both original H rows and all nine
units remain. We prove the following entire subfeature impossible:

    B has two physical circle corners and G.w<0.    (12)

The actual AB application in this feature is

    V=Q+j=(k-C_A,1-b+S_A).                          (13)

The physical radial C and its full original return cover give
P_CB.n>=d and P_CB.e=1/2. If B also has two physical circle
corners, Section 1 gives its exact actual frame (2), with no
restriction on either body's individual circle coefficients.

## 4. Two simple continuous consequences of the real A chord

Equation (11) implies D>k and

    0<S_A < (b-t)/k=b/k-b/F < b,
    q_w:=Q.w=k S_A+(1-b)C_A<1-t<1.                 (14)

The first strict bound uses D>k and beta<1. For the last one,
k S_A<b-t and C_A<1 give q_w<b-t+1-b=1-t.

Suppose k>=3/4. Then S_A<b/3<31/360<1/10 and C_A>99/100.
Since D C_A=alpha+a+k<C_A, the first coordinate of V is negative
and |V_x|<1/4. Its height satisfies

    0<V_y<1-2b/3.

Every point of the physical radial B has norm at least d>1. Thus
V in B would give

    1<|V|^2<1/16+(1-2b/3)^2,
    1-2b/3>sqrt(15)/4>29/30,
    b<1/20.                                        (15)

The squared reserve in the middle radical comparison is 44/14400.
But then the actual A circle corner obeys

    (Z_A)_x>3/4,
    (Z_A)_y>1-1/20+99/100=97/50,
    |Z_A|^2>(3/4)^2+(97/50)^2
        =1105/256+1551/160000,                     (16)

contrary to containment. Therefore the entire feature (12) requires

    1/2<k<3/4.                                     (17)

We next prove b<1/10. The exact A circle equation, (14), C_A<1
and t=kb/F>kb give

    R^2=k^2+(1-b)^2+1+2[k S_A+(1-b)C_A]
       <k^2+4-2b+b^2-2t
       <4-2b+b^2+(k^2-2bk).

For fixed b, the last parenthesis is strictly increasing in k on
the actual interval k>1/2>b. Hence (17) gives

    R^2<73/16-(7/2)b+b^2.

Since R^2>17/4, it follows that

    (7/2)b-b^2<5/16.

This left side is increasing on 0<b<31/120. At b=1/10 it equals
17/50=5/16+11/400. Thus

    b<1/10.                                        (18)

Every inequality was proved on the whole displayed interval. No
endpoint, circle weight, or support mean was sampled or specialized.

## 5. A uniform C-axis bound from the original strip and weak moment

The actual C axis is n=(-C_n,-S_n), e=(-S_n,C_n), with positive
components. We prove the bound

    S_n<5b/4                                       (19)

simultaneously for both complete original H3 rows.

In the HC-side row, set zeta=0. In the opposite row use its actual
zeta>0. Write c_H=t beta-a alpha for the original strip's transverse
parameter, so it is distinct from the cosine c in (1). In both cases
the radial support equality and the original
weak HC moment give

    d^2>=(1+a_H)^2(1+zeta^2),
    a_H=a beta+t alpha>=t alpha,
    0<=zeta<t.                                     (20)

For zeta=0 the first inequality is equality because a_H=epsilon.
For zeta>0 it follows from c_H>=(1+a_H)zeta and the original exact
support d=(1+a_H+c_H zeta)/sqrt(1+zeta^2). Also
zeta<=c_H/(1+a_H)<t beta<t.

Using d^2=(1-a)^2+b^2, a>0 and (20),

    (1+a_H)^2 zeta^2
       <=b^2-2a+a^2-2a_H-a_H^2
        <b^2-2a_H,
    zeta^2+2t alpha<b^2.                           (21)

Thus

    alpha+zeta
       <b^2/(2t)+t/2-(t-zeta)^2/(2t)
       <=b^2/(2t)+t/2.

Since b/(2F)<t<b and the last function decreases for t<b,

    alpha+zeta
       <b[F+1/(4F)]<5b/4.                         (22)

The final strict comparison uses 59/60<F<1 and
F+1/(4F)-5/4=(F-1)(F-1/4)/F<0. The actual axis has
S_n=alpha in the side row and
S_n=(alpha+zeta beta)/sqrt(1+zeta^2)<=alpha+zeta in
the opposite row. This proves (19).

Resolve the same actual w in the C frame:

    w=-q n+p e,
    q=S_n C_A+C_n S_A>0,
    p=C_n C_A-S_n S_A=j.n>0.

By (14),(18),(19),

    q<S_n+S_A<9b/4<9/40,
    p^2+q^2=1.                                     (23)

These are precisely the force-free barrier hypotheses (4), with
the original C and B radial masks and unchanged AB normal.

## 6. Complete contradiction for the stated physical B mask and return sign

In (12), G.w<0 and the actual AB point is V=Q+j. The force-free
barrier in Section 2 gives V.w>1. But its exact A-frame coordinate
is V.w=Q.w=q_w<1 by (14). This is a contradiction.

Therefore the entire original feature

    physical two-circle B and G.w<0

is impossible. Every original BC normal and both physical circle
coefficients of B and C were included. No B force or torque equation
was needed for this last contradiction; its actual true degree and
load remain unaltered.

Together with the earlier complete positive-w exclusion, the exact
remaining North-domain cover is now:

* A unique-circle B may still have G.w<0 at V=Q+j, or G.w=0
  with the original full side mean on j=1.
* A physical two-circle B can remain only at G.w=0 with that
  original actual side mean. The present small-angle estimates were
  proved for G.w<0 and are not silently transferred to this row.

The whole North interface and the original roof ABC.S family remain
open. There is no whole-family credit for this feature exclusion.

## 7. Exact operative inputs and preservation

| Operative source | SHA256 | Literal use |
| --- | --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 | Complete actual North chart, both H rows, unique A circle corner, full A3/B2/C2 equations and AB support |
| BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md | 40b4d692d48b172bca4320a9da98a34239007a61ebcff1fa7811291548086974 | Whole positive-w AB feature exclusion; all original C return means and physical masks retained |

Sections 1--2 are complete physical lemmas proved here without an
external force theorem. All nine actual units, actual normals and
means, true degrees, physical masks and individual zero weights remain.
No new normal selection, geometric sampling, computational exclusion
certificate, Lean compilation, CI, metadata edit or remote action was
performed.
