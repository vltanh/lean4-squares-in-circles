# The complete left-side return when H owns HK

**Status: complete hand owner/geometry reduction; independent root
full-source and direct-prerequisite review passed on October 25, 2026.
See REVIEW_LOW_H_OWNED_HK_SIDE_RETURN_REDUCTION_2026_10_25.md. The final
block-pressure inequality is still open; no gate or ID changes here.**

Retain the original negative-A upper-left diamond, true H5/K3/A2/B2,
the intact HXY petal, all nine squares, all three completion squares,
every positive force and every original application mean. A,K,B have
unique physical circle corners. The entire radial-B mask was excluded
separately, with all individual corner weights retained, in
LOW_DIAMOND_H_OWNED_HK_RADIAL_AND_NONNEGATIVE_PROJECTION_EXCLUSION.md.

Work throughout q0=6241/1600<=q=R^2<=1105/256 in the strict H-owned
n-normal HK row. The accepted same source excludes cn=c_H.n>=0,
so this remaining unique-B row has cn<0. The complete physical KB fan
is the one in LOW_DIAMOND_H_OWNED_HK_RETURN_FAN.md, Sections 1--3.

**Theorem.** In the entire actual KB=-f left-side feature, HB must be
a strict H-owned j contact at B's vertex opposite its physical circle
corner. B is tilted relative to K. Every B-owned or free HB alternative,
every aligned B, and every shared HB alternative is excluded with its
original mean retained until the physical exclusion. In the notation
below the exact surviving geometry is

    Q=(X,y), B=Q+[0,1]e+[0,1]vB,
    e=(-C,S), vB=(-S,-C), C,S>0, C^2+S^2=1,
    Y=Q+vB=U-sigma n,
    zB=Q+e,
    ell=j, (E-d)C>(E+d)S.

The source identifies this complete remaining force branch. It does
not assert that its original block pressure is nonnegative.

## 1. Original coordinates and the two accepted scalar inputs

Use the unchanged K frame and H frame:

    n=(E,d), j=(-d,E), E,d>0, E^2+d^2=1,
    E>v>=1/sqrt(2), 0<d<u<=v,
    r0=s/E=u+(d/E)v<1,
    V=(X,h), U=V+w j, 0<w<1-r0,
    H=U+[-1,0]n+[-1,0]j,
    K=[X,X+1] x [h,h+1], X,h>0.

Write

    N=V.n, J=V.j, Tj=J+w,
    rho=R-sqrt(2), x=rho^2,
    b0=sqrt(x-N^2).

The accepted sign-split source proves, on cn<0,

    0<N<1/2, J>=b0, r0-J>=b0,
    x>5/16, |Z|^2<13/16 for every Z in H.          (1)

The complete scalar comparison in
LOW_DIAMOND_H_OWNED_HK_FRONT_SUPPORT_BOUND.md strengthens this to

    3/8<N<1/2.                                    (2)

That comparison uses the two actual A/K circle corners, the original
A2 concurrence and their exact opposite-j gap. No hypothetical K2
equation is an input.

## 2. A strict positive f coordinate for the front/top H vertex

First r0>2d. Indeed

    r0-2d
      =(u-d)+(d/E)(v-E)
      =(u-d)[1-d(u+d)/(E(E+v))]>0.                 (3)

Here u>d, and the bracket is positive because d<E and u<=v imply
d(u+d)<E(v+E). Since r0<1, this gives d<1/2. Consequently

    3E>5d,                                        (4)

because 9E^2-25d^2=9-34d^2>1/2.

For N in [3/8,1/2],

    5/16-N^2-(3/4-N)^2
        =(1/2-N)(2N-1/2)>=0.

Thus x>5/16 and (1) imply b0>3/4-N. Since X=EN-dJ and
J<=r0-b0,

    X-d(1-r0)
       >=EN+d b0-d
        >(E-d)N-d/4
        >(3E-5d)/8>0.                             (5)

Together with w<1-r0, this proves

    U_f=X-dw>0, U_g=h+Ew>0.                       (6)

This is a whole-domain bound. There is no angle partition or polynomial
coefficient packet. It uses the original distinct contacts P and V
through (1), rather than replacing their actual means by a common point.

## 3. Every remaining HB normal points toward H's upper j support

Assume the actual KB normal is -f. Hence all of B lies in f<=X, and
its original KB application Q=(X,y) has h<=y<=h+1. The complete fan
gives ell.n>=0, excludes ell=-j by strict support separation, and
excludes ell=n, including its entire shared interval.

If ell.n>0 and ell.j<0, H's unique ell-support point is U-j. Its f
coordinate is X+d(1-w)>X, so it cannot belong to B. If ell.n=0
and ell.j<0, then ell=-j, already excluded. The equality ell.j=0
would be ell=n because ell.n>=0, and is also excluded. Thus

    ell.j>0, ell.n>=0.                            (7)

If ell.n=0, then ell=j. Otherwise both inequalities are strict, and
the actual HB application is the fixed H vertex U.

## 4. No strict-cone HB contact can be B-owned or free

Suppose ell.n>0 and ell.j>0, so its H application is U.

### 4.1. Aligned B, including every original shared KB mean

If B is aligned with K, its f interval is [X-1,X]. Since 0<dw<1,
U_f=X-dw is strictly between those two vertex coordinates. Thus U is
not a B vertex, and HB cannot be a free vertex/vertex contact.

The only aligned inward B axis satisfying both strict inequalities
in (7) is ell=g: the axes f,-f,-g fail ell.j>0 or ell.n>0.
Thus U is on B's bottom side, with actual normal g. The unchanged
B2 origin moment, including the original possibly shared KB mean,
would be

    0=gamma det(Q,-f)+nu det(U,g)
      =gamma y+nu U_f>0,                           (8)

because gamma,nu>0, y>=h>0 and (6). The circle force has zero origin
moment. This is impossible.

### 4.2. Tilted B and the complete four-axis cover

If B is tilted relative to K, its maximum-f contact is one fixed
vertex Q. Label the inward axes there as

    e=(-C,S), vB=(-S,-C), C,S>0, C^2+S^2=1,
    B=Q+[0,1]e+[0,1]vB.                           (9)

The two fixed B applications U and Q are distinct, since U_f<X.
The preselected GENERAL_FIXED_TIP_NORMAL_SELECTION.md therefore
excludes a free HB normal at this actual unique B2 body. No shared
mean has been fixed here: the K contact is a unique support vertex
of tilted B and the H contact is the unique support vertex U.
Because H does not own a strict-cone normal, ell must be B-owned.

The B axes vB and -e fail (7): vB.n<0 and (-e).j<0. Consider the
axis ell=-vB=(S,C). Its minimum face is Q+vB+[0,1]e, so

    U=Q+vB+t e, 0<=t<=1.

Its f coordinate gives dw=S+tC, and hence S<=dw<d and C>E.
Its g coordinate gives

    y=h+wE+C-tS
      =h+wE+(1-dwS)/C.

But

    y-(h+1)=[1-C+w(EC-dS)]/C>0,                   (10)

because S<d, C>E and E>d imply EC>dS. This contradicts y<=h+1.
The argument covers both endpoints of the entire candidate B face.

Only ell=e remains. By (6), its unchanged B2 origin moment is

    0=gamma det(Q,-f)+nu det(U,e)
      =gamma y+nu(S U_f+C U_g)>0.                 (11)

This is again impossible. No radial-concurrence division, circle-weight
normalization or missing K force is used in (8) or (11).

Thus the strict-cone alternative has been exhausted. In the entire
left-side feature,

    ell=j.                                        (12)

## 5. Neither an aligned B nor a shared j return is possible

If B were aligned with K, its unique minimum-j vertex would be its
bottom-right vertex, whose f coordinate is X. Every point on H's
maximum-j face has f coordinate at most U_f=X-dw<X. The physical HB
contact (12) would therefore be impossible. Hence B is tilted as in
(9), and its KB application Q is fixed.

Suppose B also owns j. Then its frame is H's frame, and the actual
HB support of B is its minimum-j side. Write

    B=[p,p+1]n+[Tj,Tj+1]j.

Its unique maximum-f vertex is Q=(p+1)n+Tj j because f=E n-d j.
Using Q_f=X and Tj=J+w gives

    p+1=N+(d/E)w.                                 (13)

As 0<(d/E)w<1, the bottom-left vertex

    Z0=p n+Tj j

belongs to H's top side: N-1<p<N. In particular the physical HB
overlap is a genuine positive-length side interval, with its entire
original mean still present.

The true B2 force equation in H's frame is

    F_B=gamma(-f)+nu j
        =-gamma E n+(gamma d+nu)j.                 (14)

Its unique circle force therefore has negative n coordinate and
positive j coordinate. Since Tj=J+w>0 and the physical far corner is
unique, it is zB=p n+(Tj+1)j. The actual vertex Z0 is adjacent to that
circle corner, so

    |Z0|>=R-1>=39/40>sqrt(13/16).

This contradicts Z0 in H and the whole-H bound (1). No choice of a
shared mean or zero-length limit is used. Thus B cannot own j.

Consequently (12) is a strict H-owned singleton contact. There is no
remaining shared HB interface.

## 6. The exact original singleton branch left by this cover

For the tilted B in (9), j.e=dC+ES>0. The minimum-j support vertex
can only be Q or Q+vB. The first has f coordinate X and is not on H's
top face. Thus

    Y=Q+vB=U-sigma n,
    EC-dS>0,
    sigma=(S-dw)/E,
    y=h+C+w/E-(d/E)S.                            (15)

The original side parameter is retained; 0<=sigma<=1 is the closed
comparison range, with any stricter physical singleton convention
unchanged.

Every vertex of B other than the one opposite its physical circle
corner is at distance at most 1 from that circle corner, and hence
has norm at least R-1>sqrt(13/16). Since Y is in H, (1) forces Y to
be the opposite vertex. Therefore the actual unique circle corner is

    zB=Q+e=(X-C,y+S).                              (16)

This rules out the other possible far corner by a whole-body bound,
not by assigning a convenient circle vertex.

Taking B2 torque about its actual circle corner in (16) gives

    nu[(E-d)C-(E+d)S]=gamma S>0.                   (17)

In particular C>S and all divisions by the bracket in (17) have their
strict signs proved. The original two circle equations, B2 origin
concurrence and the true K3 equations are exactly those of
LOW_DIAMOND_PARALLEL_ROOT_BRANCH_WORKING.md, Sections 1--3, now with
their owner/feature premises justified over the whole KB=-f feature.

Writing beta,eta for the separate original HA/HK magnitudes, the still
required block-pressure sign in this sole surviving side branch is

    (beta+eta)(N-1/2)+nu(Tj-1/2)>=0.                (18)

Equation (18) is not proved here. The upper-left KB vertex feature is
also separate. The completed theorem is precisely the whole side-feature
reduction above; no failed proof or numerical search is used as a
premise, and no roadmap gate, Lean compilation or CI is introduced.
