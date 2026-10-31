# The near-corner transmitter return of the low aligned S-leaf C5 is excluded

Date: October 27, 2026.

**Status: complete hand theorem, submitted for full root and separate
independent review.** This closes the entire remaining actual near-corner
return, including zero proper distances. All original nine units, true
degrees, circle masks, forces, normals and shared means remain.

## 1. The exact original branch and the unchanged side channel

Keep the original component

    H--B--X--C--D--H,       H--L,

where H is a genuine S-leaf root of true degree three, B,C,D are
loaded true degree-two bodies and X is the real unloaded degree-two
transmitter. Work in the complete aligned strict-low root domain

    2<R<sqrt(17)/2.

The entire local root and upper-return sources are

    S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md,
    ALIGNED_LOW_S_ROOT_UPPER_BOUNDARY_RETURN_EXCLUSION.md.

Their full independent reviews are
REVIEW_ALIGNED_LOW_S1234_HEXAGON_2026_10_27.md and
REVIEW_ALIGNED_LOW_UPPER_BOUNDARY_RETURN_TRIANGLE_BRIDGES_2026_10_27.md.
Only the root-local sections of the first source are imported;
its four-boundary-path conclusion is not used here.

Those sources force the displayed placement of X and the following
actual B frame. With n=(-c,s), j=(-s,-c), c,s>0, retain the original
orthonormal coordinates (n,j), whose origin is still the circle origin:

    B=[N,N+1] times[-W,1-W],
    P_HB=(N,-K),
    W=K+rho,          7/8<rho<=1,
    N^2+K^2<101/225,
    R^2=(N+1)^2+W^2.                                 (1)

B has exactly the physical circle corner (N+1,-W). Its full original
concurrence is

    q_B=(N+lambda,-K),
    lambda=(K-N rho)/W>=0.                            (2)

The actual B-to-X normal g has positive j component. The far B return
has already been excluded for every contained neighbor. The owned-j
return is separately excluded by
ALIGNED_LOW_S_C5_OWNED_SIDE_TRANSMITTER_EXCLUSION.md. We take precisely
the remaining strict near-corner feature:

    g=(-kappa,1)/z,       kappa>0, z=sqrt(1+kappa^2),
    Q=P_BX=(N,1-W).                                   (3)

This is a strict B vertex because both normal components are nonzero.
The original compatible diagonal-transmitter avoidance now excludes
a diagonal X: its endpoint would also be an X vertex and the selected
point normal would equal that actual X diagonal. This is the global
selection convention explicitly used in Section3 of
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md and Section4 of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md. We use only that local convention,
not either source's separate whole-component theorem.

Thus X has its original side width one. Its full unchanged force and
torque transmit the original point by exactly g:

    P=P_XC=Q+g,
    C subset {v:g dot v>=P dot g}.                    (4)

Every actual transverse mean of X remains unchanged. No physical
B--C edge or shortened force at B,C,D is introduced.

## 2. The full B2 equation supplies an exact two-parameter identity

Put

    S=N+1,       delta=1-rho,       0<=delta<1/8.

Properness at the actual return (3) gives

    lambda=kappa delta.                              (5)

This identity includes delta=lambda=0. We never divide by delta.
Substitute (2), K=W-rho and N=S-1 into (5):

    S/W=(1-kappa delta)/(1-delta).                    (6)

Let beta>0 be the unchanged positive scalar of B's circle resultant
beta(S,-W), and let mu>0 be its original HB magnitude. The full B2
force equation, using its j and then n components, gives

    mu=beta(S-kappa W)>0.

Together with (6), this proves

    0<kappa<1,
    1<=S/W<=(8-kappa)/7<=8/7.                        (7)

The equality S=W is retained when delta=0. In particular

    W>14/sqrt(113)>13/10,
    S>=R/sqrt(2)>sqrt(2),
    W<=R/sqrt(2)<3/2.                                (8)

The first rational comparison has squared reserve503 after clearing
the positive denominator100*113. Also

    |Q|^2=N^2+(W-1)^2<=N^2+K^2<101/225.              (9)

## 3. A complete scalar comparison forces kappa<2/5

The actual point P in (4) belongs to a physical boundary unit C.
Therefore

    |P|>=R-sqrt(2).                                  (10)

We show that kappa>=2/5 contradicts this, over the whole retained
parameter interval, not only at a selected pose.

Write S=R cos(phi), W=R sin(phi). By (6)--(7),

    atan(7/8)<=phi<=pi/4,
    tan(phi)=(1-delta)/(1-kappa delta).

Direct expansion of (4) gives

    |P|^2-(R-sqrt(2))^2=D(R,kappa,phi),

    D=1+2(1+kappa)/z-2R B,
    B=cos(phi)+sin(phi)
       +(kappa cos(phi)+sin(phi))/z-sqrt(2).           (11)

Here B>0. For example cos(phi)+sin(phi)>=1,
sin(phi)/z>=7/sqrt(226)>7/16 and sqrt(2)<23/16
already give that strict sign. Consequently D decreases in R.

For fixed kappa, B increases strictly with phi, since

    partial_phi B=cos(phi)-sin(phi)
                   +(cos(phi)-kappa sin(phi))/z>0.

Increasing delta decreases phi, so D increases with delta. For
fixed phi its kappa derivative is

    partial_kappa D
      =2[(1-kappa)-R(cos(phi)-kappa sin(phi))]/z^3<0,  (12)

because cos(phi)-kappa sin(phi)>=(1-kappa)/sqrt(2)
and R>2. Increasing kappa at fixed delta also increases phi,
which further decreases D. Thus for every kappa>=2/5 in (7),
the largest comparison is at R=2, delta=1/8, kappa=2/5.

At that comparison cos(phi)=38/sqrt(2669),
sin(phi)=35/sqrt(2669), and

    D_*=1+14/sqrt(29)+4sqrt(2)
                -4[73/sqrt(2669)+251/sqrt(77401)]<0. (13)

For an explicit short rational check, use

    sqrt(29)>5385/1000,
    sqrt(2669)<51663/1000,
    sqrt(77401)<278211/1000,
    sqrt(2)<99/70.

The first three squared reserves are1775,65569,360521. Substitution
in (13) gives the strict upper bound

    -230482055743/60199815043515<0.

This contradicts (10), and proves

    0<kappa<2/5.                                     (14)

The comparison includes delta=0. It neither changes an original
force nor selects an auxiliary physical configuration.

## 4. The genuine C port has a short linear bound

Write its actual (n,j) coordinates as

    P=(p,y),
    p=S-1-kappa/z,
    y=1-W+1/z.                                       (15)

Equations (8), (14) give p>0 and y>9/22>0. Indeed
S-1>sqrt(2)-1>2/5>kappa/z, while W<3/2 and
1/z>5/sqrt(29)>10/11.

Its actual minimum g support is

    H_C=P dot g
       =1-[kappa(S-1)+W-1]/z.

Since S>=W and W>13/10, while (1+kappa)/z>=1, we have

    3/10<H_C<7/10.                                  (16)

The lower bound follows directly from (4), (9):
H_C=1+Q dot g>1-|Q|>3/10. Moreover

    |P|^2=|Q|^2+2H_C-1<191/225<1.                   (17)

The remaining bound needed below is

    y-p/3<11/20.                                     (18)

Here is a one-variable proof over all original means. If T=S/W,
the function (1+T/3)/sqrt(1+T^2) decreases for T>=1.
Thus R>2 and (7) imply

    W+S/3>2(29-kappa)/[3sqrt((8-kappa)^2+49)].

By (15), y-p/3 is strictly below

    F(kappa)=4/3+(3+kappa)/(3sqrt(1+kappa^2))
                   -2(29-kappa)/[3sqrt((8-kappa)^2+49)].             (19)

On 0<=kappa<=2/5, this is uniformly concave:

    F''(kappa)<-3/5.                                 (20)

To check (20), put z=sqrt(1+kappa^2), x=8-kappa and
A=(3+kappa)/z, B=(29-kappa)/sqrt((8-kappa)^2+49).
Then

    A''/3=(2kappa+1)(kappa-1)/z^5,
    B''=21(2x^2-7x-49)/(x^2+49)^(5/2)>0.

Here x>=38/5 makes the numerator in parentheses at least333/25.
Also (1-kappa)(2kappa+1)>=1 and z^5<(11/10)^5<5/3.
These inequalities prove (20).

At kappa=1/4,

    F(1/4)=4/3+13/(3sqrt(17))-230/(3sqrt(1745))<5491/10000,
    F'(1/4)=[16/(17sqrt(17))-14560/(1745sqrt(1745))]/3,
    0<F'(1/4)<1/50.                                  (21)

For the first comparison, sqrt(17)>41231/10000 and
sqrt(1745)<417732/10000 have squared reserves4639 and23824;
the resulting reserve below5491/10000 is
10981279879/129176310690000. For the derivative, the simpler bounds
4<sqrt(17)<33/8 and167/4<sqrt(1745)<42 give positive lower
bound925696/98090289 and upper reserve20797/2669850 below1/50.

The global Taylor inequality from (20), completing one square, gives

    F(kappa)<=F(1/4)+F'(1/4)(kappa-1/4)
                           -(3/10)(kappa-1/4)^2
             <=F(1/4)+(5/6)F'(1/4)^2
              <5491/10000+1/3000<11/20.              (22)

The last reserve is17/30000. This proves (18) on the whole interval.

## 5. Every actual C frame has positive n center coordinate

C is a loaded true degree-two unit and its original neighbor D is
physically boundary. Therefore the full original local theorem
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, applies. Its actual
concurrence q_C is a positive multiple of the full circle resultant,
and its incoming proper relation is

    q_C=P+ell g,       ell>=0.                        (23)

This keeps ell=0 and does not initially assert that q_C is inside
a physical two-corner unit.

Put l=(n+kappa j)/z, so (l,g) is an orthonormal frame. The actual
port has positive l coordinate (p+kappa y)/z. Equation (23) gives
the same coordinate for q_C. Consequently the original circle
resultant has strictly positive l component.

### 5.1. C owns its incoming g axis

The actual C box has g interval [H_C,H_C+1]. Since H_C>0, its
physical circle corners can occur only on the outer g face. The
positive l component of the full resultant supplies a positive-l
circle corner Z, necessarily the upper l endpoint of that face.
By (16),

    Z dot l=sqrt(R^2-(H_C+1)^2)>sqrt(111)/10>21/20.

The last squared reserve is3/400. Thus its unchanged center has

    c_C dot l>11/20,       c_C dot g<6/5,
    c_C dot n=[c_C dot l-kappa(c_C dot g)]/z
              >7/(100z)>0.                           (24)

No actual incoming side mean has been fixed. This argument also
handles all initial two-corner/zero-individual-weight possibilities:
the actual positive-l circle corner and containment force the stated
center, rather than an assumed one-corner resultant.

### 5.2. C does not own g

Now P is the actual minimum-g vertex. By (17), that vertex and its
two adjacent vertices have norm less than2<R. Therefore its only
physical circle corner is the actual opposite vertex Z. This proves
the physical mask before using it.

Equation (23), together with y>0 and g_j>0, makes Z_j>0.
Suppose c_C dot n<=0. Since c_C=(P+Z)/2 and p>0, write

    Z_n=-u,       u>=p>0.

The actual opposite-corner distance is sqrt(2), so u+p<=sqrt(2)
and

    Z_j<=y+sqrt(2-(u+p)^2).

For fixed p,y>0, the function

    u^2+[y+sqrt(2-(u+p)^2)]^2

strictly decreases for u>=p on its domain: its derivative is
-2p-2y(u+p)/sqrt(2-(u+p)^2). The endpoint follows by continuity.
Consequently p<=1/sqrt(2) and

    R^2<=2-3p^2+y^2+2y sqrt(2-4p^2).                 (25)

Use (18) and sqrt(2-4p^2)<=sqrt(2)(1-p^2)<(99/70)(1-p^2).
After expanding and dropping the negative cubic term, (25) gives

    R^2<10803/2800+(55/42)p-(28001/6300)p^2
       <=310057303/78402800
        =4-3553897/78402800<4.                        (26)

This contradicts R>2. Thus c_C dot n>0 also in the entire strict
vertex case. Every actual inward frame and every proper-distance
endpoint has been included.

In both cases the actual support (16) also gives c_C dot g>0.
As j=z g+kappa n, we have proved

    c_C dot n>0,       c_C dot j>0.                   (27)

## 6. The original C--D contact contradicts the actual center strip

The fully reviewed local source

    ALIGNED_LOW_S_ROOT_LOWER_BOUNDARY_UNIQUE_CORNER_AND_CENTER.md

has exactly the same original root chart and true D2 with boundary
neighbor C. It imposes no condition on the upper return or X width.
It proves, retaining the weak lower-tilt equality and every original
mean,

    c_D dot n<0,       c_D dot j<1/2.                 (28)

Its full independent acceptance is
REVIEW_LOW_S124_LOWER_CENTER_AND_OWNED_RETURN_ROOTED_BLOCKS_2026_10_27.md.

Equations (27)--(28) imply

    c_C dot c_D<(c_C dot j)/2<=|c_C|/2.

Both C,D are actual physical boundary units. Since R>2,

    |c_C|>9/7,       |c_D|^2>5/3.

The first inequality uses 1/sqrt(2)<5/7; the second follows from
sqrt(2)<17/12. Therefore

    |c_C-c_D|^2>|c_D|^2+|c_C|^2-|c_C|
                >5/3+81/49-9/7
                 =2+5/147>2.                        (29)

Their real physical contact puts each center within1/sqrt(2) of
the same point, so their squared separation is at most2. This
contradicts (29).

## 7. Exact original conclusion

The complete original near-corner return (3) is impossible. The
argument includes delta=lambda=0, all actual X side means, every
C frame and original mask, the weak lower-D tilt endpoint, and
the full true B2/C2/D2 equations. The original diagonal X alternative
was excluded only by the already compatible global point-normal
selection; no selected normal was changed after extraction.

Together with the separately complete upper-return and owned-side
sources, this closes the entire aligned strict-low S124 root domain.
The high and tilted domains retain their separate complete sources
and require the exact whole-family join. This manuscript does not
silently claim a broader load family or a coarse-cell closure.

All nine physical units and all three arbitrary completion units
remain. No sampled pose, numerical root, altered force or mean,
Lean compilation, CI, remote action or shared-metadata edit is a
premise of the proof.
