# The aligned S123 Southwest root cannot have a radial far endpoint

Date: October 27, 2026.

**Status: complete hand original-mask exclusion with an exact rational
scalar certificate, submitted for full root and separate independent
review.** Together with the independently accepted unique-far source,
this closes the entire aligned Southwest direct-normal feature.
The actual South direct normal remains a separate feature.

## 1. Exact original component and the accepted complete domain

Retain exactly the original component

    A--B--M--C--U--A,       A--L,

with true A3, genuine S leaf L, true loaded B2,M2,C2 and the
actual unloaded side transmitter U2. Keep all nine units, every
actual normal, physical circle mask, individual zero weight,
shared-side mean and original force and torque equation.

Use the fully independently accepted necessary-domain theorem
S_LEAF_C5_ALIGNED_SOUTHWEST_ROOT_DOMAIN.md, SHA256
9ccacf5e8fa7553a7505ed319b829fa938ce74b053a60253927cba70f156398c,
with REVIEW_S123_ALIGNED_SOUTHWEST_DOMAIN_AND_UNIQUE_FAR_ROOTED_BLOCKS_2026_10_27.md.
Its exact current domain is

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    A=[epsilon,d] x [-b,a],       a+b=1,
    0<a<29/100,       K>0,
    n=(-K,a)/L_a,     m=(-K,-b)/L_b,
    L_a=sqrt(K^2+a^2), L_b=sqrt(K^2+b^2).

Here n is the actual A--U normal and m the actual A--B
normal. B owns m by the original compatible singleton
selection already proved in that source, and B is physical
unique. C owns n. Take exactly the radial-C mask:

    a^2=2epsilon*K+epsilon^2,
    epsilon=L_a-K=a^2/(L_a+K),
    C=[d,d+1]n+[-1/2,1/2]f,       f=Jn.              (1)

The real incoming C mean has f coordinate -a<0. Both
physical C circle corners and both original weights remain.

In the actual B frame (m,j), j=Jm, the complete unchanged
box and full B2 proper concurrence are

    N=(b^2-epsilon*K)/L_b,
    z=b*(K+epsilon)/L_b,
    S=N+1,       W=sqrt(R^2-S^2),
    B=[N,N+1]m+[W-1,W]j,
    Z_B=S*m+W*j,
    lambda=z*S/W-N in[0,1],
    eta=z+1-W in[0,1].                               (2)

No actual mean has been chosen to obtain these equalities.
The inside-unit concurrence clause is used only for this
proved unique physical B mask.

## 2. Exact positive support and a compact whole K range

First N>0. Indeed (1) gives

    b^2-epsilon*K
       =1-2a+a^2/2+epsilon^2/2
       >9241/20000>0.

Also N<b<1. Since a>epsilon and 0<a<1,

    r_P:=sqrt(epsilon^2+b^2)<1.

Equations (2) give

    1/2<W<11/6.                                     (3)

For the upper bound use R^2-(N+1)^2<1105/256-1;
the squared comparison with (11/6)^2 has reserve103/2304.

### 2.1. The actual proper B star forces K>1/4

Suppose K<=1/4. Equation (1) implies
a^2<31/3600<1/100, so b>9/10. The actual incoming
angle then satisfies

    N/r_P
      =[1-epsilon*K/b^2]
        /[sqrt(1+(K/b)^2)*sqrt(1+(epsilon/b)^2)]
      >(179/180)*(25/26)*(1000/1001)
       =20/21+335/117117>20/21.                      (4)

Here epsilon*K/b^2<5/972<1/180,
sqrt(1+(K/b)^2)<26/25 with squared reserve899/202500,
and sqrt(1+(epsilon/b)^2)<1001/1000 with squared
reserve1208729/729000000.

The full original properness lambda>=0 gives

    R*N<=r_P*(N+1).

Thus (4) and r_P<1 imply R<41/20<sqrt(17)/2, a
contradiction. The last squared reserve is19/400.

### 2.2. The actual loaded boundary path forces K<7

Write

    m=D0*n+E0*f,
    D0=(K^2-a*b)/(L_a*L_b),
    E0=K/(L_a*L_b)>0,
    kappa=D0/E0=K-a*b/K.                             (5)

The actual B center has coordinates

    B_n=(N+1/2)D0-(W-1/2)E0,
    B_f=(N+1/2)E0+(W-1/2)D0.                        (6)

The actual C center lies on the positive n axis. The real
B--M--C boundary path puts M between B,C in circular order;
each successive gap exceeds40 degrees and their sum is the
minor endpoint gap. This is the exact physical path theorem
used in Section2 of FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md.
In particular the minor B,C angle exceeds80 degrees. Hence

    B_n<cot(80 degrees)*|B_f|<(9/50)|B_f|.           (7)

The rational last comparison needs no numerical angle
estimate. Put alpha=pi/18<11/63. Then
sin(alpha)<11/63 and cos(alpha)>7817/7938, so
cot(80 degrees)=tan(alpha)<1386/7817<9/50,
with final reserve1053/390850.

If K>=7, then kappa>K-1/(4K)>0, so B_f>0. Equations
(3),(6) give

    (B_n-B_f/5)/E0
      =(N+1/2)(kappa-1/5)
          -(W-1/2)(1+kappa/5)
      >(7/30)kappa-43/30
      >(7/30)(K-1/(4K))-43/30
      >=23/120>0.

This contradicts (7). Therefore the entire actual range is

    1/4<K<7.                                        (8)

The loaded M has been used as an actual boundary-path body,
not contracted to a transmitter or omitted from a force sum.

## 3. Exact original return bounds

The unique B circle has positive j coordinate. The full
unchanged B2 equation therefore makes its return normal
have negative j component. Its complete actual feature cover is

| Return | Actual B point in (m,j) | Actual direction |
| --- | --- | --- |
| Near vertex | (N,W-1) | proportional to (-lambda,-eta) |
| Owned -j side | (zS/W,W-1) | -j |
| Far vertex | (S,W-1) | proportional to (1-lambda,-eta) |

If a displayed vertex direction could have zero length,
retain the original endpoint until its actual boundary-contact
guard below is imposed. In particular the far direction never
vanishes: lambda=1 implies z=W and eta=1.

Apply S123_ALIGNED_RADIAL_SOUTHWEST_PORT_SCALAR_CERTIFICATE.md.
Equations (1)--(8) verify every original scalar guard, with
no pose or mean substituted. At either remaining B--M point
Q the physical sharp boundary-contact theorem gives

    |Q|>=sqrt(R^2-1)-1.

The exact rational certificate therefore proves

    D0>1/4,
    h_far>61/60>d,
    1/10<Q_n<3/4,       1/2<Q_f<43/50               (9)

for the near and owned-side returns.

A contained unit beyond minimum support h has center
projection at least h+1/2, while the universal center bound
is |c|<=d+1/2. Hence an actual neighbor support cannot
exceed d. The strict far support in (9) excludes that
whole feature, including every physical M mask.

The finite certificate uses a two-variable closed rational
box and outward integer arithmetic only. It has18980 splits,
13096 accepted boxes and5885 guard-excluded boxes, maximum
depth21. The full explicit tree rule, six endpoint extrema,
strict rational reserves and reproducible checker are supplied
with the scalar source.

## 4. Both retained actual normals have g_n>0>g_f

For the owned return, -j=E0*n-D0*f, so (9) gives the
claim immediately.

For the near return, the actual sharp boundary-point inequality
and N>0 give W<=1 and N>=sqrt(R^2-1)-1>4/5. These
are the exact equalities and inequalities proved in Section4
of the scalar source. Since

    N<(b^2)/sqrt(K^2+b^2)<=1/sqrt(K^2+1),

we obtain K<3/4. Consequently

    0<D0/E0=K-a*b/K<K<3/4.

Also eta=z+1-W>0. Its endpoint eta=1 would imply z=W,
making the actual incoming point P one unit from the circle
corner Z_B. This contradicts |P|=r_P<1<R-1. Thus

    0<eta<1,
    lambda-eta=-(S-W)(1-eta)/W<0.

The actual near normal is therefore nonzero, with channel
components proportional to

    g_n=eta*E0-lambda*D0>0,
    g_f=-lambda*E0-eta*D0<0.                         (10)

This keeps lambda=0 and W=1. No original normal is inferred
from a vanished concurrence vector.

## 5. The full true-M2 star excludes the two retained returns

The full radial-C equation and its original incoming mean
f=-a<0 imply that the actual C-to-M normal h has h_f>0.
An h_n>0 support would expose an unshareable physical circle
corner. Thus exactly these original alternatives remain:

    h_n<0: P_CM=(d,1/2),
    h_n=0: P_CM=(X,1/2), X>=d, h=f.                 (11)

All original C corner weights, including an individual zero
weight, are still present.

If h_n<0, (9) gives the strict actual chord bound

    |Q-(d,1/2)|^2
       <(61/60-1/10)^2+(43/50-1/2)^2
       =1-2711/90000<1.                             (12)

But the two actual outward normals of M are -g,-h.
Equations (10),(11) make their dot product negative. The
complete unit-square support/feature lemma in Section2 of
RADIAL_BOUNDARY_UPPER_CONTACT_LOADED_MIDDLE_SHORT_PORT_EXCLUSION.md
then requires its two actual ports to be at least one unit
apart. That local section requires only the literal chord
condition (12), not its narrower rectangular sufficient bounds.
This exact broader scope was checked in
REVIEW_RADIAL_UPPER_LOADED_MIDDLE_SHORT_PORT_HEXAGON_2026_10_27.md.

For h=f, Section3 of that same complete local source applies
with Q_f<43/50<9/10 and g_n>0>g_f. For clarity its proof
does not use a lower bound on Q_n. If M owns its incoming
f axis, the other support lies at height at least3/2, already
impossible. Otherwise its minimum-f point (X,1/2) is a strict
vertex. Write the two inward axes (-c,s),(s,c), c,s>0.
The full feature cover and Q_f<9/10 force s<2/5,c>9/10
and put Q on the left-adjacent vertex or its adjoining owned
side. Comparing all four actual corners makes M physical
unique, with circle corner

    Z=(X+s,1/2+c).

The full true-M2 proper radial concurrence has n coordinate
X on the actual C-force line, so its f coordinate is

    X(1/2+c)/(X+s)>1.

On the other unchanged proper line it equals Q+t*g for
t>=0, hence its f coordinate is at most Q_f<9/10.
This is the contradiction. This argument proves the unique
mask before using it and retains all original C side means,
both M forces, zero proper-distance endpoints and all loads.

## 6. Exact whole-feature join

Every actual return in the radial-C mask has now been excluded.
The complementary unique-C mask is already independently
accepted in S_LEAF_C5_ALIGNED_SOUTHWEST_UNIQUE_FAR_EXCLUSION.md,
SHA256 0d46e1520aca8f57cc040149c1aa7da4cf4338396524ffe15c8697b416e38ad0,
with the same rooted-blocks complete independent review named
in Section1. The necessary-domain source proves that these
are all physical C masks and that C owns its incoming axis.
Together they exclude the entire original high aligned
Southwest direct-normal feature.

The actual South direct normal remains separate; no whole
S123 fine gate or coarse cell is claimed here. All nine units,
the real loaded B--M--C path and all actual original means
and forces are retained. No numerical pose, compilation, CI,
shared metadata change, normal reselection or remote action
is used.
