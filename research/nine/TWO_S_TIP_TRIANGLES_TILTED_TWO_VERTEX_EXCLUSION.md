# Two S-tip triangles cannot use the tilted two-vertex articulation interface

Date: October 27, 2026.

**Status: accepted complete whole-interface hand exclusion after full
root and separate independent reviews in
REVIEW_TWO_S_ALIGNED_NONPARALLEL_AND_TILTED_PW_ROOT_2026_10_27.md and
REVIEW_TWO_S_TILTED_TWO_VERTEX_HEXAGON_2026_10_27.md.**
This closes the entire strict P/W
interface of either tilted S root in the last C2.33.b2 attachment.
The other genuine S root keeps every actual frame and contact
owner. The proof uses its small physical point to shorten the
earlier intact-petal two-vertex calculation.

## 1. The original S/S graph and all genuine aggregates

Keep the original graph

    HA, AB, BH, HC, CD, DH, AL, CM,

with genuine S leaves L,M and degrees H4,A3,C3,B2,D2,L1,M1.
Both arbitrary completion squares remain fixed. The accepted
high-radius reductions supply

    O in int H,
    H,A,C physically circle-clear,
    B,D loaded degree-two tips,
    nonzero common cycle moment in each actual triangle.

Write

    D_0=sqrt(R^2-1/4)-1,
    delta=D_0-1,
    0<delta<1/60,
    103/50<R<=sqrt(1105)/16<21/10.

Assume A is tilted. Its full local chart and concurrence are

    A=D_0 e_x+[0,1]u+[0,1]v,
    u=(-a,-b),       v=(-b,a),
    a>b>0,           a^2+b^2=1,
    q_A=q e_x,       q>0,
    sigma=D_0-q,     0<=sigma<D_0.

The general local S-star routing has placed H at the low vertex
D_0 e_x+u and B at the adjacent far vertex D_0 e_x+u+v.
The original compatible fixed-star selection makes these two
strict A-vertex normals owned by H and B, respectively, with
both vertices in the relative interiors of the corresponding
neighbor sides. This is exactly the original prelisted P/W
interface, with arbitrary degrees and masks at its neighbors.

Use the orthonormal vector frame (-u,v), keeping the original
circle origin unchanged. Put

    X=1-sigma a,      Y=1-sigma b,      Z=sigma b,
    N_0=sqrt(X^2+Y^2),
    J=sqrt(X^2+Z^2),
    n=(-X,Y)/N_0,     v_B=(-Y,-X)/N_0,
    m=(-X,-Z)/J,      k=(Z,-X)/J,
    K=X/(N_0 J)>0,
    L=(X^2-YZ)/(N_0 J).

Here n points A to B and m points A to H. The actual ports are

    Q=(D_0 a-1,-D_0 b) in A intersect H,
    P=Q+(0,1) in A intersect B.                        (1)

Strictness gives X,Y>0. We have

    n=L m-K k,       v_B=K m+L k.                      (2)

Let g be the original B-to-H normal, gamma>0 its magnitude,
and mu,nu>0 the original AB,AH magnitudes. With the complete
opposite branch resultant S=F_D+F_M, the actual equations are

    F_B=mu n-gamma g,
    S=nu m+gamma g.                                    (3)

No degree-two equation has been placed at H or C.

## 2. The inner H face is strictly negative for an immediate geometric reason

Put rho_H=Q.m. Because O is in int H and Q is on H's
minimum-m face, rho_H<0. Its exact numerator is

    J rho_H=1-D_0 a+sigma(D_0-a)<0.                   (4)

The local algebra of this inequality gives

    D_0 a>1,
    a>60/61,
    b<11/61<3/16,
    0<=sigma<(D_0 a-1)/(D_0-a)<1,
    -delta<rho_H<0.                                    (5)

For the last bound use
rho_H=((1-D_0 a)X+D_0 b Z)/J>1-D_0.
All denominators in (5) are positive since D_0>1>a.

The actual B point has

    |P|^2=D_0^2+2-2D_0(a+b)<D_0^2.                  (6)

Every point of a two-circle-corner radial S unit has norm at
least D_0. Thus B has a unique physical circle corner.
The already compatible GENERAL_FIXED_TIP_NORMAL_SELECTION
removes a free BH normal: AB is a fixed side-interior application
on this unique B, and a free BH application would be a distinct
B vertex. Every actual shared-side BH alternative remains.

## 3. The complete mutual-owner cover retains only g=k or g=v_B

The physical triangle owned-normal lemma gives

    n.g<=0,        m.g>=0.                             (7)

Thus the possible B- or H-owned mutual normals are
g=-n, m, v_B, k. If g=-n, the real B forces are parallel
along its owned axis n, making B radial S; this contradicts (6).

If g=m, (3) makes S a positive multiple of the actual H axis m.
For any physical triangle pair whose sum is a positive root axis,
both actual root ports lie on that axis's maximizing face. Indeed
an owned transverse axis contradicts transverse balance and the
owned-normal nonobtuse lemma; a longitudinal axis makes both
normals parallel with the same sign; otherwise the two strict
vertex normals have opposite transverse signs and must use the
same vertical face by the opposite-vertices obstruction. Their
positive longitudinal sum chooses the maximizing face.

Apply that actual feature cover to H,C,D. Its relevant face has
height 1+rho_H>1-delta. In a nonparallel common-face pair, the
unchanged zero moment and proper negative-resultant concurrence
give every actual port support at least the face height, by
TWO_S_TIP_TRIANGLES_ALIGNED_NONPARALLEL_EXCLUSION.md, Section 4.
In a parallel axis pair the support equals that height directly.
But C contains its genuine point delta e_M, so the actual H-to-C
support is at most delta. Since 1-delta>delta, g=m is impossible.

For g=k, L<0 would place the mutual B point at P-rho v_B with
rho>0. Its m-coordinate relative to Q is -Z/J-rho K<0,
contrary to H's minimum-m support. L=0 gives k=-n, already
excluded. For g=v_B, L<0 instead places the mutual H point at
Q+t k with t>0. Its n-coordinate relative to P is -Y/N_0-tK<0,
contrary to B's minimum-n support. L=0 gives v_B=m, already
excluded. Consequently both remaining owners satisfy

    L>0,        K>=L.                                  (8)

The second inequality follows from L/K=X-YZ/X<=X<=1.
All original side means have survived this routing.

## 4. The H-owned transverse contact is excluded entirely by the real B tip

For either remaining owner, the unique B circle force has positive
n component and negative v_B component. Write its actual unit as

    B=P+[0,1]n+[-rho_B,1-rho_B]v_B,
    0<rho_B<1,      V=1-rho_B in (0,1),

and its actual circle corner as

    z_B=X_B n-Y_B v_B,
    rho=P.n,
    V_0=-P.v_B=q(a-b)/N_0>0,
    X_B=1+rho,
    Y_B=V_0+rho_B,
    X_B^2+Y_B^2=R^2.                                  (9)

The local bound from the original two-vertex calculation is

    rho=[2-(D_0+sigma)(a+b)+D_0 sigma]/N_0
         >=[2-D_0(a+b)]/sqrt(2)
         >761/(960 sqrt(2))>11/20.

For its monotonic step, differentiating with respect to sigma
gives rho'=q(a-b)^2/N_0^3>0. The remaining comparison uses
a+b<19/16 and D_0<61/60. Hence X_B>31/20>R/sqrt(2), so

    X_B>Y_B.                                           (10)

The genuine proper B advance from P along n is

    A_B=V_0 X_B/Y_B-rho>=0.

Its exact weighted-corner identity is

    (A_B-V)Y_B=-rho_B(X_B-Y_B)<0,
    A_B<V.                                             (11)

For g=k, the original mutual point is P+V v_B. Intersecting
its actual k line with the AB normal line gives

    A_B=VK/L>=V,

contradicting (11). This excludes the complete H-owned transverse
case without any hypothesis about the other triangle's frame.

## 5. The remaining owner forces a small actual H vertex

It remains g=v_B. Its original point has the form

    T=P+t n+V v_B,       0<=t<=1.

Its minimum-m condition on H gives the actual identity

    L t+K V=Z/J,
    V<=sigma b N_0/X.                                 (12)

In particular sigma>0. By (2)--(3),

    S.m>0,       S.k>0.

Write H's actual frame as

    H=Q+[0,1]m+[-eta,1-eta]k,       0<eta<1,
    q_k=Q.k=bq/J>0,
    p_k=q_k+1-eta>q_k.

The other triangle H,C,D has nonzero common moment. Its full
root-feature cover and C's genuine delta-point give exactly the
same conclusion as Section 5 of the aligned-nonparallel source:

    0<q_k<p_k<=delta.                                 (13)

To spell out the complete scope: except for two perpendicular
H-owned axes, its two ports share either H's positive-m face
or its positive-k face. Coincident nonparallel ports are impossible
because q_H=-tau S would have negative scalar product with S,
whereas every H support is strictly positive from O in int H.
The positive-m face has height 1+rho_H>1-delta and cannot carry
the small-point neighbor C by the common-face support inequality.
The positive-k face must therefore have height at most delta.
In the perpendicular exception the axes are precisely +m,+k;
C cannot use +m and hence uses +k, giving the same bound.

Together with (5), (13) makes the actual AH point satisfy

    |Q|^2=rho_H^2+q_k^2<2delta^2.

But its original coordinates in (1) give

    D_0 b<sqrt(2)delta<1/40,
    alpha:=D_0 a-1 in (0,delta),
    h:=1-D_0 b>39/40,
    P=(alpha,h).                                      (14)

No actual port or H mean has been moved to obtain this smallness.

## 6. B's actual normal cannot be almost vertical

Put beta=X/N_0 and a_B=Y/N_0, so

    n=(-beta,a_B),      v_B=(-a_B,-beta),
    beta,a_B>0,        beta^2+a_B^2=1.

For the actual B point P=(alpha,h), its proper radial advance
implies the same local inequality used in the aligned source:

    p_n(R-|P|)<=|P|,
    p_n=-alpha beta+h a_B.                            (15)

If a_B>=19/20, then beta<5/16,

    p_n>19h/20-1/192,
    |P|<h+1/6400.

Here h>39/40>361/400 and alpha<delta<1/60. The lower difference
in (15) is again

    (19h/20-1/192)(103/50-h-1/6400)-h-1/6400.

It is concave on [361/400,1] with positive endpoint values
1069997/12800000 and 2407/2048000. Therefore

    a_B<19/20,
    beta>sqrt(39)/20>3/10,
    N_0/X<10/3.                                       (16)

Using (5),(12),(14),(16), every remaining actual mean obeys

    V<=sigma b N_0/X
       <(sqrt(2)/60)(10/3)
       =sqrt(2)/18<2/25.                             (17)

The last comparison is exact: 25sqrt(2)<36 since 1250<1296.

## 7. The actual circle corner lies beyond R

Equation (9) gives the original physical circle corner

    z_B=P+n-v_B+V v_B.

Since P=(alpha,h),

    |P+n-v_B|
      >=sqrt((a_B-beta)^2+(h+a_B+beta)^2)-alpha
      >=sqrt(h^2+2h+2)-alpha
      >11/5-alpha.

The middle inequality uses a_B+beta>=1; the last uses h>39/40.
Together with (14),(17),

    |z_B|>11/5-1/60-2/25
          =631/300>21/10>R.

This contradicts |z_B|=R and excludes the B-owned transverse
case. All mutual owners were covered in Sections 3--5, so the
entire tilted P/W articulation is impossible.

The argument retains every actual B mask, force, side mean and
normal allowed by the original compatible selection, the full
degree-three C root and its genuine S leaf, and both completion
squares. No intact-petal pressure, fictitious boundary C premise,
new normal reselection, numerical pose, Lean compilation or CI
is used. The A-owned +u tilted interface remains separate.
