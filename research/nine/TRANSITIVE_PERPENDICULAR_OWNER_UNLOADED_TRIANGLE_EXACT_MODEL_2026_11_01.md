# Transitive perpendicular side ownership: complete original moment reduction and two smooth variance roots

November 1, 2026. PR #11 continuation. **Evidence at construction: H for the exact physical and analytic reduction; exhaustive arithmetic certification and independent replay are recorded separately.**

## 1. Entire original feature and actual contact geometry

Retain the same original physical force-and-torque certificate, all nine actual squares and their complete physical contacts, applications, means, loads and circle masks. Three actual squares A,B,C are selected-circle-unloaded and have exactly the three positive internal triangle edges and one original positive outside exit each. Outside terminals may repeat and have arbitrary frames, degrees, loads and additional contacts.

Assume the three actual internal intersections are distinct singletons, the core frames are pairwise nonparallel, and the transitive side-owner pattern is C owns CA and CB, A owns AB. Every owner point is side-interior and every nonowner is a strictly exposed vertex. Here the two C-owned normals are **perpendicular**, rather than equal or opposite.

Normalize the actual square and its original applications as

    C=[0,1] x [0,1],
    p_CA=(1,s_0),       p_CB=(t_0,1),
    0<s_0,t_0<1,

with the C-to-A direction East and the C-to-B direction North. Reflections and rotations provide this ordering without changing which square owns AB.

A has p_CA as its unique leftmost vertex. Write its inward axes as

    u=(c,s),       v=(s,-c),
    c,s>0,        c^2+s^2=1,
    A=p_CA+[0,1]u+[0,1]v.

The side-normal triangle theorem [UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md](UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md) gives nonnegative dot product between the A-owned AB normal and the A-to-C direction West. Its possible own axes are -u and -v. The -u option has its support side through p_CA in direction v; every side-interior application there has height below s_0<1, whereas all actual B points have height at least 1. Hence only

    n_AB=-v=(-s,c)

is possible, with its unchanged original side-interior application

    P=p_CA+ell u,       0<ell<1.                  (1)

B has p_CB as its unique bottommost vertex. Its other original application P is a distinct strict vertex. The actual returns A,C touch, so the radius-free opposite-strict-vertex lemma in [UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md](UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md), Section 2.3, makes these B vertices adjacent. Since P has horizontal coordinate greater than 1>t_0, it is the right vertex, not the left one. Therefore for some c_1,s_1>0 with c_1^2+s_1^2=1,

    U=(c_1,s_1),       V=(-s_1,c_1),
    B=p_CB+[0,1]U+[0,1]V,
    P=p_CB+U.

Comparing coordinates in (1) gives the entire exact contact chart

    s_0=1+s_1-ell s,
    t_0=1-c_1+ell c,
    0<s_1<ell s.                                  (2)

The final inequality is exactly s_0<1. It implies s_1<s, hence c_1>c. The remaining strict bounds 0<s_0,t_0<1 follow from the physical premises; the displayed formulas below preserve their full domain.

Put

    K=s c_1-c s_1>0,
    L=c c_1+s s_1>0.                              (3)

These are the sine and cosine of the positive angle between u and U.

## 2. Full A torque forces an acute half-quadrant; full B torque forces its original side mean

Let the positive original CA,CB,AB magnitudes be a,t,b. Normalize the entire original system by b>0, so the oriented internal vectors become

    C-to-A=(a,0),
    C-to-B=(0,t),
    A-to-B=(-s,c).

The full outside vectors, without deleting any original force, are

    E_A=(a+s,-c),
    E_B=(-s,t+c),
    E_C=(-a,-t).                                  (4)

At A, E_A dot u=ac>0 and E_A dot v=1+as>0. Its original outside application is forced to the opposite vertex

    q_A=p_CA+u+v.

The full A moment about p_CA is

    ell+det(u+v,E_A)=0,
    1-ell=a(c-s).                                 (5)

Thus c>s>0. In angular notation 0<arg(u)<pi/4, and since s_1<s, also 0<arg(U)<arg(u). Equation (5) retains the original positive magnitude as

    a=(1-ell)/(c-s)>0.

At B, the two own components of E_B are

    F_U=t s_1-K,
    F_V=t c_1+L>0.                                (6)

Its incoming original AB force at P=p_CB+U is (s,-c), whose moment about p_CB is -L. If the original outside application is p_CB+V+epsilon U, its complete moment is

    -L+epsilon F_V-F_U=0.                         (7)

If F_U>0, its actual strict support is epsilon=1. Equation (7) becomes

    t(c_1-s_1)+K=0,

impossible since c_1>s_1 and K>0. If F_U<0, its support is epsilon=0 and (7) becomes

    t s_1=K-L,

also impossible, since

    K-L=-(c-s)c_1-(c+s)s_1<0.

Therefore the **only** remaining original feature is F_U=0. The outside normal is exactly V and

    t=K/s_1,
    E_B=(s/s_1)V.

The original side application is retained and (7) forces its exact parameter

    epsilon=L s_1/s,        0<epsilon<1,
    q_B=p_CB+V+epsilon U.                         (8)

No normal or side mean has been chosen after stress extraction; both follow from all original equations.

## 3. C's full moment and the actual outside points

C's outside vector E_C is strict Southwest, so its original application is its corner (0,0). Its complete moment equation is

    -a s_0+t t_0=0,
    a/t=t_0/s_0.                                 (9)

The three unchanged outside squares therefore contain the actual points

    W_A=q_A+(a+s,-c)/sqrt((a+s)^2+c^2),
    W_B=p_CB+2V+epsilon U,
    W_C=(-t_0,-s_0)/sqrt(t_0^2+s_0^2).             (10)

Here (9) was used to express the original Southwest unit normal entirely through the two actual C means. The support-unit-step fact behind (10) is valid for every outside frame and mean: at a minimum support point q, adding a unit normal moves each own-coordinate component inward by at most one, so q+e belongs to the same actual outside square.

The additional positive-force scalar relation

    (K/s_1)t_0=[(1-ell)/(c-s)]s_0                 (11)

is retained in the original physical domain. For a stronger certificate it is legitimate to drop this one constraint after using its exact implication (9): the resulting larger point domain still contains every actual triple in (10). This is a proof relaxation, not a replacement certificate for the packing.

## 4. A smooth closed parameter box retains every physical limiting direction

Write r=s_1/s, which satisfies 0<r<ell<1. Then

    0<s<1/sqrt(2),      c=sqrt(1-s^2),
    0<r<ell<1,
    s_1=r s,           c_1=sqrt(1-r^2 s^2),
    s_0=1-(ell-r)s,
    t_0=1-c_1+ell c,
    L=c c_1+s s_1,
    epsilon=r L.                                  (12)

For exact arithmetic use the closed enlarged region

    0<=s<=1/sqrt(2),      0<=r<=ell<=1.            (13)

All expressions in W_B and W_C are continuous there. In particular

    s_0>=1-s>=1-1/sqrt(2)>0,

so W_C's denominator has a uniform positive lower bound. Also 0<=t_0<=1, 0<s_0<=1 and 0<=epsilon<=1 throughout the enlarged region. Its angular/zero-force boundaries are closed proof enclosures; no original positive force has been silently set to zero.

The remaining potentially singular A direction near c=s and ell=1 is eliminated by the following exact two-endpoint argument.

## 5. Exact variance reduction to two explicit A directions

Let

    q_A=(1+c+s, s_0+s-c),
    M=(W_B+W_C)/2,
    v_0=q_A-M.

We first establish on the entire closed region (13)

    q_A,x>=2,      q_A,y<=1,
    W_B,x<=2,      W_B,y>=3,
    W_C,x<=0,      W_C,y>=-1.                     (14)

The q_A bounds follow from c+s>=1, c>=s and s_0<=1. The upper horizontal bound for W_B follows from t_0<=1, epsilon<=1 and c_1<=1. The W_C bounds follow directly from its negative unit direction.

For the remaining lower height bound, when s>0,

    W_B,y=1+2c_1+epsilon s_1
          =1+2c_1+(c/s)c_1 s_1^2+s_1^3
          >=1+c_1(2+s_1^2)+s_1^3.

If s_1>0, the two positive sides c_1(2+s_1^2) and 2-s_1^3 have squared difference

    c_1^2(2+s_1^2)^2-(2-s_1^3)^2
      =s_1^3(4-3s_1-2s_1^3)>0.

Indeed s_1<=1/sqrt(2)<3/4 makes 3s_1+2s_1^3<99/32<4. Thus W_B,y>3. At s_1=0, including the whole s=0 boundary, the exact formula gives W_B,y=3. This proves every bound in (14).

Consequently v_0,x>=1 and v_0,y<=0.

In the original positive-force domain, the A unit direction in (10) has the form

    e_A=(cos(delta),-sin(delta)),
    0<=delta<=arccos(s).

This follows from a>=0: its horizontal component is at least s, with the limiting directions (s,-c) at a=0 and (1,0) as a grows. For fixed q_A,W_B,W_C, the equally weighted variance of q_A+e_A,W_B,W_C depends on e_A only through

    (4/9) v_0 dot e_A
       =(4/9)[v_0,x cos(delta)-v_0,y sin(delta)],

plus a constant, since |e_A|=1. The bracket is positive and concave on this entire quarter-circle interval: its second derivative is its negative. Its minimum is therefore at an endpoint.

It follows that the actual three-point variance is at least the smaller of the variances obtained by the two **auxiliary** replacements

    e_A^(0)=(1,0),
    e_A^(1)=(s,-c).                               (15)

These replacements are only a rigorous scalar lower bound for variance. They are not asserted to be actual contacts or altered original outside squares. All actual W_A,W_B,W_C remain as in (10); the inequality proved here is what permits the two certificate roots.

## 6. Exact arithmetic certificate interface

For j in {0,1}, define

    Z_A^(j)=q_A+e_A^(j),
    Z_B=W_B,
    Z_C=W_C,

using the smooth closed formulas (12)--(15). It suffices to prove on the entire closed region (13) that both exact variances

    V_j=(|Z_A^(j)-Z_B|^2+|Z_B-Z_C|^2+|Z_C-Z_A^(j)|^2)/9

are strictly larger than 625/144. Section 5 then gives that bound for the actual variance, while actual disk containment gives actual variance<=R^2. The resulting R>25/12 contradicts R^2<=1105/256, with rational reserve 55/2304 in squared radii.

A rational rectangular chart can be obtained with the half-angle parameter p:

    c=(1-p^2)/(1+p^2),
    s=2p/(1+p^2),
    0<=p<=1/2,
    1-p^2-2p>=0,
    0<=r,z<=1,
    ell=r+(1-r)z.

The exact inequality on p cuts out precisely c>=s. It includes its irrational angular endpoint without replacing it by a smaller rational bound. Boxes outside that inequality may be certified empty; boxes crossing it must retain an outward enclosure of every legal point. All radicands and W_C's positive denominator are bounded explicitly in the closed domain.

The separate executable proof and emitted certificate must certify **both** roots with complete coverage and outward arithmetic; optimization output or a finite grid is not a proof. This manuscript establishes the entire original physical-to-arithmetic implication, including every support branch, original mean and limiting geometry. Its arithmetic and review status is governed by the companion certificate record.

No full original coarse parent is closed merely by writing the model. A complete direct-triangle theorem still requires the other owner families, the arithmetic replay and an explicit common-selected-certificate join.
