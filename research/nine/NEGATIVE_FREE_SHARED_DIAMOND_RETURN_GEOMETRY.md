# The entire low-radius free/shared diamond family is excluded

**Status: complete whole-domain hand argument; root and separate independent full saved-source, direct-prerequisite and exact-polynomial audits passed.**

Work in the original selected certificate for the triangle-attached diamond
HK,HA,HB,KA,KB,HX,XY,YH, retaining true H5/K3/A2/B2 and the intact HXY
petal. Put q=R² and q0=6241/1600. Assume q0≤q<17/4, A has one physical
circle corner z_A, c_H·z_A<0, HA is free, and AK is a genuine shared side.
K is physically boundary. B is positively circle-loaded and may have either
physical circle mask, with every original individual weight retained.

The results below use no force or torque equation at K or H. They retain
every original shared mean, all additional forces and all three completion
squares.

**Theorem.** The entire low-radius free-HA/shared-AK family is impossible.
The proof keeps true H5/K3/A2/B2 throughout. It excludes the complete
physical B-return fan after fixing the original H pose by actual HK contact.
Both physical B masks and every original shared mean and weight endpoint
are retained. The result joins the earlier high-radius theorem to exclude
every negative free HA contact in the triangle-attached diamond.

## 1. Actual HK contact fixes the complete H pose

The radius-independent local arguments in Sections 1–3 of
NEGATIVE_UNIQUE_TRIANGLE_FREE_ENDPOINT_HIGH_RADIUS.md apply before that
source's high-radius comparisons. NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md
supplies the whole-window bound b>3/5. Thus, in the actual A frame, with
origin at the true circle center,

    z_A=(b,a), a>b>3/5, a²+b²=q,
    Q=(b−1,a−1), A=Q+[0,1]e_x+[0,1]e_y,
    K=[b−1+t,b+t]×[a−2,a−1], 0<t<1.

The original AK mean is Q+τe_x with t≤τ≤1. A's genuine equations give
n_y/n_x≤1 for the actual H-to-A normal n, whose two components are positive.
The complete original H frame therefore is

    H=Q+[0,1]w+[0,1]v,
    w=(c,−d), v=(−d,−c), 0<c<d, c²+d²=1.

The physical HK contact initially gives c≥t. If c>t, the H vertex Q+w
lies strictly inside K: its x coordinate lies strictly between b−1+t
and b+t, and its y coordinate lies strictly between a−2 and a−1.
Therefore c=t. Put

    h=√(1−t²), x=b−1+t,
    w=(t,−h), v=(−h,−t), 0<t<h,
    V=Q+w=(x,a−1−h), L=Q+w+v=(x−h,a−1−h−t).

The entire HK contact is {V}. V lies in the relative interior of K's
left side, so its actual H-to-K normal is exactly e_x. This is a
conclusion about the original physical contact, not a new normal choice.

The physical circle equation of K, including its two-corner transition,
is

    m(a)=max(2−a,a−1),
    x+1=√(q−m(a)²), b=√(q−a²), t=√(q−m(a)²)−√(q−a²).       (1)

The actual H center and the original negative projection satisfy

    c_H=Q+((t−h)/2,−(t+h)/2),
    c_H·z_A=q−a−b−[(a+b)h+(a−b)t]/2<0.                    (2)

## 2. A complete scalar restriction, a<8/5

First a<2 follows from b>3/5 and q<17/4. The function t in (1) is
strictly increasing with a at fixed q on both m-pieces and strictly
decreasing with q at fixed a. For a≤3/2 its a derivative is
(2−a)/√(q−(2−a)²)+a/b>0. For a≥3/2 it is
a/b−(a−1)/√(q−(a−1)²)>0, by monotonicity of
u/√(q−u²). Its q derivative is negative because m(a)<a.

Suppose a≥8/5. Then m=a−1 and

    t≥(√389−13)/10>2/3,

the last comparison following from 9·389−59²=20>0. Also (1) gives
2a−1=t²+2bt<1/2+√2 b, because t<h implies t<1/√2. Consequently

    q> a²+2(a−3/4)²
      =3a²−3a+9/8≥801/200>4.                              (3)

The bracket in (2) decreases with t for t≥2/3: its derivative is
(a−b)−(a+b)t/√(1−t²)<0. Here a/b<10/3, so
(a−b)/(a+b)<7/13<2/√5. Cauchy's inequality at t=2/3 therefore gives

    c_H·z_A≥q−R√(5/2+2√5/3)>0,

since 5/2+2√5/3<4<q. This contradicts (2), proving a<8/5 on the
whole original low-radius domain.

The following uniform bounds will be used only as exact enlarged domains:

    279/200<a<8/5, b>23/20, 22/25<x<1,
    12/25<t<1/√2, 1/√2<h<22/25.                           (4)

For a's lower bound, a>R/√2≥79/(40√2)>279/200. The b bound follows
from b²>q0−64/25=429/320>(23/20)². Since m(a)<121/200,

    q0−(121/200)²−(47/25)²=1/5000>0,

proving x>22/25; m≥1/2 and q<17/4 give x<1.

For the lower t bound, monotonicity in a gives a comparison with a=b=u,
where u=R/√2 and t=√(u²+4u−4)−u. The inequality t>12/25 is equivalent
to u>661/475, which holds already at R=79/40 by squaring positive
quantities. The h bound follows from 1−(12/25)²=481/625<484/625.
In particular L_x=x−h>0 and L_y=a−1−h−t<0.

## 3. Every physical B circle corner is southeast

All three boundary units A,K,B form the actual path A–K–B. The
angular-neighbor rule excludes a physical AB contact. K's center is
(x+1/2,a−3/2). By (4), the absolute ratio of its second coordinate to
its first is less than 7/92<1/12<tan(π/36). Its center direction α_K
therefore belongs to (−π/36,π/36).

Two touching physical boundary centers have angle less than
θ=arccos(9/25): their norms exceed 5/4 and their squared distance is
at most 2, so cos θ_actual>1−1/(rs)>9/25. Also θ<7π/18, because
cos(7π/18)=sin(π/9)<π/9<22/63<9/25.

A's center has angle greater than π/4, so it is the counterclockwise
boundary neighbor of K. B is its clockwise neighbor. The strict
40-degree lower center separation from CENTERED_INNER_ARC.md and the
preceding 70-degree upper bound place B's center direction in

    (−5π/12,−7π/36).

Every physical circle corner lies strictly within π/12 of its center
direction by FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section 1.
Thus every physical B circle corner has angle in (−π/2,−π/9), and in
particular has strictly positive x coordinate and strictly negative y
coordinate. Every original positive-weight resultant has those signs,
including a two-corner B with one individual weight zero.

## 4. The complete KB fan and its strict moment sign

Let g be the actual normal from K toward B, and T its original
application, including a genuine shared mean. K owns its KH normal
−e_x. The physical triangle HKB and
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md give g_x≤0.

If g_x<0<g_y, the contact is K's upper-left vertex (x,a−1), which
belongs to A; this would be a forbidden physical AB contact. If
g=e_y, B lies in y≥a−1, whereas H has maximum height a−1 only at Q.
Physical HB would then force Q∈B, again giving AB contact. Hence the
complete remaining fan is

    g=−e_x;  g_x<0 and g_y<0;  g=−e_y.                    (5)

In the left-axis case T=(x,T_y). If T_y≥0, the whole-orientation
right-support lemma in NEGATIVE_H_OWNED_LEFT_AXIS_SMALL_COORDINATE_EXCLUSION.md,
Section 1, gives every B corner the bound

    |z|²≤max(x²,(1−x)²)+(T_y+1)²<1+a²<q,

because 0<x<1, T_y≤a−1 and b>1. This contradicts B's physical circle
contact. Thus T_y<0 in that case. The same support lemma includes
T_y=0 directly; its proof uses only T_y≥0.

In the strict southwest case T=(x,a−2). In the bottom-axis case
T_y=a−2 and T_x≥x>0. Consequently every alternative in (5) satisfies

                         det(T,g)<0.                    (6)

No equation at K was used. The actual B2 equation gives
F_B=μm+γg, with μ,γ>0 and m the actual H-to-B normal. Section 3 and
g_x≤0 imply m_x>0. The exact B torque therefore requires

                         det(P,m)>0,                    (7)

where P is the original HB application. Equation (7) is a retained
necessary condition, not an assertion that all return features satisfy it.

## 5. The complete HB feature fan and the B-owned support chart

The following geometric feature exclusions apply to every actual HB
owner, including free and shared contacts. The physical HKB triangle
excludes H-owned axes −w and v, since
both have negative x component and HK has normal e_x. Q cannot belong
to B because Q belongs to A. V cannot belong to B: K occupies a
half-plane locally at V and H's two inward edges are strictly within
the opposite half-plane; its two remaining angular gaps are each
strictly smaller than a right angle, so neither can contain a unit-square
corner sector. A strict normal at W=Q+v is opposite the strict H-vertex
cone of the actual HK normal at V; the opposite-vertex contact argument
in FAN_HUB_OWNED_ENDPOINT_EXCLUSION.md, Section 2, makes B and K disjoint.

The side QV with outward normal −v borders the actual bounded HAK
triangle hole, by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md. Its three physical boundary segments are QV in H,
Q(x,a−1) in A, and (x,a−1)V in K. A further square attached through
the relative interior of QV would lie in this bounded triangle, of
area th/2<1. The contact-triangle localization theorem excludes it.
Its endpoints Q,V have already been excluded.

Thus the whole actual HB contact fan consists only of the side VL with
normal w or the vertex L with its actual cone normal. Now suppose that m
is owned by B, including a genuinely shared HB. A B-owned singleton
occurs at L, and a shared HB may occur only on VL with normal w.
Using m_x>0 from Section 4, both
possibilities have the exact common support description

    m=(c,−s), e=Jm=(s,c), 0<c≤t, s=√(1−c²)≥h,
    min_B m·z=p:=m·L>0.                                  (8)

For the shared case c=t, m=w and every point on VL has this same
support value; L itself need not belong to B. No original mean is fixed.

Because g has nonpositive components and e has positive components,
the actual equation gives F_B·e=γg·e<0. In B's actual (m,e) frame this
forces its center's e coordinate to be nonpositive. Thus max_B e·z≤1/2.
Every KB point belongs to K and has both coordinates at least those of
T0=(x,a−2). Put

    f=e·T0=sx−c(2−a).

Then max_B e·z≥f. Whenever f>0, this gives f≤1/2, and all B corners obey

    |z|²≤(1+p)²+(1−f)².                                  (9)

This includes a physical radial B and every original individual weight:
if its center's e coordinate is zero, both e endpoints ±1/2 are retained.

## 6. Exclude the whole a≤3/2 B-owned return domain

Assume a≤3/2. Then m(a)=2−a and t<63/100. The last bound follows by
increasing a to 3/2 and decreasing q to q0 in (1), and using
√(q0−1/4)<1911/1000 and √(q0−9/4)>321/250.

### 6.1. The lower support f is uniformly above 19/50

For fixed q,a, f decreases in c, so

    f≥hx−t(2−a)=:f0(a,q).

The q derivative of f0 is positive because x_q>0 and t_q<0. At fixed
q, with M=2−a, its a derivative is

    (f0)_a=hM/(x+1)+t−(tx/h+M)t_a.

On the complete comparison interval a≤a'≤3/2 at q=q0,
t_a>1, M≥1/2, h<22/25, x>22/25, M<121/200 and x+1>47/25.
Thus the two positive terms sum to less than
(22/25)(121/376)+63/100<49/50, whereas tx/h+M>12/25+1/2=49/50.
Hence (f0)_a<0 on that entire interval. Therefore

    f≥f0(a,q)≥f0(3/2,q0)
      >(77/100)(91/100)−(63/100)/2
       =3857/10000>19/50.                               (10)

Here x>91/100 at the last endpoint and h>77/100 follow by squaring
positive quantities and t<63/100. These are full monotonic comparisons,
not pose samples.

### 6.2. The radial support p is uniformly below 7/8

Since f≤1/2, necessarily c>9/20: otherwise s>89/100 and (4) give
f>(22/25)(89/100)−(9/20)(121/200)>1/2.

The exact circle identity in the current m=2−a piece gives

    a=1+(x+1)t/2−t²/4,
    p=(c−st/2)x+(s−c)h+s(t/2+t²/4).

The coefficient c−st/2 is positive. The bound f≤1/2 gives

    x≤x*=[1/2+c(1−t/2+t²/4)]/(s+ct/2).

Substitute x* in p to obtain p*. We verify p*<7/8 on the single enlarged
rectangle 9/20≤c≤2/3, 12/25≤t≤2/3, retaining c≤t when bounding h.
Define

    A0=1−c²−c²t/2, C0=c(t/2−1),
    B0=c/2+c²+(1−2c²)t/2+t²/4−7ct/16,
    D0=−t/4+c(t²−t)/2−7/8.

Clearing the positive denominator gives

    (s+ct/2)(p*−7/8)=h(A0+sC0)+B0+sD0.

The h coefficient is (s−c)(s+ct/2)>0. The tangent bound and an elementary
squared comparison give

    h≤(2−t)/√3<26(2−t)/45=:H0,
    s≥1−23c²/40=:S0.

The first rational comparison is 3·26²>45². For the second, putting
z=c²≤4/9 gives (2·23/40−1)−(23/40)²z≥11/3600>0.
Because H0C0+D0<0, the cleared expression is at most

    P(c,t)=H0 A0+B0+S0(H0 C0+D0).

This displayed expression is an explicit cubic in c and quadratic in t.
Its second derivatives are

    P_cc=1001/1440−137t/80+26t²/45
          +c(299/75−1357t/600−437t²/600),
    P_tt=1/2+19c/45+26c²/45−437c³/1800.

On the entire rectangle, P_cc≥18839/36000>0 and P_tt>0. Hence its
maximum occurs at a corner of that rectangle. The four values, in the
order (c,t)=(9/20,12/25),(9/20,2/3),(2/3,12/25),(2/3,2/3), are

    −54804587/18000000000,  −59791/86400000,
    −1071859/60750000,     −35131/874800.

They are all strictly negative. Every expression is verified by direct
expansion and rational arithmetic; no sampled orientation or parameter
subdivision is a premise. Therefore p≤p*<7/8.

### 6.3. The physical circle contradiction

Equations (9)–(10) and p<7/8 give every B corner

    |z|²<(15/8)²+(31/50)²=q0−3/5000<q.

This contradicts the physical circle contact of B and closes the whole
a≤3/2 B-owned HB domain, including a=3/2, every shared HB mean, both
physical B masks and every individual zero corner-weight endpoint.

## 7. Exclude the whole a≥3/2 B-owned return domain

Now 3/2≤a<8/5 and m(a)=a−1. We keep the same actual quantities p,f
and all the physical consequences of Sections 1–5.

### 7.1. A uniform support bound f>31/100

Again f≥f0(a,q)=hx−t(2−a). At fixed a, (f0)_q>0, so decrease q to q0
as a scalar comparison. This comparison does not require t<h at its
endpoint; the radicals stay positive throughout. On the entire rectangle
q=q0, 3/2≤a≤8/5, one has

    7/12<t<29/40, 17/25<h<5/6, 22/25<x<1.

The lower t bound follows already from t≥2−√2>7/12 on the original
q≤17/4 domain. For its upper comparison endpoint, at a=8/5,
√(q0−(a−1)²)<941/500 and √(q0−a²)>1157/1000, giving t<29/40.
The h bounds follow by squaring.

Here x_a=−(a−1)/(x+1), t_a=a/b−(a−1)/(x+1)>32/47, and

    (f0)_a=h x_a+t−(tx/h+2−a)t_a
       <−17/100+29/40−(127/125)(32/47)
        =−6427/47000<0.

For clarity, the three bounds used are h x_a<−17/100,
tx/h+2−a>127/125, and the displayed t_a estimate. All hold throughout
the complete comparison interval. At a=8/5,q=q0, the stronger
h>687/1000 follows from t<29/40. Therefore

    f≥f0(a,q)≥f0(8/5,q0)
       >(687/1000)(22/25)−(29/40)(2/5)
        =983/3125>31/100.                                (11)

### 7.2. A uniform support bound p<17/20

The necessary f≤1/2 forces c>1/2: if c≤1/2, then s>43/50 and
f>(22/25)(43/50)−1/4>1/2, because 2−a≤1/2.

The exact current circle identity is

    a=1/2+(x+1)t−t²/2.

Define only for scalar comparison

    M*=1−(x+1)t/2+t²/4,
    p*=c(x−h)+s(M*+h+t−1), f*=sx−cM*.

Since M*−(2−a)=a/2−3/4≥0, one has p≤p* and f*≤f≤1/2.
The expression p* has precisely the low-piece algebra used in Section 6.2.
Its positive x coefficient c−st/2 allows the same substitution

    x≤[1/2+c(1−t/2+t²/4)]/(s+ct/2).

Call the resulting upper bound p**. We verify p**<17/20 on the whole
actual triangular domain

    1/2<c≤t<1/√2, 7/12<t.

With k=17/20, put

    A0=1−c²−c²t/2, C0=c(t/2−1),
    B0=c/2+c²+(1−2c²)t/2+t²/4−kct/2,
    D0=−t/4+c(t²−t)/2−k.

Then (s+ct/2)(p**−k)=h(A0+sC0)+B0+sD0. Its h coefficient is
(s−c)(s+ct/2)>0. Use the tangent at t=3/5 and a concave-square-root
chord bound:

    h≤(5−3t)/4=:H1,
    s≥5/4−77c/100=:S1       (1/2≤c≤71/100).

The second bound holds by concavity: at c=1/2 the lower line is
173/200<√3/2; at c=71/100 its value is 7033/10000, whose squared
gap below 1−c² is 126911/100000000. The line is therefore below the
square root throughout that complete interval. The actual c,t are
both smaller than 71/100.

Again H1C0+D0<0, so the cleared expression is bounded above by

    J(c,t)=H1 A0+B0+S1(H1 C0+D0).

Direct expansion gives

    J=3/16−9t/16+t²/4
       +c(−51/125+689t/800+5t²/32)
       +c²(57/80−1239t/800+223t²/800).

Since J_tt=1/2+5c/16+223c²/400>0, its maximum at each fixed c in
the enlarged triangle 1/2≤c≤t≤71/100, t≥7/12 is on one of three
boundary segments. Their complete signs are as follows.

* On t=7/12, 1/2≤c≤7/12, the c derivative is positive; its minimum
  there is J_c(7/12,7/12)=122567/3456000>0. Thus the maximum is
  J(7/12,7/12)=−180157/82944000<0.
* On t=c, write

      D(c)=223c⁴/800−557c³/400+1459c²/800−1941c/2000+3/16.

  Here D'' decreases throughout [7/12,71/100], and starts at
  −169/1920<0. Also D'(7/12)=−74269/1728000<0. Hence D decreases
  and its maximum is the same strictly negative initial value.
* On t=71/100, J is the concave quadratic

      −1717/20000+(90321/320000)c−(1972757/8000000)c².

  Completing its square bounds it, even on the entire real line, by
  −12835245191/2525128960000<0.

This exhausts the enlarged triangular domain. All comparisons concern
the original scalar quantities; neither the actual square nor any
application mean was moved. Therefore p≤p*≤p**<17/20.

### 7.3. The physical circle contradiction

Using (9), (11) and p<17/20, every B corner obeys

    |z|²<(37/20)²+(69/100)²=q0−81/40000<q.

This contradicts B's physical circle contact. Together with Section 6,
it excludes every B-owned HB normal in the complete low-radius
free-HA/shared-AK domain, including every genuine shared HB interval.

## 8. The remaining HB feature cannot meet a physical radial B

Sections 6–7 exclude every B-owned HB normal, including shared HB.
All remaining HB contacts in the complete fan of Section 5 are singletons
at B vertices, located on VL or at L. We show that the entire segment VL
has smaller norm than every noncircle vertex of any physical radial B.

Put S0=√(q−1/4). The two noncircle vertices of a contained unit with two
physical circle corners have squared norm

    ρ²=(S0−1)²+1/4=q+1−2S0.                              (12)

First |L|<|V|. Write

    D=h(b−1)+t(a−1).

The exact identity L=V+v gives |L|²−|V|²=1−2D. In the a≤3/2 piece,
the circle identity in Section 6.2 gives

    D=x(h+t²/2)−ht+t²/2−t³/4.

In the a≥3/2 piece, its actual a is at least the comparison coordinate
1+(x+1)t/2−t²/4, so the same expression is a lower bound for D.
Since x>22/25, t<1/√2 and h≥1−3t²/5,

    D>22/25−t+103t²/250+7t³/20.

The square-root bound follows by squaring positive quantities for
0≤t²≤1/2. The coefficient 22/25−t is positive, so its substitution
has the stated direction. Subtracting 1/2, the remaining polynomial has
the exact completed-square form

    19/50−t+103t²/250+7t³/20
      =1/6750+(2/125)(t−2/3)
       +[103/250+(7/20)(t+4/3)](t−2/3)².

Because t>12/25, the bracket exceeds 157/150. Completing the square
therefore bounds the entire expression below by

    1/6750−(2/125)²/[4(157/150)]=461/5298750>0.

Thus D>1/2 and |L|²<|V|² throughout the whole chart.

We next prove |V|²<ρ². When a≤3/2, put M=2−a and S=x+1=√(q−M²).
Direct expansion gives

    ρ²−|V|²
      =(1−h)(2M−1+h)−2(M²−1/4)/(S+S0)>0.                (13)

Indeed 1−h>3/25, h>77/100, M≥1/2, M<61/100 and
S+S0>47/25+191/100=379/100. The first term exceeds 9/100 and the
subtracted term is less than 7/100. The bounds h>77/100 and t<63/100
hold on this complete low-coordinate piece by Section 6.

When a≥3/2, put N=a−1 and S=x+1=√(q−N²). Expansion instead gives

    ρ²−|V|²=h(2N−h)−2(N²−1/4)/(S+S0)>0.                 (14)

Here 1/2≤N<3/5, h>7/10 and h<5/6. The first term exceeds 7/60,
whereas the subtracted term is less than 3/50, using S+S0>379/100.
Both inequalities include the a=3/2 transition.

The squared norm is convex along the segment VL, so every point of VL
has squared norm at most |V|²<ρ². None can be a physical radial B vertex:
the inner vertices have norm ρ, and the outer vertices lie on the circle.
Therefore the complete physical radial-B alternative is excluded.

## 9. Unique B has an H-owned singleton HB

We are left with one physical circle corner on B and no B-owned HB
normal. If HB were free, Section 5 places its actual point at L.
If KB is a singleton, the existing compatible fixed-tip selection in
GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes this free HB normal.
Its coincident radial-D exception is impossible with the actual boundary
neighbor K; alternatively a coincidence would put L in HK={V}, which
is false. No normal is changed after multiplier extraction.

If KB is genuinely shared, its normal is one of the two axes −e_x,−e_y
in (5), and B has K's displayed frame. For a shared left side, its x
coordinates at vertices are x−1 and x, whereas L_x=x−h is strictly
between them. For a shared bottom side, its vertex y coordinates are
a−3 and a−2, whereas L_y=a−1−h−t lies strictly between them because
1<h+t<2. In either case L cannot be a B vertex, contradicting the
free HB premise.

Thus HB is an H-owned-only singleton with actual normal w and actual
application

    P=V+σv=(x−σh,a−1−h−σt), 0<σ≤1.                    (15)

The strict convention gives the actual side-interior case; allowing the
endpoint σ=1 only enlarges the estimates. P is an actual B vertex.
V cannot be the contact by the complete tangent-sector argument in
Section 5. The true B2 torque retains the necessary strict condition
det(P,w)>0 from (6)–(7).

### 9.1. No genuinely shared KB remains

If KB shares K's left side, B=[x−1,x]×[y,y+1]. A vertex P would have
x−σh equal to x or x−1. The first gives P=V, already impossible; the
second requires σh=1, impossible with σ≤1 and h<1.

If KB shares K's bottom side, B=[y,y+1]×[a−3,a−2]. Equation (15) puts
P at its top height only when

    h+σt=1, σ=(1−h)/t=t/(1+h).

Its bottom height would require h+σt=2, impossible. Since P_x<x and
B touches K, P must be B's upper-left vertex, not its upper-right one.
Consequently B has the actual corner

    Z=(P_x+1,a−3)=(b+σ,a−3).

Its excess squared norm is

    |Z|²−q=2bσ+σ²+9−6a>0.

For a≤3/2 the sign is immediate. For a≥3/2, b>23/20,
t>7/12 and h<5/6 give σ>7/22, so 2bσ>161/220, while
9−6a>−3/5. The excess is still strictly positive. This contradicts
containment and excludes every shared KB mean.

Thus KB is a singleton. Its normal cannot be free: B is unique and
its two physical applications are fixed singletons, so the same existing
fixed-tip selection applies. The whole remaining KB fan has either a
K-owned axis or a B-owned strict southwest normal. A remaining singleton
K-axis is not also B-owned: with parallel frames, a relative side-interior
application would give a positive shared segment, while a point-only
vertex/vertex application cannot carry a side-axis endpoint under the
existing strict convention.

## 10. Every remaining singleton KB owner is impossible

### 10.1. K owns the left axis

Let g=−e_x. Both P and T are B vertices, since neither contact normal
is owned by B. They are distinct: equality would put their common point
in HK={V}, which a third square cannot contain. They cannot be opposite
vertices either. At opposite vertices their strict B normal cones would
make the other two units H,K disjoint by the same opposite-vertex
contact lemma used in Section 5. Thus P,T are adjacent B vertices.

Write Δ=T−P. Since T lies on K's left side,

    Δ_x=σh, Δ_y≥h+σt−1, |Δ|=1.

If Δ_y≤0, then |Δ_y|≤1−h and Δ_x≤h, giving
|Δ|²≤h²+(1−h)²<1, impossible. Hence Δ_y>0. Since P is a strict
minimum-w support vertex of B, w·Δ>0. Therefore

    σt>Δ_y=√(1−σ²h²),

which implies σ²(t²+h²)>1, or σ>1. This contradicts (15).

### 10.2. K owns the bottom axis

Let g=−e_y. Again P,T are distinct adjacent B vertices. Write
e=T−P=(r,s), with r>0 and s≥0: T_x≥x>P_x and T_y is B's maximum
height a−2. The strict minimum-w condition gives

    A0:=tr−hs>0, r²+s²=1, hence r>s.

The other inward B edge at P must be f=(s,−r), because the opposite
choice has negative w projection. Thus B=P+[0,1]e+[0,1]f.
The actual force F_B=μw+γ(−e_y) has strictly positive f component.
Since B is physically unique, its actual circle corner is one of

    Z1=P+f,  Z2=P+e+f.

If it is Z1, the two genuine pair moments about Z1 have signs

    det(P−Z1,w)=−A0<0,
    det(T−Z1,−e_y)=−(r−s)<0.

If it is Z2, write B0=hr+ts. Then

    det(P−Z2,w)=B0−A0=(h−t)r+(h+t)s>0,
    det(T−Z2,−e_y)=s≥0.

In each case the positive pair magnitudes make torque balance
impossible, while the unique circle force has zero moment about its
actual corner. This exhausts the physical corner alternatives.

### 10.3. B owns a strict southwest KB normal

Write g=(−s1,−c1), e=(c1,−s1), with c1,s1>0 and c1²+s1²=1.
Here T is K's actual lower-left vertex T0=(x,a−2).
The side-normal triangle theorem at B gives w·g≥0. Equality would
make w a B axis, already excluded. Hence

    α=w·e=tc1+hs1>0, β=w·g=hc1−ts1>0.

Because P is B's strict minimum-w support vertex, the whole B is
P+[0,1]e+[0,1]g, and T=P+λe for some λ∈[0,1]. The actual H side
support value gives

    λα=w·T−w·P=h(1−h).

Consequently

    det(P,w)=−f0(a,q)+h(1−h)β/α.

The original support lower bounds in Sections 6.1 and 7.1 give
f0(a,q)>31/100 throughout the whole domain. Moreover

    β/α<h/t,
    h(1−h)(h/t)=h²t/(1+h)<ht/2≤1/4.

The first inequality follows immediately by cross multiplication with
positive denominators, and the second uses 0<h<1 and 2ht≤1.
It follows that

    det(P,w)<−31/100+1/4=−3/50<0.

This contradicts the original positive-moment requirement (7).
The proof retains the unchanged actual λ and every endpoint; it has
not replaced an application by the supporting-line intersection.

## 11. Whole owner assembly and retained scope

The exact physical HK geometry gives the whole original chart without
an equation at K or H. Sections 3–5 provide the complete original B
contact and physical-corner fan. Sections 6–7 exclude every B-owned HB
normal and every shared HB mean. Section 8 removes the full physical
radial-B mask; Section 9 removes the unique-B free HB and shared KB
alternatives using the existing compatible preselection only where its
fixed-point premises apply. Section 10 exhausts every remaining KB
owner. Therefore the entire q0≤q<17/4 free-HA/shared-AK family is
excluded, for both physical B masks.

The singleton AK alternative was already excluded by the same fixed-tip
selection with its coincident exception geometrically impossible. The
complete higher-radius free-HA theorem includes q=17/4. The joined
conclusion is therefore: a negative unique endpoint A in the actual
triangle-attached diamond cannot have a free HA contact anywhere in the
declared radius window. This includes both unique-K masks UUS/UUU and
all original mean and individual weight endpoints. The proof also
retains the K two-corner transition a=3/2 wherever it occurs.

No degree-two equation is assigned to K, no K or H force is split or
discarded, and the intact HXY petal and all three extras remain. The
remaining H-owned-HA singleton features at the negative endpoint, the
full unique-K diamond parent, C2.34.b0, the unrestricted lower bound,
and every original equality classification are not closed by this source.
No Lean compilation or CI was run.
