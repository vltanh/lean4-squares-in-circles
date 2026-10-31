# An owned tilted S leaf excludes its inward upper boundary contact

Date: October 27, 2026.

**Status: complete original-domain hand exclusion, submitted for full
root and separate independent review.** This closes the entire strict
inward-upper BC feature when A has its outer-lower leaf and B its
owned far-axis leaf. C has one physical circle corner; D may have
either physical mask. The actual North BC mean remains separate.

Keep all nine actual squares and the original component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+E, 0<E<1/60,
    R^2=(2+E)^2+1/4<=Q_*=1105/256.

The actual AB normal is East, owned by A alone. The original positive
cycle moment and complete one-owner leaf cover give

    A=[-X,h] times [-v,1-v],       X=1-h,
    X^2+v^2=d^2,       |h|<=E,
    P_AB=(h,-k),       0<k<v<13/50.

The real A leaf is at (-X,-v). Write the actual B axes

    j=(s,-c),       f=(c,s),       c,s>0, c^2+s^2=1.

In this positively oriented (j,f) frame its actual owned-S chart is

    B=[E,d] times [-w,T],       T=1-w,
    d*e_M=(d,0),       P_AB=(E,-w),
    h=E*s-w*c,       k=E*c+w*s.

Every actual force, weighted application and physical circle weight
is retained. In particular no North mean is assigned an endpoint.

## 1. The actual inward contact and the two genuine leaf identities

Suppose the actual BC normal is strict Northwest in this B frame,
at Q=(E,T). The full B3 equations give

    m=(-a,b),       a,b>0, a^2+b^2=1,
    nu*T*a=mu*w*s,       nu*b=mu*c.

Consequently w>0 and, on writing r=a/b,

    r=w*s/(c*T)>0,
    p:=c/s=w/(r*T),
    w=r*p/(1+r*p).                                    (1)

These are identities for the original normal and magnitudes.
The original one-owner singleton preselection in
ADJACENT_S_C4_ONE_OWNER_OUTER_CONTACT_SIDE_OWNERS.md makes C the
actual side-axis owner of this strict B-vertex contact. It applies
with the fixed actual AB point supplied by B's vertex and leaves
every original C side mean free. No all-cycle shared-mean selection
is being substituted.

The two actual root identities and k<v give the stronger physical
inequality

    0<v^2-k^2=2E(1+s)-w^2-2wc.                       (2)

Indeed h^2+k^2=E^2+w^2 and v^2=d^2-(1-h)^2. Hence

    0<w<13/50,       T>37/50.                         (3)

For this conclusion w^2<4E<1/15<(13/50)^2 suffices. The proof
will use (2), not an independently chosen root pose.

## 2. The complete actual C side and its true C2 radial point

Put t=(b,a). For the original mean parameter z in [0,1],

    C=Q+[0,1]m+[-z,1-z]t.

Define the actual scalar projections

    L=|Q|=sqrt(E^2+T^2),
    u=Q.m=(T-rE)/sqrt(1+r^2),
    V=Q.t=(E+rT)/sqrt(1+r^2)>0.                       (4)

Whenever r<=2, (3) gives u>0. The genuine loaded C2 theorem,
with its actual physical boundary neighbor D, gives the proper
radial point

    q=Q+rho*m=lambda*Z_C,       rho>=0, lambda>0.

C has its one physical circle corner, so the unique-corner clause
applies. In particular this does not turn a two-corner mask with
a zero individual weight into a unique physical corner.

Since u>0, that corner is on the far-m side. Since V>0, its
transverse component is positive and maximal: otherwise the
other corner of that same far-m side would be farther from O.
Thus, with W=sqrt(R^2-(u+1)^2)>0, the actual corner and center are

    Z_C=(u+1)m+W*t,
    z_C=(u+1/2)m+(W-1/2)t.                            (5)

The full proper-distance inequality also gives the radial cap

    R<=L+L/u.                                        (6)

For completeness, lambda>=u/(u+1), while
V/lambda is the actual corner's transverse coordinate. Comparing
the two components gives R<=L*(u+1)/u. These are necessary
consequences of the actual mean and force equations, not a change
to z or rho.

In world coordinates, if p<r, write

    m=(-sin(delta),cos(delta)),
    t=(cos(delta),sin(delta)),
    tan(delta)=(r-p)/(1+rp)=r*(1-w)-w/r.              (7)

For 0<delta<arctan(2), set A0=u+1/2>0. If

    W-1/2<q0*A0,
    tan(delta)>(6q0-1)/(6+q0),                       (8)

then the actual expression (5) gives

    (z_C)_y-6(z_C)_x>0.                              (9)

Here sin(delta)-6cos(delta)<0, so the substitution in (8) has
the displayed strict direction even if W-1/2 is negative. A
convenient exact sufficient condition for the first inequality is

    u>u0>0,
    (u0+1)^2+[1/2+q0*(u0+1/2)]^2>Q_*.              (10)

We will also check that the actual center has positive height.
Then (9) means theta_C>arctan(6).

## 3. The whole range 0<r<=5/8

Let S=sqrt(1+r^2). Initially T>37/50 and E/T<5/222. Hence

    L<T+1/5000,
    (L/u)^2
      <(89/64)*(1+(5/222)^2)/(1-(5/8)*(5/222))^2
       <36/25.                                      (11)

The last exact reserve is 663511/76650025. The radius is greater
than 103/50. Thus (6) first gives

    T>103/50-6/5-1/5000
      =4299/5000>6/7.                               (12)

This elementary improvement allows the E error to be kept smaller
than the actual radius increase. With zeta=E/T, use
sqrt(1+zeta^2)<=1+zeta^2/2 and S<59/50. Then

    L+L/u
      <T+S+E*[7/720
          +(59/50)*(35/48+49/4320)*(576/569)]
      <T+S+(9/10)E.                                 (13)

The bracket is 9159143/10242000, whose gap below 9/10 is
58657/10242000. Every denominator is positive by (12).
On the other hand

    R>103/50+(9/10)E,

as follows on squaring: the difference is
4/625+(73/250)E+(19/100)E^2>0. Equations (6) and (13) imply

    T+S>103/50,
    w<1+S-103/50<3/25.                              (14)

If r<=7/20, then S<53/50 and T<=1 contradict (14).
Thus the entire remaining range here is 7/20<r<=5/8.

We claim that (14) also implies tan(delta)>7/20. Substitute its
upper bound for w into (7). The desired strict inequality follows
from

    (106+206r^2-35r)^2-10000(1+r^2)^3>0.             (15)

The unsquared right-hand expression 106+206r^2-35r is positive
throughout this interval. To verify (15) without a numerical test,
put x=r-2/5, so |x|<=9/40. The polynomial on its left equals

    3776/625+(18152/125)x
      +x^2*[142289/25-(36612/5)x-11564x^2
                         -24000x^3-10000x^4].

The bracket exceeds 3000: replacing each signed term by its
lower bound at |x|<=9/40 leaves the exact reserve
1021367/6400. Completing the square in the remaining quadratic
gives a positive minimum 25103278/5859375. This proves (15)
and the claimed strict angular bound, in particular p<r.

Now (4), (14) and S<59/50 give

    u>(22/25-1/96)/(59/50)>73/100.

Use (10) with u0=73/100 and q0=8/15; its exact reserve is
51319/4000000. The second condition in (8) holds because

    7/20>33/98=(6q0-1)/(6+q0),

with reserve 13/980. Also p=w/(rT)<2/5, so s>9/10 and c<2/5.
The actual point Q has world height T*s-E*c, hence

    Q_y>(22/25)*(9/10)-(1/60)*(2/5)>17/24>1/sqrt(2).

Every point of a unit square is at distance at most 1/sqrt(2)
from its center, so the actual point Q gives a positive center
height. Equations (8)--(10) prove
theta_C>arctan(6) throughout the entire first range.

## 4. Exact bounds from the two real leaves

The middle range will use only a short list of rational
inequalities, all following directly from (2). They are recorded
explicitly to retain every endpoint and to make the arithmetic
independently checkable.

For r,p>0 put w=rp/(1+rp), S_p=sqrt(1+p^2). Inequality (2) is

    E>[w^2*S_p+2wp]/[2(S_p+1)].                     (16)

Its right side is strictly increasing separately in r and p.
Indeed w increases in both, S_p/(S_p+1) increases in p, and
p/(S_p+1) also increases in p.

At a proposed comparison point for which 30w^2<1, define the
entirely rational expression

    J(r,p)=(30w^2-1)*(1+p^2/2)+60wp-1.              (17)

If J(r,p)>0, then sqrt(1+p^2)<=1+p^2/2 and the negative
coefficient show that the right side of (16) exceeds 1/60.
This comparison point and all larger ones are impossible.

For a row [r0,r1], a positive J(r0,pbar) therefore proves
p<pbar. A positive

    J(r1,wbar/[r1*(1-wbar)])

proves w<wbar throughout the row: at fixed w the right side of
(16) decreases with r, and it increases with w. This is a scalar
comparison, not a substitution of new physical data.

## 5. The whole range 5/8<=r<=2

Apply the comparison just proved in the following seven rational
rows. No point of the parameter intervals is sampled or omitted.

| r0 | r1 | pbar | wbar | u0 | q0 |
| --- | --- | --- | --- | --- | --- |
| 5/8 | 13/20 | 2/9 | 49/400 | 363/500 | 27/50 |
| 13/20 | 7/10 | 3/14 | 63/500 | 353/500 | 23/40 |
| 7/10 | 39/50 | 5/24 | 131/1000 | 337/500 | 5/8 |
| 39/50 | 9/10 | 1/5 | 11/80 | 629/1000 | 141/200 |
| 9/10 | 11/10 | 9/50 | 147/1000 | 14/25 | 83/100 |
| 11/10 | 3/2 | 4/25 | 81/500 | 9/20 | 21/20 |
| 3/2 | 2 | 2/15 | 7/40 | 7/20 | 127/100 |

Here are the complete rational tests used in every row:

    J(r0,pbar)>1/200,
    J(r1,wbar/[r1*(1-wbar)])>1/100,
    (1-wbar-r1/60)^2-u0^2*(1+r1^2)>9/10000,
    (u0+1)^2+[1/2+q0*(u0+1/2)]^2-Q_*>9/10000,
    (r0-pbar)/(1+r0*pbar)
          -(6q0-1)/(6+q0)>9/1000.                    (18)

These are direct substitutions of the displayed rational numbers.
For additional exact checks, the respective smallest reserves
before the coarser lower bounds in (18) are

    303797/39890312,
    5354736307/333135504000,
    53389/56250000,
    457/500000,
    824/83897.

All comparison depths in (17) satisfy 30w^2<1, including the
depth determined by each (r0,pbar). Thus Section 4 supplies the
first two bounds p<pbar,w<wbar. Formula (4) and the third test
then give u>u0. The fourth test is exactly (10). Finally (7)
is increasing in r and decreasing in p, so the last test proves
the second condition in (8), with 0<delta<arctan(2).

Every row has p<2/9 and w<7/40. Thus s>97/100 and c<2/9,
and the actual vertex height satisfies

    Q_y>(33/40)*(97/100)-(1/60)*(2/9)>17/24.

The final strict reserve is 9527/108000. Its actual center has
positive height. The center test therefore proves
theta_C>arctan(6) on all seven rows, including their common
endpoints.

## 6. The entire remaining range r>=2

This range needs only the actual owned side, physical boundary
status and (1),(3); it does not use concurrence or a circle mask.
They imply

    p=w/(rT)<13/74,
    s>49/50,
    c<p<13/74.

In world coordinates the actual center has, for its unchanged
z in [0,1],

    (z_C)_x
      <=Q_x+[(c-s)r+(c+s)]/[2sqrt(1+r^2)].

The bracket is negative: it is
s*((p-1)r+p+1), at most s*(3p-1)<0 for r>=2.
Moreover T*c=w*s/r, so

    (z_C)_x<Q_x=E*s+T*c<E+w/r<11/75.                 (19)

The actual point Q again lies high enough to give a positive
center height, since

    Q_y>(37/50)*(49/50)-(1/60)*(13/74)>17/24,

with exact reserve 967/69375. A physical boundary center has
norm greater than 27/20. If its x coordinate is nonpositive,
its angle already exceeds pi/2. Otherwise (19) gives

    cos(theta_C)<44/405<1/sqrt(37).

The last comparison is the integer inequality
37*44^2<405^2. Thus theta_C>arctan(6) here as well.

## 7. The complete original contact exit

Sections 3,5,6 exhaust every actual r>0. They prove the local
conclusion theta_C>arctan(6)>4*pi/9. For the last comparison,
tan(pi/18)>pi/18>1/6 follows from pi>3.

The full original-domain theorem
OUTER_LOWER_S_OWNER_BOUNDARY_NEIGHBOR_CENTER_ANGLE.md gives
0<theta_D<2*pi/3 for the actual A-root boundary neighbor D.
It treats both physical D masks, every actual AD feature and
every North mean, while retaining the true D2/C2 hypotheses
only where their actual proper radial points are used.

The original circle-spoke order L,M,C,D puts these touching
boundary units in counterclockwise minor-center order. Since
both centers have positive height, it requires theta_C<theta_D.
The resulting angle gap is strictly less than 2*pi/9, whereas
the physical boundary-center separation is strictly greater
than 2*pi/9. This is a contradiction.

Thus the entire inward-upper BC contact is impossible in the
stated original domain, for either D mask. Together with
OWNED_S_LEAF_ROOT_OUTWARD_UPPER_CONTACT_EXCLUSION.md it leaves
only the actual B-owned North BC mean in this owned-B leaf
type. That remaining mean is not claimed excluded here.

The proof keeps the full A3/B3 equations, true C2/D2 equations,
actual normal ownership and side means, both genuine leaves,
all physical masks and all nine units. Its rational rows are
explicit hand inequalities on complete intervals; no numerical
pose, certificate, compilation, CI or remote action is a premise.

