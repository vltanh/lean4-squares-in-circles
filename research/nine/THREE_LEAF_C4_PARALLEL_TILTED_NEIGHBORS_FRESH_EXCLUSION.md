# Three genuine S leaves on C4: all parallel-middle tilted-neighbor cases

Date: October 27, 2026.

**Status: complete fresh hand proof of the entire remaining parallel-middle
interface, saved for full independent and root review.** Both one-tilted
and two-tilted outer-root cases are included, with every original side
mean and the full A3/B3/C3/D2 equations. No lost proof is used.

## 1. Exact original graph and common domain

Retain all nine actual contained unit squares, the original compatible
selected certificate, and the actual positive component

    A--B--C--D--A, A--L_A, B--L_B, C--L_C,
    A3, B3, C3, D2, L_A1, L_B1, L_C1.

All three leaves are genuine S leaves. Work in the strict-high range

\[
 R^2=(d+1)^2+1/4\le1105/256,
 \qquad d=1+\varepsilon,
 \qquad 0<\varepsilon<1/60.
\tag{1}
\]

The complete middle-root theorem
`GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md`
(`5dba416ea7bfd8500daf6f33bcecd56521dd7013f2357b9442964d2c49edb480`)
has separate full independent acceptance
`REVIEW_GENUINE_S_THREE_FORCE_TWO_NEAR_FRESH_DOMAIN_HEXAGON_2026_10_27.md`
(`2595b9050f97e3af62ef950f1c214a9f2f94fc0de8f0c4c26356f61d1587d1e5`).
Here take its whole parallel alternative, with B's real leaf East.
The actual B-to-A and B-to-C normals are both West. After exchanging the
outer labels if necessary their original means are

\[
 P_A=(\varepsilon,t),\qquad P_C=(\varepsilon,-k),
 \qquad t,k>0,\quad t+k\le1.
\tag{2}
\]

The means in (2) need not be B vertices. Their strict signs come from the
full genuine-root zero-mean exclusion, not from moving a mean. We assume
at least one outer root does not own its contact axis with B.

Each root contains its actual epsilon-disk point and is physically clear.
D has nonzero circle load and is physically boundary. Indeed if its
actual circle resultant vanished, its true two-force balance would give
opposite normals. A and C would be beyond opposite D supporting lines,
whose distance is at least one; their two actual near points would give
that distance at most 2epsilon<1. This is impossible. Write r=R-sqrt(2),
so every actual D point has norm at least r. For a convenient exact bound,

\[
 r>16/25,
\tag{3}
\]

because R>sqrt(17)/2>103/50 and sqrt(2)<71/50. The two squared reserves
are 4/625 and 41/2500, respectively. No force equation at an outer root
has been reduced to degree two.

## 2. Complete genuine-leaf cover at one tilted outer root

Assume A does not own its contact axis. Its actual maximum-x point is
the strict vertex P=P_A. Choose its two inward own axes as

\[
 f=(-c,-s),\quad j=(-s,c),\qquad
 c,s>0,\quad c^2+s^2=1,
\]
\[
 A=P+[0,1]f+[0,1]j.
\tag{4}
\]

Both possible tilts are represented, without an order between c and s.
The actual A-to-B force is mu East, mu>0, at P. Its own components are
mu(-c,-s). All own-coordinate moments below are multiplied by the same
orientation sign when interpreted in the original plane; their zero
sum is therefore the full actual physical torque equation.

### 2.1. The two candidate genuine-leaf forms

The owned -f support has height epsilon*c+t*s<=sqrt(epsilon²+t²)<d;
owned +f has height 1-epsilon*c-t*s<1<d; and owned -j has height
epsilon*s-t*c<epsilon<d. The point P itself also has norm less than d.

At the lower adjacent vertex P+f, norm d would give

\[
 t^2-2ts=2\varepsilon(1+c),
\]

so t>2s and therefore s<1/2. Its required lower-j radial support sign
would give t*c<=epsilon*s, impossible since c>sqrt(3)/2>epsilon.
The axis endpoint is already covered by the owned +f exclusion.

Apart from the far opposite vertex treated in Section 2.2, the entire
actual support cover thus leaves exactly:

* **Type V:** the strict upper adjacent vertex P+j. Its unchanged radial
  point and exact identity are
  \[
  (\varepsilon-s,t+c),\qquad
  t^2+2ct=2\varepsilon(1+s).
  \tag{5}
  \]
* **Type J:** the owned far-j side, with its original radial application
  d*j. Its exact identity is
  \[
  tc=\varepsilon(1+s),\qquad
  t=\varepsilon(1+s)/c.
  \tag{6}
  \]
  In this case P has own coordinates (-t,epsilon), and the leaf's
  original offset from P is (t,1). The whole side interval, including
  any formal endpoint t=1, is retained until excluded below.

In either type

\[
 0<t\le\frac{\varepsilon(1+s)}c.
\tag{7}
\]

For V the inequality is strict and t<2sqrt(epsilon)<13/50. This section
has used only the actual leaf geometry, not a circle direction of D.

### 2.2. Full A3 torque excludes the opposite genuine-leaf vertex

Suppose instead that the genuine leaf is at P+f+j. Its actual own
coordinates and radial signs are

\[
 E_f=1-\varepsilon c-ts>0,
 \qquad E_j=1-\varepsilon s+tc>59/60.
\]

The leaf norm gives E_f²+E_j²=d², so E_f<1/sqrt(15)<E_j. Expanding
the same identity in the original coordinates gives

\[
 t^2+2t(c-s)=-1+2\varepsilon(1+c+s)<0.
\]

Hence s>c. Let alpha>0 be the actual leaf magnitude, put
ell=mu*d/alpha>0, and scale the entire remaining AD force by d/alpha.
Its own components are

\[
 X=\ell c-E_f,\qquad Y=\ell s-E_j.
\tag{8}
\]

The real leaf moment about P, with this same scaling, is
Delta=E_j-E_f>0. The AB force acts at P. The following is the complete
actual AD support and original mean cover; rho always denotes its
unchanged side parameter in [0,1].

| Actual AD feature | Full moment or consequence | Contradiction |
| --- | --- | --- |
| X<0,Y<0 at P | Delta | Strictly positive |
| X>0,Y>0 at P+f+j | Delta+Y-X=ell(s-c) | Strictly positive |
| X>0,Y<0 at P+f | Delta+Y=0 gives ell*s=E_f | X=E_f(c/s-1)<0 |
| X<0,Y>0 at P+j | Delta-X=0 | X=Delta>0 |
| X>0,Y=0 at P+f+rho*j | rho*X=Delta, ell*s=E_j | X=(c/s)E_j-E_f<Delta |
| X=0,Y>0 at P+rho*f+j | Delta+rho*Y | Strictly positive |
| X<0,Y=0 at P+rho*j | Delta-rho*X | Strictly positive |
| X=0,Y<0 at P+rho*f | rho*(-Y)=Delta, ell*c=E_f | -Y=E_j-(s/c)E_f<Delta |

The force cannot be zero because AD has positive magnitude. Every row
is impossible, including rho=0 or 1. Thus the opposite genuine-leaf
vertex is excluded by the full A3 equations. No fourth force can be
added to this lemma without repeating its proof; it is not a hub-degree
export.

## 3. A uniform actual-height bound at every tilted outer root

Type V already gives t<13/50<3/8. For type J suppose t>=3/8.
Equation (6) gives

\[
 c<4/45,\qquad s>44/45,\qquad ts>c.
\tag{9}
\]

Here c<4/45 follows from epsilon<1/60 and 1+s<2. The last strict
comparison has the reserve (3/8)(44/45)-4/45=5/18.

Keep the entire A3 force equation. Its AD own components are

\[
 X=\mu c>0,\qquad Y=\mu s-\alpha.
\]

The actual real leaf moment about P is t*alpha. If Y>0, AD is at the
far opposite vertex; full torque gives

    mu(s-c)=alpha(1-t).

Combining this with mu*s>alpha forces c>ts, contrary to (9). This
also excludes t=1 directly. If Y=0, its full +f-side mean P+f+rho*j
has rho=ts/c>1, again impossible. Thus Y<0 and AD applies at the actual
lower adjacent corner P+f. In the type J own chart its norm is exactly

\[
 |P+f|^2=(1-t)^2+\varepsilon^2
 \le25/64+1/3600<(16/25)^2<r^2.
\tag{10}
\]

The exact rational reserve in the middle comparison is 6731/360000.
This actual point cannot belong to boundary D. We have proved, for both
complete genuine-leaf types and every original mean,

\[
 0<t<3/8.
\tag{11}
\]

The reflected statement holds at a tilted lower C with its original
height k and reflected two inward axes.

## 4. Two tilted outer roots necessarily have small tilts

Suppose both A and C are tilted. Write the actual lower frame as

\[
 C=P_C+[0,1](-\bar c,\bar s)+[0,1](-\bar s,-\bar c),
 \qquad \bar c,\bar s>0,\quad\bar c^2+\bar s^2=1.
\]

For 0<z<min(c,bar c), their actual sections at x=epsilon-z have
A's lower endpoint t-z*s/c and C's upper endpoint -k+z*bar s/bar c.
Both sections have positive length. Their initial vertical order is A
above C; continuity and disjoint interiors prevent that order from
reversing anywhere in this common open x interval. Taking its limiting
endpoint, physical nonoverlap gives

\[
 t+k\ge\min(c,\bar c)
          \left(\frac sc+\frac{\bar s}{\bar c}\right).
\tag{12}
\]

This remains weak at all actual tangencies. Choose c<=bar c by reflecting
and exchanging the two outer labels if necessary. Then s>=bar s and

\[
 s\le t+k<3/4,
 \qquad c,\bar c>\sqrt7/4>1/2.
\]

The two genuine-leaf inequalities (7) now give t,k<(7/2)epsilon.
Using (12) again gives s,bar s<7epsilon<7/60. Hence both cosines exceed
99/100; the squared reserve is 283/45000. One final substitution in (7)
gives

\[
 t,k<\frac{335}{297}\varepsilon<\frac65\varepsilon,
 \qquad s,\bar s<t+k<3\varepsilon.
\tag{13}
\]

In particular both tilted roots satisfy the common small chart

\[
 t<2\varepsilon,\qquad s<3\varepsilon<1/20,
 \qquad c>99/100.
\tag{14}
\]

The proof of (12)--(14) is physical and uses both actual root sections;
it does not assume an A--C edge or an equality of their supports.

## 5. Exactly one tilted outer root gives the same small chart

Suppose A is tilted and C owns the actual East axis toward B. The actual
C horizontal interval is [epsilon-1,epsilon], and its right-side mean
has height -k<0. The complete genuine S support cover of this rectangle
leaves exactly:

* a near-South leaf, strict at (epsilon,-T) with
  T=sqrt(d²-epsilon²), or owned South with T=d; in either case
  \[
  C=[\varepsilon-1,\varepsilon]\times[-T,1-T],
  \quad T=1+\eta,\quad0<\eta\le\varepsilon;
  \tag{15}
  \]
* a strict far-left leaf at (epsilon-1,+z) or (epsilon-1,-z), where
  \[
  z=2\sqrt\varepsilon<13/50.
  \tag{16}
  \]

For completeness, a West owned leaf would require 1-epsilon=d, an
East leaf would require epsilon=d, and a North leaf is impossible since
the unit side contains the negative height -k. The upper-near vertex has
norm below d whenever its outward radial sign is positive. The two far
vertices have norm d exactly when their y coordinate is +/-z. Thus all
owned endpoints as well as strict vertices are included above.

If the far-left leaf has y=-z, C's vertical interval is [-z,1-z]. By
(11), the actual upper A vertex P=(epsilon,t), 0<t<3/8, lies in the
relative interior of C's right side. A has a strictly leftward inward
sector at P, so its interior overlaps C. This case is impossible.

If the far-left leaf has y=+z, C's vertical interval is [z-1,z]. The
same actual support-side argument forces t>=z. Type V is then impossible
by t<2sqrt(epsilon)=z. In type J, combining t²>=4epsilon with (6) gives

\[
 c\le t(1+s)/4<t/2<3/16,
 \qquad s>15/16.
\]

The real A leaf direction (-s,c) and the real C leaf direction
(-(1-epsilon),z)/d both lie above West, each within atan(1/3) of it:
c/s<1/5 and z/(1-epsilon)<78/295<1/3. Their actual mutual angle is
less than atan(1/3)<1/3. Their equal-radius centers consequently have
distance less than (91/60)/3=91/180<1, contradicting their disjoint
open incircles. These are the two actual leaves, not substituted rays.

Only (15) remains. The actual lower adjacent A corner

    Q_0=(epsilon-c,t-s)

has x strictly inside C's horizontal interval and y>-1>-T. It cannot
lie in int(C), so physical nonoverlap forces

\[
 s\le t+\eta.
\tag{17}
\]

By (11), s<3/8+1/60=47/120<2/5 and c>9/10. Substituting (7) gives
t<(14/9)epsilon<2epsilon. Equation (17) then gives s<3epsilon and
c>99/100. Thus the same full small chart (14) holds. Reflection covers
the other ordered choice of the one tilted root.

## 6. Complete AD port and force cover in the small tilted chart

We now keep any actual tilted upper root satisfying (14), in either
genuine-leaf type. The full force equation always gives a strictly
positive AD component along f. Its far-f/far-j corner cannot be shared
by any actual contained unit: both of that corner's own coordinates
about O exceed 9/10. Indeed, for V put

\[
 u=\varepsilon c+ts,\qquad v=tc-\varepsilon s.
\]

Then P has own coordinates (-u,v), with

\[
 0<u<1/50,\qquad 1+v>99/100.
\tag{18}
\]

The far corner is (1-u,1+v). For J it is (1-t,1+epsilon), and
t<1/30. In both cases A occupies the inward Southwest quadrant in
this own frame. The full tangent-sector proof in Section 1 of
`SHORT_ARM_THREE_FORCE_TRIANGLE_PARENT_NEAR_ROOT_FRESH_EXCLUSION.md`
forces any other unit touching that corner to have an actual point of
squared norm greater than 221/50=1105/256+663/6400. This is a purely
physical corner statement; no triangle or force premise is imported.

Consequently the full remaining AD cover is exactly:

1. a strict lower adjacent vertex P+f, with AD vector X(f-r*j), X>0,r>0;
2. the owned +f side, with original mean P+f+rho*j, 0<=rho<=1, and AD
   vector X*f, X>0.

Here are the exact ratios and means obtained from the full moment about
the unchanged P. The real leaf moment is alpha*u/d in V and alpha*t
in J; the entire AB force acts at P.

| Genuine leaf | Strict lower vertex ratio r | Owned +f actual mean rho |
| --- | --- | --- |
| V | u*s/[c(1+v-u)+u*s] | u*s/[c(1+v)+u*s] |
| J | t*s/[c(1-t)] | t*s/c |

These are identities, not chosen means. For example in V, scaling by
d/alpha gives AD=(ell*c+u,ell*s-(1+v)). At the lower vertex the full
moment sets its second component to -u; on the owned side that component
is zero and rho times its first component equals u. The displayed two
formulas follow. The J derivation is identical with actual leaf offset
(t,1) and force along j. Every denominator is positive by (14),(18).

The complete uniform bounds are

\[
 0<r<1/100\quad\hbox{in the strict case},
 \qquad 0<\rho<1/100\quad\hbox{in the owned case}.
\tag{19}
\]

For V, the larger ratio is at most 10/9603<1/100, using
u<1/50,s<1/20,c>99/100 and 1+v-u>97/100. For J the larger ratio
is at most 5/2871<1/100, using t<1/30 and 1-t>29/30. These bounds
also prove that no original side endpoint has silently survived beyond
its actual moment equation.

Unify the port notation by taking rho=0 in the strict case. Then the
unchanged actual D port is

\[
 Q_A=P+f+\rho j
   =(\varepsilon-c-\rho s,\ t-s+\rho c).
\tag{20}
\]

Unify the normal notation by taking r=0 in the owned case. The actual
outward D normal is a positive multiple of

\[
 m_A=(c-rs,s+rc).
\tag{21}
\]

Its two components are strictly positive, since s>0. Its slope satisfies

\[
 0<\frac{m_{A,y}}{m_{A,x}}
 <\frac{3/50}{1979/2000}
 =\frac{120}{1979}<\frac1{10}.
\tag{22}
\]

Equation (20) has

\[
 -1<Q_{A,x}<-29/30,\qquad |Q_{A,y}|<1/20.
\tag{23}
\]

For the lower x bound use rho*s<3epsilon/100, so epsilon-rho*s>0.
For the upper one use 99/100-1/60-29/30=1/150. Its y coordinate is
greater than -s>-1/20 and less than 1/30+1/100=13/300<1/20.
Every original vertex/side mean and both V/J real-leaf forms have now
been included.

## 7. The original two D supports satisfy the accepted physical cap

### 7.1. Both outer roots tilted

Apply Section 6 also to the actual reflected lower root. Its unchanged
D port has the same bounds (23); its outward D normal has positive x,
strictly negative y, and absolute slope less than 1/10. The two normals
are therefore acute: after positive rescaling their dot product is
1-z_A*z_C>0, where 0<z_A,z_C<1/10.

The two actual ports have squared distance less than

\[
 (1/30)^2+(1/10)^2=1/90<1.
\tag{24}
\]

### 7.2. Exactly one outer root tilted

The lower owned root is (15). Use its actual own axes f_C=(-1,0),
j_C=(0,1), and put U=1-epsilon. Its incoming point has own coordinates
(-epsilon,-k). Its real leaf has coordinates (xi,-T), where xi=-epsilon
for the strict near-South leaf or xi=0 for its owned South side.

The full C3 force gives the remaining CD vector proportional to
(lambda-xi,T), both positive, so its actual application is exactly

\[
 Q_C=(\varepsilon-1,-\eta).
\tag{25}
\]

The full unchanged origin moment is

\[
 \lambda(k-\eta)=UT-\eta\xi.
\]

Thus k>eta, and the absolute downward slope of the actual outward D
normal is

\[
 z_C=\frac{T(k-\eta)}{UT-\xi k}
 \le\frac{k-\eta}{U}<\frac{k}{1-\varepsilon}<\frac{60}{59}.
\tag{26}
\]

It is strictly positive. In particular the two outward D normals have
opposite strict y signs and positive dot product, since (22),(26) give
z_A*z_C<6/59<1. The actual point (25) satisfies (23), and (24) again
bounds the distance of the two original ports. No C2 or shortened star
has replaced this full C3 calculation.

### 7.3. Physical contradiction in both complete cases

In either row, the actual D ports lie at x<-29/30 and |y|<1/20<1/4,
are less than one apart, and have actual outward normals with positive
x components, opposite strict y components, and positive scalar product.
These are exactly the full hypotheses of
`CLOSE_SUPPORT_PORTS_STRADDLING_NORMALS_FRESH_EXCLUSION.md`
(`f3c83072e2e09bc844bbd1a79813ab76b7979d008980ce9b2be07f25b85811d2`).
Its complete independent acceptance is
`REVIEW_CLOSE_SUPPORT_PORTS_STRADDLING_FRESH_ROOTED_BLOCKS_2026_10_27.md`
(`81ce471afe1f69d9f6aa0495750cbdcf0c1084e1c6f18d4731ad2ab7821f9b38`).

That force-free theorem excludes the actual contained D, including
coincident ports, vertex/side endpoints and every physical circle mask.
It never identifies a support-line meeting with force-line concurrence.
This gives the required contradiction in both entire original interfaces.

## 8. Original join and limits of exports

Sections 2--3 exhaust every genuine leaf at every actual tilted outer
contact. Sections 4 and 5 separately cover two tilted outer roots and
each ordered one-tilted/one-owned placement. Sections 6--7 keep every
remaining original D application, mean and normal. They therefore exclude
the whole parallel-middle case with at least one outer root not owning
its B-contact axis, without an A--C edge or a root force deletion.

The complementary both-owner interface is separately proved in
`THREE_LEAF_C4_OWNED_NEIGHBORS_FRESH_EXCLUSION.md`. With the common
middle-root theorem these two complete interfaces cover the original
high all-S A3 attachment. The earlier low/critical and D-leaf reductions
still enter through their exact separate whole sources; this file does
not itself change any coarse or fine metadata.

The local far-opposite leaf and height arguments require a true outer
degree-three root. They must not be imported into a diamond H4/K4 star.
The geometric section-order inequality and the final physical D cap
have only their explicitly stated physical scopes. All nine squares,
positive forces, actual side means, original owners, circle masks and
zero corner weights remain. No sampled pose, numerical search,
computational certificate, compilation, CI, remote edit or normal
reselection is a premise.
