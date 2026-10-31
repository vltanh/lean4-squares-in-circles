# An owned S/S triangle singleton has one adjacent-vertex port chart

Date: October 27, 2026.
Author: rooted_final_review.
Comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

**Status: complete continuous-domain analytic candidate, pending full
independent review.** This strengthens the cubic interface-angle result
by proving the actual leaf and contact-feature cover throughout the
whole original radius interval. No orientation or coefficient packet
is used. The remaining positive-width original S/S gate stays open.

## 1. Actual domain and complete necessary normal form

Use the common selected physical certificate in

\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1<61/60.
 \tag{1}
\]

H and B are distinct genuine radial S-leaf roots. The actual positive
degree of B is three, with neighbors its genuine leaf, H, and K.
K is a physical circle-touching unit distinct from both leaves and
physically touches H. Every force, degree, circle weight and mask at
H and K is arbitrary. The physical HK contact need not carry stress.
All other original units and forces remain.

Assume HB is an actual singleton and its actual H-to-B unit normal n
is owned only by H. Let P be its actual B vertex. The original physical
certificate makes P a relative-interior point of H's owned side: a
vertex/vertex singleton would instead have a normal strictly inside
both vertex cones, and so could not have this side owner.

**Theorem 1.1.** After naming the actual inward B axes v,w suitably,
all these conclusions hold simultaneously:

\[
 \begin{gathered}
 d>1,\qquad \delta=d-1\in(0,1/60),\\
 B=P+[0,1]v+[0,1]w,\qquad
 n=\alpha v+\beta w,\qquad
 \alpha=\cos\theta,\ \beta=\sin\theta,\quad 0<\theta<\pi/6,\\
 P=xv-uw,\qquad u>0,\qquad x\le\delta,\qquad
 h=\alpha x-\beta u\in[-\delta,\delta],\\
 \boxed{\quad \delta\ge
       \left(\frac{\beta}{1+\alpha}\right)^3
       =\tan^3(\theta/2).\quad}
 \end{gathered}
 \tag{2}
\]

The genuine B leaf has exactly one of these two complete features:

| Actual B leaf feature | Exact radial application and remaining interval |
| --- | --- |
| Adjacent vertex | p_B=P+v=(x+1)v-uw, with (x+1)^2+u^2=d^2, x+1>0, and 0<u<2sqrt(delta) |
| Positive far side | e_B=v, x=delta, with the actual radial mean d v on that side and 0<u<1 |

In particular v is the **closer** inward B axis to n; the genuine leaf
cannot be attached to the farther axis, either negative side, the HB
vertex, or the opposite B vertex.

Let m be the actual B-to-K unit normal, including the full original
contact mean before the conclusion is derived. Then BK is a singleton
at exactly the other adjacent vertex,

\[
 Q=P+w,\qquad
 m=\frac{w-rn}{|w-rn|},\qquad r>0,\quad \beta r<1,
 \tag{3}
\]

where, on the entire corresponding leaf features,

\[
 L=\beta x+\alpha u,\qquad
 r=\frac{u}{\beta+L}\quad\hbox{(vertex)},\qquad
 r=\frac u\beta\quad\hbox{(side)}.
 \tag{4}
\]

The denominator in the vertex formula is
beta(1+x)+alpha u>0. There is no global assertion r<beta or L>=0;
those sharper signs will only be used inside an explicitly contrary
radius-angle inequality in Section 5.

For the original H4/K3/B3/C2 hub-tip diamond, the already proved
whole-domain HB/BK ownership theorem makes the singleton BK in (3)
owned only by K. Thus this entire H-owned HB branch has no shared BK.
The actual H/K forces, physical C and all three extras are retained.

## 2. Whole owner support and the forbidden contact points

The arbitrary-degree owner-direction theorem gives d>=1. Put
delta=d-1 in [0,1/60). It gives the exact actual H supports

\[
 |h|\le\delta,\qquad
 d(e_H\cdot n)=h-1,\qquad
 |d(e_H\cdot Jn)|\le2\sqrt\delta<1.
 \tag{5}
\]

H's n-coordinate interval is [h-1,h]. In either signed perpendicular
own axis its maximum coordinate is at most one. Indeed if the actual
leaf has positive transverse coordinate y, that maximum is y<1;
if y<0, it is y+1<1; if y=0, its original aligned leaf mean gives
the whole allowed maximum interval [0,1]. Therefore

\[
 h_H(Jn)\le1,\qquad h_H(-Jn)\le1.
 \tag{6}
\]

Initially name the actual inward B axes arbitrarily and write
n=alpha v+beta w with alpha,beta>0. Strict positivity follows
from the unique B support vertex at P. Because P is a side-interior
point of H, the tangent sector of H there is a half-plane. B's
right-angle sector is strictly inside the opposite open half-plane
except for its vertex. The two remaining tangent gaps each have
angle strictly below pi/2. Any further unit square containing P
would have tangent sector of angle at least pi/2. Hence

\[
                              P\notin K.
 \tag{7}
\]

If the actual B leaf is at a strictly exposed support vertex p_B,
that point is the relative interior of its genuine radial leaf's
inner side. The same tangent-gap argument gives

\[
          p_B\notin K
       \quad\hbox{when the B leaf direction is strict at p_B}.
 \tag{8}
\]

These are statements about the actual occupied units, not new
normal choices. Aligned leaf directions and every actual side-mean
endpoint are kept in their side features below.

## 3. The entire wrong-leaf cover is impossible

Write the unchanged true B3 force equation as

\[
            \lambda e_B-\mu n+\nu m=0,
                         \lambda,\mu,\nu>0.
 \tag{9}
\]

### 3.1. The HB vertex and both negative own faces

If the genuine leaf application is P, e_B has nonpositive components
on both inward axes. The same is true if e_B is either negative own
side axis. Equation (9) makes both components of m strictly positive.
Its actual B application would be P+v+w, opposite the HB vertex.
This is impossible in the physical H-B-K triangle.

For completeness, H has maximum n-support h=n dot P. At Q=P+v+w,
K has its minimum-m support and n dot m>0. The complete strict
support-span bound, applied in direction -n, gives
min_K n dot z>n dot Q-1. But
n dot Q=h+alpha+beta>h+1. Thus min_K n dot z>h, separating the
actual H and K. This covers every negative-side leaf mean at once.

### 3.2. The opposite vertex, with every real BK mean

Suppose the actual leaf is at the opposite vertex and strictly
exposes it. Write

\[
 p_B=P+v+w=d(av+bw),\qquad
       a,b>0,\quad a^2+b^2=1.
 \tag{10}
\]

If both components of m are negative, its application is P,
contradicting (7). If both are positive, it applies at p_B,
contradicting (8). If m is either positive B axis, the physical
triangle side-normal lemma applied at B gives
m dot(-n)>=0, whereas its actual value is -alpha or -beta<0.
Thus only the two mixed quadrants and the two negative axes remain.

For m_v<0<m_w its actual application is Q=P+w. Torque about P
and the v-component of (9) give

\[
 \nu m_v=\lambda(b-a),\qquad
 \mu\alpha=\lambda b,\qquad
 \nu m_w=\mu(\beta-\alpha).
 \tag{11}
\]

Consequently a>b and beta>alpha. For the other mixed quadrant,
the reflected calculation gives a<b and alpha>beta.

For m=-v, retain the **entire actual side mean**
Q=P+tau w, 0<=tau<=1. Equation (7) gives tau>0. The complete
force and torque equations are

\[
 \mu\beta=\lambda b,\qquad
 \nu=\lambda\left(a-\frac\alpha\beta b\right),\qquad
 \nu\tau=\lambda(a-b).
 \tag{12}
\]

Positivity and tau>0 give a>b. Since tau<=1, the last two
identities imply a-b<=a-(alpha/beta)b, hence alpha<=beta.
The reflected negative-w case gives a<b and alpha>=beta.
No application mean has been chosen or discarded.

Every actual normal feature has therefore given

\[
                  (a-b)(\alpha-\beta)\le0.
 \tag{13}
\]

It follows that

\[
 \begin{aligned}
 n\cdot e_B
 &=\frac{(\alpha+\beta)(a+b)+(\alpha-\beta)(a-b)}2
       \le\frac{\alpha+\beta}{\sqrt2},\\
 h&=d(n\cdot e_B)-(\alpha+\beta)
       \le\left(\frac d{\sqrt2}-1\right)(\alpha+\beta)
       <-\frac{19}{80}<-\frac1{60}.
 \end{aligned}
 \tag{14}
\]

Here 1/sqrt(2)<3/4, d<61/60, and alpha+beta>=1. The final
rational reserve is 19/80-1/60=53/240>0. This contradicts
h>=-delta>-1/60. Thus the opposite vertex is impossible on
the full radius interval. Its aligned directional endpoints were
already retained as positive-side leaf features, not lost here.

### 3.3. The exhaustive surviving genuine leaf

The only remaining radial support features are a positive adjacent
vertex or a positive far side. Choose v to be that actual leaf
axis and w the other inward axis. Its actual support point then
has exactly the two forms in Section 1, initially with u>=0 and
0<=u<=1 in the side case. This naming does not assume v is the
closer axis to n. That stronger conclusion follows from Section 5.

## 4. The whole BK contact and exact original concurrence

In both remaining leaf features e_B dot w<=0. Equation (9) gives
m dot w>0. The choice m=w is excluded by the physical triangle
side-normal lemma, because w dot(-n)=-beta<0. If m dot v>0,
the actual application is P+v+w, already excluded by the opposite-
vertex support-span argument in Section 3.1. Therefore

\[
                     m\cdot v<0<m\cdot w,
                         \qquad Q=P+w.
 \tag{15}
\]

This is a strict B support vertex, so BK cannot have positive
shared length. This conclusion did not assume a chosen owner or
a singleton on BK.

The actual HB force line is P+R n. Its intersection with the
genuine radial leaf line is q=P+r n, with r in (4). For a vertex
leaf the denominator beta+L=beta(1+x)+alpha u is positive, and
direct subtraction gives

\[
       q=\frac{L}{\beta+L}(P+v),\qquad
                   q-P=\frac u{\beta+L}n.
 \tag{16}
\]

For a side leaf the radial line is R v and r=u/beta.
The two original force lines are nonparallel in either feature.
The real B3 moment equation makes the BK force line pass through
the same q. If u=0, then q=P, and its line through Q=P+w would
force m to be an axis, contrary to (15). Thus u>0 and r>0.

Since Q-q=w-rn has negative v-component and the actual m has
the same strict sign, its proportionality factor is positive.
Equation (15) now gives exactly (3), including beta r<1. In the
side case beta r=u, so the complete actual side interval reduces
to 0<u<1, with both former endpoints excluded by actual forces.

## 5. The leaf-relative cubic bound and the closer-axis conclusion

Put t=beta/(1+alpha) in (0,1). Suppose, for contradiction,

\[
                               \delta<t^3.
 \tag{17}
\]

Both actual leaf features have x<=delta. The original support
h=alpha x-beta u>=-delta gives

\[
                   0<u\le\frac{\delta(1+\alpha)}\beta
                               =\frac\delta t.
 \tag{18}
\]

In the vertex case u^2<=delta^2/t^2<delta t<delta, so
(1+x)^2=d^2-u^2>1 and x>0. The side case has x=delta.
If delta=0, (18) already contradicts u>0. Thus, under (17),
x>=0, L>=0 and

\[
 0<r\le u/\beta,\qquad \beta r\le u,\qquad
 r\le\frac{\delta(1+\alpha)}{\beta^2}
        <\frac\beta{(1+\alpha)^2}<\beta.
 \tag{19}
\]

Take Jn=-beta v+alpha w. Then
P=h n-L Jn, and w-rn has positive coefficients beta-r and
alpha in that H frame. Equations (5)--(6) bound the support of
the **entire actual H**, giving

\[
 \begin{aligned}
 (Q-hn-Jn)\cdot(w-rn)
   &=1-\alpha-\alpha L-\beta r,\\
 \alpha L+\beta r
   &\le\alpha\beta\delta+(1+\alpha^2)u
       \le\delta\frac{(1+\alpha)^2}\beta.
 \end{aligned}
 \tag{20}
\]

The last identity uses
alpha(1-alpha^2)+(1+alpha^2)(1+alpha)=(1+alpha)^2.
The exact threshold is

\[
       \frac{\beta(1-\alpha)}{(1+\alpha)^2}
              =\left(\frac\beta{1+\alpha}\right)^3=t^3.
 \tag{21}
\]

Consequently (17) makes the first expression in (20) strictly
positive. Dividing by |w-rn| gives h_H(m)<Q dot m=min_K m dot z,
contradicting the actual physical H/K contact. Thus delta>=t^3.
Since t>0, d>1 follows as well.

Let theta be the actual angle from the real leaf axis v to n.
Then t=tan(theta/2). The exact comparison

\[
 \tan^3(\pi/12)=26-15\sqrt3>1/60
 \tag{22}
\]

follows by squaring the positive quantities in
sqrt(3)<1559/900; the numerator reserve is
1559^2-3(900)^2=481>0. Since delta<1/60, (21)--(22)
force theta<pi/6. In particular v is the closer inward axis.
The previous frame-angle bound is strengthened to a bound tied
to the **actual** genuine leaf feature, with its equality retained.

For the vertex feature one also obtains the asserted quantitative
height bound on this full surviving domain. Since alpha>cos(pi/6)
and delta<1/60, alpha+beta u-delta>0. Its actual support gives

\[
 \alpha\sqrt{d^2-u^2}\ge\alpha+\beta u-\delta.
\]

Squaring these positive sides and using alpha^2+beta^2=1 yields

\[
 u^2+2\beta(\alpha-\delta)u
       \le2\delta(\alpha^2+\alpha)-\beta^2\delta^2<4\delta.
 \tag{23}
\]

All omitted terms on the left are positive. Hence u<2sqrt(delta).
There is no assertion of the same bound for the aligned side slider.

## 6. Exact original join, inputs and remaining scope

In the original hub-tip diamond the true B3 has precisely the
neighbors required here. H is the actual H4 root and K the actual
K3 physical boundary hub. C and the three extra units are untouched.
The whole normal-form source supplies side ownership on BK in the
existing common certificate. Since (15) is strict at the B vertex,
that owner can only be K. Thus both HB and BK are side-owned
singletons in this entire H-owned HB family, with the exact actual
port positions and force-line formulas (2)--(4).

This strengthens a necessary continuous normal form; it does not
exclude the remaining narrow-angle chart, the B-owned HB singleton
family, the shared HB family, or the entire original S/S gate. No
original checklist row or coarse cell is declared closed by this
source alone. The exact threshold equality in (2) remains.

| Direct input | SHA256 | Actual scope used |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine radial S support points, inward segments and complete side means |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Singleton owner is at a side-interior/strict-vertex contact; original force and moment laws |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | Arbitrary-degree H owner supports and the full transverse leaf bound |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Every actual side-normal sign and the full strict support-span lemma |
| SS_HUB_TIP_SHARED_CONTACT_NORMAL_FORM.md | 18d2f8f7cfc86f9521b68ed05f1450ad19e79ed8399065cffa0419acca687278 | Original-domain BK ownership only, for the separate K-owner conclusion in this section |

The original critical-wall, fixed-angle and cubic manuscripts remain
unchanged. Sections 3--5 above reproduce the whole new feature and
scalar argument, so no earlier small-point estimate or coefficient
packet enters this source. Every physical mask, individual zero
circle weight, positive force, true degree, upper-radius endpoint,
side mean and original unit is retained. No computational certificate,
post-extraction selection, new gate ID, ledger edit, Lean run, CI or
remote mutation is introduced.
