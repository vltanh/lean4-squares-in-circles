# Tilted wall tips in the parallel D-leaf C4 have no westward outgoing force

**Status: complete hand branch theorem; root and two separate independent full hand
audits passed.** This source treats the entire tilted-tip
domain of the parallel D-leaf C4 wall model, including every frame of
the other tip and of the middle boundary square. All physical circle
masks, contact owners and actual side means remain.

The wall model has positive graph \(A-B-U-C-A\), with a radial D
leaf at the clear articulation A. The two actual cycle normals outward
from A are both \(-e_x\). Put

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 r=R-\sqrt2,\qquad s=1-r,
 \qquad A=[-s,r]\times[-v,H],\quad H+v=1,
 \quad H,v>0.
 \tag{1}
\]

The two wall applications, including means on any shared side, are

\[
 P_B=(-s,y),\qquad P_C=(-s,-w),\qquad y,w>0,
 \qquad y+w\le1.
 \tag{2}
\]

B,U,C are loaded degree-two bodies and physically touch the circle.
Their positive pair edges and circle loads are the actual physical
ones. The reduction from general parallel A reactions to this wall
model is a separate premise; no possible positive-right A reaction is
discarded by the present statement.

**Theorem.** If B is tilted, its actual outward BU normal has strictly
positive first coordinate. The reflected statement holds for a tilted
C. In particular no tilted tip can send a westward or vertical
outgoing force toward U. The proof includes the whole mixed-normal
contact at its lower vertex and does not assume any owner for BU.

Together with the complete aligned-tip sign theorem, this supplies the
parallel wall-model contradiction: both outward U pair normals have
nonpositive first coordinate, whereas U's circle resultant has strictly
negative first coordinate. No statement about U's frame is required.

## 1. Whole wall-tip geometry and uniform constants

The torque equation at A, whose leaf has zero origin moment, forces
the two nonzero wall heights to have opposite signs. Neither height
can vanish: every point of a boundary unit has norm at least r, while
\(s<r\). This gives exactly (2), after relabeling.

The boundary-point bound yields

\[
 y,w\ge\sqrt{r^2-s^2}=\sqrt{1-2s}.
\]

Since \(y+w\le1\), and the lower R endpoint gives \(s<4/9\),

\[
 \frac38\le s<\frac49<\frac9{20},\qquad
 \frac13<y,w<\frac23,
 \qquad |P_B|,|P_C|<\frac56.
 \tag{3}
\]

In particular

\[
 R\le\frac58+\sqrt2,
 \qquad R^2<\frac{17}{4}.
 \tag{4}
\]

For the last comparison use \(\sqrt2<10/7\): the squared upper
bound is less than \(153/64+25/14=1871/448<17/4\).
A two-physical-circle-corner unit is radial S and every point of it
has norm greater than \(9/10\). Thus (3) proves that B and C each
have exactly one physical circle corner, regardless of the original
corner-weight masks.

The positive radial concurrence theorem
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, applies to
each tip because U is a boundary neighbor. The concurrence lies
inside the unique-corner tip and behind each actual support contact.

### 1.1 The entire tilted upper tip

If B is tilted, its rightmost support is the vertex \(P_B\). Write
its inward side axes as

\[
 e_1=(-a,b),\qquad e_2=(-b,-a),
 \qquad a,b>0,\quad a^2+b^2=1.
\]

No adjacent vertex can be its circle corner, since its norm is at most
\(|P_B|+1<11/6<79/40\). Therefore the circle corner is opposite
\(P_B\). Put

\[
 p=a+b,\qquad k=b-a,
 \qquad z_B=(-s-p,y+k),
 \qquad p^2+k^2=2.
 \tag{5}
\]

The radial concurrence is on the horizontal A force line and has the
form

\[
 q_B=(-s-\ell,y)=\lambda z_B,
 \qquad \ell\ge0,\quad0<\lambda\le1.
\]

Its second coordinate gives \(k\ge0\), so \(a\le b\) and
\(0\le k<1\). More explicitly,

\[
 \lambda=\frac{y}{y+k},\qquad
 \ell=\frac{p y-s k}{y+k}\ge0,
 \qquad
 c_B=(-s-p/2,y+k/2).
 \tag{6}
\]

The lower tilted tip has the reflected description with w in place
of y. In particular both centers and both unique circle corners are
strictly northwest/southwest, respectively.

### 1.2 Every aligned upper tip and its full mean

If B is aligned, write

\[
 S=s+1,\qquad Y=\sqrt{R^2-S^2},\qquad
 B=[-S,-s]\times[Y-1,Y].
 \tag{7}
\]

The circle corner is the upper-left one: its positive radial
concurrence has second coordinate y>0, so a negative lower circle
corner cannot supply its ray. The full actual mean satisfies
\(Y-1\le y\le Y\); it is not set to either endpoint. Its center
is \((-S+1/2,Y-1/2)\). The lower tip is reflected.

The following bounds include the full window and all such means:

\[
 \frac{11}{8}\le S<\frac{36}{25},\qquad
 \frac43<Y<\frac{151}{100},\qquad
 |c_B|<\frac{69}{50}.
 \tag{8}
\]

For S use (3) and \(\sqrt2<283/200\) at \(R=79/40\).
The lower Y bound follows from
\((79/40)^2-(36/25)^2>16/9\). The function
\(Y^2=2+2\sqrt2-2s(2+\sqrt2)\) decreases with s, so

\[
 Y^2\le\frac12+\frac54\sqrt2
       <\frac{127}{56}<\left(\frac{151}{100}\right)^2.
\]

The middle comparison uses \(\sqrt2<99/70\).

Finally
\(|c_B|^2<(47/50)^2+(101/100)^2=19037/10000
<(69/50)^2\).

Every upper tip, tilted or aligned, consequently has center
\((-X_B,Y_B)\) with

\[
 X_B\ge s+1/2,\qquad 0<Y_B\le y+1/2.
 \tag{9}
\]

The lower tip has center \((-X_C,-Y_C)\), with the corresponding
inequalities using w.

## 2. A one-sided 22.5-degree arc for a boundary unit

We prove the needed frame-uniform statement in full. Let a boundary
unit in the declared radius window have center c and a farthest circle
corner z satisfying \(\det(c,z)\ge0\). Then its open interior
contains the closed radius-\(5/4\) arc from the center direction
counterclockwise through angle \(\pi/8\). The far endpoint can be
extended slightly while remaining inside.

Choose positively oriented own axes toward z. In these coordinates

\[
 c=\varrho(\cos\theta,\sin\theta),\qquad
 0\le\theta\le\pi/4,
 \qquad
 \varrho^2+\varrho(\cos\theta+\sin\theta)+1/2=R^2.
 \tag{10}
\]

The angle range is exactly the determinant condition: adding
\((1/2,1/2)\) to c turns its direction counterclockwise precisely
when its first own coordinate is at least its second. This includes
the radial and diagonal limiting frames. Put
\(d=5/4\), \(\chi=\pi/8\), \(C=\cos\chi\),
\(T=\sin\chi\). Uniformly,

\[
 \frac54<\varrho<\frac{31}{20}<2,
 \qquad \varrho-dC<\frac25<dT<\frac12.
 \tag{11}
\]

The center lower bound is \(\varrho\ge R-1/\sqrt2>5/4\).
The upper bound follows from
\(\varrho^2+\varrho+1/2\le1105/256\).
For the other comparisons use \(C>23/25\),
\(1/3<T<2/5\), all immediate by squaring the half-angle formulas.

The only nontrivial face at the far endpoint of the arc is the lower
first-coordinate face. Its inward clearance is equivalent to

\[
 f(\theta):=(\varrho-dC)\cos\theta+dT\sin\theta<1/2.
\]

At fixed R, differentiate (10):

\[
 \varrho'=-\frac{\varrho(\cos\theta-\sin\theta)}
 {2\varrho+\cos\theta+\sin\theta}.
\]

The quotient \(\varrho/(2\varrho+\cos\theta+\sin\theta)\)
is less than 2/5. Since \(\cos\theta\ge\sin\theta\ge0\),

\[
 \begin{aligned}
 f'(\theta)
 &\ge (dT-2/5)\cos\theta
       +\bigl(2/5-(\varrho-dC)\bigr)\sin\theta>0.
 \end{aligned}
\]

Thus its maximum is at \(\theta=\pi/4\), where
\(\varrho=R-1/\sqrt2\). The required strict inequality becomes

\[
 R<\sqrt2+\frac54(C-T).
\]

Indeed \(R<25/12\), while \(\sqrt2>707/500\) and
\(C-T=\sqrt{1-1/\sqrt2}>27/50\) give the stronger rational
lower bound \(2089/1000>25/12\) on the right.
For the last square-root comparison use
\(1/\sqrt2<17/24\) and \(7/24>(27/50)^2\).

The remaining faces are strict directly from (11). At the far
endpoint its first coordinate is below the center's first coordinate.
Its second coordinate exceeds the center's second coordinate because
\((\varrho-dC)\sin\theta-dT\cos\theta<0\), and exceeds it
by less than \(dT<1/2\). The first coordinate differs below the
center by f, already proved less than 1/2. The center-direction
radius-d point is also in the open square, since
\(0<\varrho-d<3/10<1/2\).
Both coordinates vary monotonically along the intervening arc,
so the whole closed arc is inside. Strictness at its far endpoint
permits the asserted extension.

## 3. Every wall tip has a western tail longer than 22.5 degrees

For a tilted upper tip, (5)--(6) give

\[
 \det(c_B,z_B)=\frac{p y-s k}{2}\ge0.
\]

Section 2 therefore supplies exactly its western inner-circle tail.
Reflect for the lower tilted tip.

For an aligned upper tip, set \(X=S-1/2\) and
\(Y_0=Y-1/2\). At the point a further \(\chi=\pi/8\)
westward from its center direction, the inner-circle coordinates are

\[
 \left(-\frac{5(CX+TY_0)}{4|c_B|},
        \frac{5(CY_0-TX)}{4|c_B|}\right).
 \tag{12}
\]

The only difficult face is its bottom \(y=Y-1\). Using
\(C>12/13\), \(T<5/13\), and (8), the numerator exceeds
\(|c_B|(Y-1)\) by more than

\[
 \begin{aligned}
 &\frac{15}{13}(Y-1/2)-\frac{25}{52}(S-1/2)
          -\frac{69}{50}(Y-1)\\
 &\qquad>\frac{157}{16250}>0.
 \end{aligned}
 \tag{13}
\]

For this exact check the expression decreases with Y and S; insert
\(Y=151/100\) and \(S=36/25\). The trigonometric comparisons
are equivalent to \(\sqrt2>238/169\).
The left and top faces are automatic from \(S>5/4\), \(Y>5/4\).
For the right face, the magnitude of the negative first coordinate
in (12) is greater than
\((15/13)(7/8)/(7/5)=75/104>1/2>s\).
The center angle plus \(\chi\) is still below pi: indeed
\(Y_0/X>(5/6)/(47/50)>1/2>\tan\chi\).
Both coordinates therefore vary monotonically from the center direction to
this point; the center-direction point is inside by
`CENTERED_INNER_ARC.md`. Thus this closed arc too lies in the open
square and extends slightly past its western endpoint. Again reflect
for C.

The boundary contacts BU and UC and the eastern leaf order their
centers as B,U,C along the western arc, by
`CIRCLE_CONTACT_ANGULAR_ORDER.md`. The actual radius-5/4 intersection
of U is a connected open arc of length strictly greater than pi/4,
by `CYCLIC_GLOBAL_CONTINUATION.md`, Sections 2--4, and it contains
its center direction by `CENTERED_INNER_ARC.md`. Disjoint interiors
put that entire arc between the two just-proved western tails.
Consequently the western center gap \(\Phi\) of B and C satisfies

\[
                         \boxed{\Phi>\pi/2.}
 \tag{14}
\]

This applies to both aligned/tilted choices independently and uses
the actual open square arcs, not merely separated center points.

## 4. Every tilted wall tip has k greater than 7/10

Suppose B is tilted and \(k\le7/10\). Then
\(p=\sqrt{2-k^2}\ge\sqrt{151}/10>49/40\), so its center
coordinates in (6) satisfy

\[
 X_B=s+p/2>79/80,
 \qquad Y_B=y+k/2.
\]

For the other tip, whether aligned or tilted, (9) gives
\(X_C\ge7/8\) and \(Y_C\le w+1/2\). Thus

\[
 Y_B+Y_C\le y+w+7/20+1/2\le37/20.
\]

The actual two center vectors have scalar product

\[
 \begin{aligned}
 c_B\cdot c_C
 &=X_BX_C-Y_BY_C\\
 &>\frac{553}{640}-\frac{1369}{1600}
   =\frac{27}{3200}>0.
 \end{aligned}
\]

Their western angle lies in \((0,\pi)\), so it would be less
than pi/2, contradicting (14). We have proved, for every tilted tip,

\[
                             k>\frac7{10}.
 \tag{15}
\]

## 5. The entire mixed lower-vertex contact is screened

Consider the lower vertex of the tilted upper B,

\[
 T_B=P_B+e_2=(-s-b,y-a).
\]

Its actual outward contact normal toward U must be parallel to
\(T_B-q_B=(\ell-b,-a)\), with the positive outward sign, by
the proper-concurrence theorem. No contact owner has been specified.

Equation (15) gives the uniform strict bounds

\[
 a<\frac4{15},\qquad b>\frac{24}{25},\qquad p<\frac54.
\]

The expression for ell in (6) increases with y; after setting
\(y=2/3\), it increases with p, decreases with s, and decreases
with k. Bounding
\(y<2/3\), \(s\ge3/8\), \(k>7/10\), \(p<5/4\) therefore gives

\[
 0\le\ell<
 \frac{(2/3)(5/4)-(3/8)(7/10)}{2/3+7/10}
 =\frac{137}{328}.
\]

Set \(E=b-\ell\) and \(t=a/E\). Then

\[
 E>\frac{4447}{8200},\qquad 0<t<\frac12,
 \qquad t(y-a)<\frac15.
 \tag{16}
\]

For the last inequality, if \(y-a\le0\) it is immediate.
Otherwise use
\(a(y-a)\le a(2/3-a)<8/75\) and
\((8/75)/(4447/8200)<1/5\).

The normal is thus \((-1,-t)/\sqrt{1+t^2}\), and its actual
support value is

\[
 \begin{aligned}
 h_T&=\frac{s+b-t(y-a)}{\sqrt{1+t^2}}\\
 &>\frac{3/8+24/25-1/5}{9/8}
   =\frac{227}{225}>1.
 \end{aligned}
 \tag{17}
\]

Here \(\sqrt{1+t^2}<\sqrt5/2<9/8\). In particular
\(T_B-q_B\ne0\), so no coincident-concurrence exception was
lost when determining the normal.

No unit square in the containing disk can lie beyond this support
line. In fact, for a unit contained in \(n\cdot x\ge h_T>0\),
its center has \(n\cdot c\ge h_T+1/2\). For any own frame
\(u_1,u_2\),

\[
 \max_{\text{corners}}|z|^2
 =|c|^2+1/2+|c\cdot u_1|+|c\cdot u_2|
 \ge |c|^2+|c|+1/2
 \ge(h_T+1)^2+1/4>17/4,
\]

contradicting (4). This excludes every actual lower-vertex BU normal,
including U-owned, B-owned endpoint limits and any surviving free
normal. The lower-tip statement is reflected.

## 6. All remaining tilted-tip normal features have positive x component

At B, its circle corner has strictly positive second coordinate,
and its A force is horizontal. Its other actual outward normal g
toward U must therefore satisfy \(g_y<0\), by vertical force
balance. For the tilted square this leaves precisely its inner lower
face, lower vertex, outer lower face, rightmost vertex, or circle
corner. The circle corner cannot belong to another contained unit;
Section 5 excludes the lower vertex.

The outer lower face has normal \((-b,-a)\) and support

\[
 1+sb-ya>
 1+\frac38\frac{24}{25}-\frac23\frac4{15}
 =1+\frac{41}{225}>1.
\]

The same whole-unit cap argument excludes it, including arbitrary
means on that face. The inner lower face has normal \((a,-b)\)
with positive first coordinate. Every outward normal at the rightmost
vertex lies in the cone spanned by \((a,-b)\) and \((b,a)\),
whose nonzero vectors all have positive first coordinate.

These are all square support features with \(g_y<0\). Hence
\(g_x>0\), proving the theorem. Reflection proves the lower-tip
version with the same first-coordinate conclusion.

Every use of force was an actual body equation or the proved proper
concurrence theorem. The four completion squares were never moved or
discarded. No numerical angle cover, normal-ownership assumption,
Lean compilation or CI is a premise.
