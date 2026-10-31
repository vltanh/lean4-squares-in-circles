# An H-owned unloaded end of the four-spoke pentagon has two fixed opposite return vertices

Date: October 28, 2026.

**Status: complete new radius-free necessary-domain hand theorem, frozen for
full independent and root review. Neither original H4_D0 load family is
declared excluded.**

## 1. Original scope and exact conclusion

Retain the original actual unit squares H,A,B,C,D,E and all contacts

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is unloaded with its full four positive neighbors A,B,C,D. D is unloaded
with its full three positive neighbors H,C,E. All original pair magnitudes
are positive. Every body is physically interior-disjoint from every other
body. A,B,C,E retain their actual degrees, loads, physical boundary masks,
frames and force equations. No circle hypothesis is needed here.

Assume that H owns its original normal toward D. Use the existing strict
point-normal convention throughout. The complete accepted shared-end and
opposite-horizontal-sign results give, after a rigid motion and the
legitimate horizontal reflection,

\[
\begin{gathered}
H=[0,1]^2,\qquad n_{HD}=(0,1),\qquad n_{HA,x}<0,\quad n_{HA,y}<0,\\
\max_A y<1,\qquad n_{HC,x}>0,\quad n_{HC,y}\ge0,\\
P=(p,1),\quad 0<p<1,\qquad
D=P+[0,1]u+[0,1]v,\\
u=(a,b),\quad v=(-b,a),\quad a,b>0,\quad a^2+b^2=1.
\end{gathered}                                                     \tag{1}
\]

In particular D is genuinely tilted and HD is its bottom-vertex singleton.
Let \(\gamma>0\) be the original HD force magnitude.

**Theorem.** Every original configuration in (1) necessarily has

\[
D\cap C=\{P+u\},\qquad D\cap E=\{P+v\}.                           \tag{2}
\]

Both original return normals strictly expose these opposite D vertices.
There is a number \(\eta>0\) such that, in the actual orthonormal frame
\((u,v)\), the three unchanged force vectors at D are exactly

\[
\begin{array}{c|c|c}
\text{neighbor}&\text{D application in frame coordinates}&
                    \text{force vector in that frame}\\ \hline
H&(0,0)&(-\gamma b,-\gamma a)\\
C&(1,0)&(\eta+\gamma b,-\eta)\\
E&(0,1)&(-\eta,\gamma a+\eta).
\end{array}                                                       \tag{3}
\]

These are the original magnitudes, not a new choice of normal or stress.
The normal on CD may be C-owned or free, and the normal on DE may be
E-owned or free. All such possibilities remain.

Thus this theorem excludes every D-owned CD alternative, every DE top
vertex alternative, and the entire D-owned DE upper-side alternative,
including arbitrary shared intervals and their actual aggregate means.
No mean is fixed before its case is excluded. It does not assert that
the remaining domain (2)--(3) is empty.

For both original families
\(\mathrm{H4\_D0.L124}\) and \(\mathrm{H4\_D0.L0124}\), substitute
\((A,B,C,D,E)=(0,1,2,3,4)\). This is their entire H-owned H3 end-spoke
interface. In L124 the graph-preserving reflection gives the analogous
statement at end 0 whenever H owns that end normal. A loaded end of
L0124 is never assigned an unloaded equation.

## 2. A sharpened whole-unit support span

Let K be an actual unit square, let n be a unit direction, and let Q be
any actual minimum-n support point of K. Q may be a side mean, including
either endpoint. If e is a unit direction with \(n\cdot e<0\), then

\[
       \max_{Z\in K}e\cdot(Z-Q)
            \le \sqrt{1-(n\cdot e)^2}.                            \tag{4}
\]

At a vertex Q write its two orthonormal inward axes as r,s, so
\(n\cdot r,n\cdot s\ge0\). Both \(e\cdot r,e\cdot s\) cannot be
positive, since that would imply \(n\cdot e\ge0\). At most one positive
axis component contributes to the maximum. For any unit axis r with
\(n\cdot r\ge0\), its positive e component is at most
\(\sqrt{1-(n\cdot e)^2}\): decompose e into its negative n component
and its perpendicular component and maximize on the closed unit
semicircle \(n\cdot r\ge0\). This also covers a zero axis component.

At a side support, write \(Z-Q=t n+\lambda Jn\), with \(0\le t\le1\)
and \(\lambda\) in an interval of length one containing zero. The
normal term has nonpositive e projection, and the transverse term is
at most \(|e\cdot Jn|=\sqrt{1-(n\cdot e)^2}\). This proves (4) with
the complete actual mean interval.

In particular, (4) is strictly less than one. The non-strict sharpened
form, rather than only that strict unit bound, will be used once below.

## 3. The whole CD contact set lies on one actual D edge

Write \(q=1-p\), so \(0<q<1\). There are precisely two HC alternatives
in (1).

If \(n_{HC,y}>0\), its H application is the original corner

\[
                         S=(1,1).
\]

In the D frame this point has coordinates

\[
                         S_D=(a q,-b q),                        \tag{5}
\]

with \(0<(S_D)_u<1\) and \((S_D)_v<0\).

If \(n_{HC,y}=0\), the normal is East and the entire C lies in
\(x\ge1\). Choose any original physical HC point \(S=(1,s)\),
\(0\le s\le1\); its actual force mean is one permissible choice. Then

\[
 S_D=(a q+b(s-1),-b q+a(s-1)),\qquad
                 (S_D)_u<1,\quad(S_D)_v<0.                      \tag{6}
\]

Take any actual \(Z\in C\cap D\). Its D coordinates belong to
\([0,1]^2\). Suppose its v coordinate is positive. In the northeast
HC case, the segment from (5) to Z contains a point with both D
coordinates strictly between zero and one, including when Z has
u coordinate zero or one. That point belongs to C by convexity and
to the open interior of D, contradicting physical interior
disjointness.

In the East HC case, \(Z_x\ge1\) gives

\[
                  a Z_u\ge q+b Z_v>0.
\]

Thus \(Z_u>0\). A point of the segment from (6) sufficiently close to
Z again has both D coordinates strictly between zero and one. This
is the same contradiction. As usual, a point of a closed physical
unit in the open interior of another forces open-interior overlap.

Consequently every actual CD point has v coordinate zero. The point
P itself is impossible: in the northeast case it lies strictly below
the minimum HC support value on C, because
\(n_{HC}\cdot(P-S)=-q n_{HC,x}<0\); in the East case \(P_x=p<1\).
We have proved the whole-set statement

\[
                 C\cap D\subset\{P+t u:0<t\le1\}.               \tag{7}
\]

No force application or common point has been replaced by an arbitrary
vertex in this argument.

## 4. Every D-owned CD alternative is excluded

If the original CD normal is D-owned, (7) forces its outward direction
from D to be \(-v\). This includes every positive shared segment and
every mean on it, and any singleton at the relative interior of this
D edge.

For completeness, the other D axis u cannot occur only at the endpoint
\(P+u\): a C side interior with that axis would produce additional CD
points on the D edge in the positive v direction, contrary to (7);
a point-only vertex/vertex contact cannot carry a D axis under the
retained strict convention.

Write the original CD vector as \((0,-\mu)\) in the D frame, with
\(\mu>0\). The complete, unchanged force equation at D gives its E
vector as

\[
                         (\gamma b,\gamma a+\mu).
\]

Both components are positive. Its actual D support is the top
vertex \(P+u+v\), whose world height is \(1+a+b\). The E vector has
world y component \(\gamma+\mu a>0\). Apply the strict consequence of
(4) to the actual E minimum support at that vertex in the South
direction. It gives

\[
                         \min_E y>a+b>1.                       \tag{8}
\]

The strict inequality \(a+b>1\) follows from \(a,b>0\) and
\(a^2+b^2=1\). Equation (8) contradicts \(\max_A y<1\) and the
actual AE contact.

All D-owned CD cases are therefore impossible. By (7) and the strict
point-normal convention, the remaining CD contact is exactly the
singleton \(P+u\), and its vector in the D frame has the form

\[
                           (\xi,-\eta),\qquad \xi,\eta>0.       \tag{9}
\]

The parameter \(\eta\) is the actual force component. Its positivity
is not a subsequent generic-normal selection.

## 5. The DE top vertex is excluded

Using (9), full force balance at D gives its actual E vector

\[
                       (\gamma b-\xi,\gamma a+\eta).            \tag{10}
\]

The v component is strictly positive. If \(\gamma b-\xi>0\), its
support is again the top vertex \(P+u+v\). The world y component is

\[
 \gamma-\xi b+\eta a
       >\gamma(1-b^2)+\eta a>0.
\]

The identical whole-E bound (8) again contradicts AE. Thus

\[
                               \xi\ge\gamma b.                  \tag{11}
\]

This argument uses neither a D2 surrogate nor a circle equation at E.

## 6. The entire D-owned DE upper-side case is excluded

Suppose equality holds in (11). Put
\(\Gamma=\gamma a+\eta>0\). The E vector is \(\Gamma v\), so its
original application has D coordinates \((\tau,1)\), with the
complete possible side-mean range \(0\le\tau\le1\).

Take the full D torque equation about its actual H point P. The H
force contributes zero, the C force at (1,0) contributes \(-\eta\),
and the E force contributes \(\tau\Gamma\). Hence

\[
                    \tau=\frac{\eta}{\Gamma},\qquad
                    1-\tau=\frac{\gamma a}{\Gamma}.             \tag{12}
\]

In particular \(0<\tau<1\); this is a consequence of the complete
equation, not a point-contact assumption.

The actual DE mean has world height \(1+a+\tau b\). The unit E is
supported there with minimum normal \(v=(-b,a)\). Apply (4) with
e=South, for which \(v\cdot e=-a\). It gives the whole-unit bound

\[
 \min_E y\ge1+a+\tau b-b
          =1+a\left(1-\frac{\gamma b}{\Gamma}\right).             \tag{13}
\]

It remains to prove \(\Gamma>\gamma b\) for each original HC type.

### 6.1. Northeast HC

Here the actual point \(S=(1,1)\) belongs to C. In world coordinates
the CD vector in (9), with \(\xi=\gamma b\), is

\[
                  m=(b\Gamma,\gamma b^2-\eta a).
\]

Its minimum support on C is the actual point \(P+u\). Therefore

\[
\begin{aligned}
0&\le m\cdot(S-(P+u))\\
 &=b\,[q\Gamma-\gamma].
\end{aligned}
\]

Thus \(\Gamma\ge\gamma/q>\gamma>\gamma b\).

### 6.2. East HC

The whole C lies in \(x\ge1\), so \((P+u)_x\ge1\). Its original HC
point \(S=(1,s)\), \(0\le s\le1\), lies strictly below \(P+u\).
The CD vector has positive x component \(b\Gamma\). Since its
minimum on C is at \(P+u\), the inequality
\(m\cdot(S-(P+u))\ge0\) forces its y component to be nonpositive:

\[
                   \gamma b^2-\eta a\le0.
\]

Consequently

\[
                  \Gamma=\gamma a+\eta
                    \ge\frac{\gamma}{a}>\gamma b,
\]

where \(ab<1\). This includes equality in the preceding y-component
inequality and every original HC side mean.

In both cases (13) gives \(\min_E y>1\), contradicting the real AE
contact. Thus the entire DE upper-side case, including every shared
mean and every external owner, is excluded.

## 7. The precise remaining opposite-vertex equations

We have proved \(\xi>\gamma b\). Therefore (10) strictly exposes
the left D vertex \(P+v\), and DE is a physical singleton there.
Take the unchanged full D moment equation about P:

\[
                 -\eta-(\gamma b-\xi)=0.
\]

It follows that \(\xi=\eta+\gamma b\), proving (2)--(3).

For use in the still-open residual, define the world components

\[
\begin{aligned}
 X&=\eta(a+b)+\gamma ab>0,\\
 Y_C&=\eta(b-a)+\gamma b^2,\\
 Y_E&=\eta(a-b)+\gamma a^2.
\end{aligned}
\]

Then the original C and E vectors from D are respectively
\((X,Y_C)\) and \((-X,Y_E)\), with \(Y_C+Y_E=\gamma\).

If HC is northeast, its actual point S=(1,1) gives the exact further
necessary inequality

\[
                         (1-p)X\ge\eta+\gamma b.                 \tag{14}
\]

If HC is East, the same actual point-versus-support comparison as
in Section 6.2 gives

\[
                   Y_C\le0,\qquad
                   a>b,\qquad
                   \eta\ge\frac{\gamma b^2}{a-b}.               \tag{15}
\]

The middle conclusion follows because \(\gamma b^2>0\). No strict
inequality is claimed at the last step: the complete equality
endpoint remains.

These are necessary physical and full-moment statements only. In
particular E's genuinely loaded two-force equation, the full original
H4 equation, all other bodies and all nine-square circle and pocket
obligations remain available and unchanged. The original H-owned
interface has not yet been closed.

## 8. Literal inputs and bookkeeping limit

| Operative input | SHA256 |
| --- | --- |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 |
| INNER_PENTAGON_FOUR_SPOKE_OWNED_UNLOADED_END_OPPOSITE_HORIZONTAL_SIGNS.md | 8a938f2d49f6307fbf2a21630d419693e675e2c5103b75a949cb0abaf6ceee09 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 |

The last source supplies the literal original-family scope only. Its
long-port or radius hypotheses are not needed for this stronger local
necessary-domain conclusion. The recovered older source pins remain
unchanged and their accepted current-dependency adoption records remain
operative. There is no new selector, truncation of a positive star,
replacement of a mean, numerical pose, Lean compilation or CI premise.
This source earns no original fine-family, graph-parent or coarse-cell
closure credit.

