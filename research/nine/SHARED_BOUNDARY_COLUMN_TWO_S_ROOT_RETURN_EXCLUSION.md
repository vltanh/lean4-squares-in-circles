# Two stacked boundary units forbid a return through two genuine S roots

Date: October 26, 2026.

**Status: complete reusable hand candidate, pending fresh full
independent review.** The theorem excludes an entire shared-column
feature with arbitrary degrees at its two boundary units. It uses
the full original H4 and B3 equations in the diamond application,
and does not select or replace a contact mean.

## 1. Exact local and original scope

Work in the original radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad
 \frac9{10}<d<\frac{61}{60}.
 \tag{1}
\]

The local theorem below uses d>=1. Let H,B be distinct actual
genuine S-leaf roots, with their whole radial leaves retained.
Let K,C be actual physically circle-touching units. All these
units and the two leaves are distinct and interior-disjoint.

Suppose H,K,C have positive-length shared contacts HK,HC,KC
and the two actual normals H-to-K and H-to-C are parallel.
Require the actual physical contacts HB and BK. At B require
exactly the three positive pair forces to H,K and its genuine
S leaf. At H retain its genuine S-leaf force, its positive HB
force, and all remaining positive pair forces, which must point
in the common direction from H toward K,C. Their complete sum
is positive. H has no circle force, as follows already from its
genuine S-leaf root geometry. The actual degrees, forces and
circle masks of K,C are otherwise arbitrary.

**Theorem 1.1.** These hypotheses are impossible.

In the original SS hub-tip diamond, the actual component is

\[
 HK,\ HB,\ HC,\ BK,\ CK,\ HL_H,\ BL_B,
 \tag{2}
\]

with true degrees H4,K3,B3,C2, positive loads at K,C and three
arbitrary completion units. The theorem applies to the entire
feature in which HC,CK,HK are genuinely shared and the parallel
pair in that triangle is at H. No BK or HB side-owner premise
is imposed; all actual selected normals are covered.

The complete original d<1 interval is already excluded by
DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md. The proof below
retains d=1 until it derives a strict contradiction at that wall.

## 2. Two boundary units fix the whole column geometry

Two coframed units on opposite parallel supports of H cannot
touch each other. Thus the two parallel H normals have the same
sign. Rotate the common frame so both point left. The K,C
intervals have identical horizontal projections; positive shared
KC then makes them exactly stacked. Reflect vertically so K
is the upper member. Write the whole units as

\[
 \begin{aligned}
 H&=[h,h+1]\times[t-1,t],\\
 K&=[h-1,h]\times[T-1,T],\\
 C&=[h-1,h]\times[T-2,T-1].
 \end{aligned}
 \tag{3}
\]

The genuine S-leaf inward segment puts an actual point of H
within radius delta=d-1. Hence h<=delta<1/60. The common
horizontal center coordinate of K,C is h-1/2<0, so their
farthest horizontal coordinate is h-1.

Because both actual units touch the same circle, their farthest
vertical coordinate magnitudes are equal:

\[
 \left|T-\frac12\right|+\frac12
   =\left|T-\frac32\right|+\frac12.
\]

This gives T=1. Thus

\[
 K=[h-1,h]\times[0,1],\qquad
 C=[h-1,h]\times[-1,0],\qquad
 R^2=(h-1)^2+1.
 \tag{4}
\]

Both physical circle masks are now unique, as a consequence of
their nonzero horizontal and vertical center coordinates. No
individual circle weight assumption was used.

Put

\[
 a=\sqrt{R^2-1}=1-h,\qquad X=h+1=2-a.
\]

Since d>=1 and R^2<=1105/256,

\[
 a^2\ge\frac{13}{4}>\left(\frac95\right)^2,\qquad
 a^2\le\frac{849}{256}<\left(\frac{11}{6}\right)^2.
\]

Consequently

\[
 -\frac56<h<-\frac45,\qquad
 \frac16<X<\frac15.
 \tag{5}
\]

The two original positive shared lengths in (3) give

\[
                              0<t<1.
 \tag{6}
\]

All original shared means are still arbitrary actual means in
their actual intersections.

## 3. The complete HB interface is forced upward

Let n be the actual H-to-B normal. The actual physical triangle
H,K,B and the H-owned HK normal -e_x permit the degree-free
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. It gives

\[
                              n_x\le0.
 \tag{7}
\]

No strict negative x component is possible. If n_y>0, its support
application on H is (h,t), in the relative interior of K's right
side. If n_y<0, it is (h,t-1), in the relative interior of C's
right side. In either case the actual inward unit segment of B
in direction n immediately enters the open interior of that
fixed column unit, contradicting disjointness.

If n=-e_x, its actual application lies on H's left side, with
height between t-1 and t. Away from height zero the same local
argument enters K or C. At height zero, K and C fill the local
left half-plane while H fills the local right half-plane; no
fourth unit can have interior points arbitrarily near that
application. This includes every actual shared mean endpoint.

Thus n_x=0. The downward alternative would give
max_B y=t-1<0, preventing B from touching K, whose minimum
height is zero. Hence the only actual normal is

\[
                 n_{HB}=e_y,\qquad \min_B y=t.
 \tag{8}
\]

The genuine S-root near-origin point of B now gives

\[
                      0<t\le\delta<\frac1{60}.
 \tag{9}
\]

In particular d=1 is impossible. No separate equality-radius
assumption was made.

Let lambda_H e_H be H's genuine leaf force, and let M>0 be the
complete aggregate of all its actual leftward pair magnitudes.
Its full unchanged force equation is

\[
                  \lambda_H e_H-M e_x+\mu e_y=0,
                         \qquad \lambda_H,M,\mu>0.
\]

Thus its genuine leaf direction is strictly southeast. Its
actual support point on H is therefore its lower-right vertex:

\[
                 p_H=(X,t-1),\qquad
                 d^2=X^2+(1-t)^2.
 \tag{10}
\]

This is the full H4 equation in (2), with M=mu_HK+mu_HC.
No false degree-three equation has been used at H.

## 4. Every possible actual BK normal

Let m be the actual K-to-B normal. No point of B can lie on
K's left side x=h-1=-a. Indeed B contains an actual point q
with |q|<=delta, whereas for such a point P,

\[
 |P-q|\ge a-\delta>\frac95-\frac1{60}
      =\frac{107}{60}>\sqrt2,
\]

exceeding the diameter of B. This rules out the entire left
side and both left corners, regardless of their force status.

A downward K normal would give max_B y=0, contrary to (9).
An upward K normal would give min_B y=1, also contrary to (9).
The lower-right K vertex has height zero and cannot belong to B.

Consequently the full actual support-normal cover is exactly

\[
 \begin{array}{ll}
 \text{(i)}&m=e_x,\quad \min_B x=h;\\
 \text{(ii)}&m_x,m_y>0,\quad
          P_{BK}=(h,1).
 \end{array}
 \tag{11}
\]

Case (ii) includes every free BK normal and every B-owned-only
normal; no finite normal avoidance or prescribed owner was used.

## 5. The entire strict northeast BK cone violates the real B moment

Suppose (ii). If B is axis-parallel, its strict northeast minimum
is its lower-left vertex, at height t rather than one. Hence B
must be tilted. Use its complete actual lowest-vertex chart

\[
 B=Q+[0,1]v+[0,1]w,\qquad
 v=(-c,s),\quad w=(s,c),\quad
 c,s>0,\quad c^2+s^2=1,\quad Q_y=t.
 \tag{12}
\]

No ordering of c,s is imposed. Since m_x,m_y>0,

\[
                            m\cdot w>0.
\]

Every actual minimum-m support point therefore lies on the
segment Q+[0,1]v, including its two endpoints. Write the actual
point P=(h,1) as Q+xi v, with 0<=xi<=1. Then

\[
 1-t=\xi s,\qquad Q_x=h+\xi c,\qquad
 s\ge1-t.
\]

The complete slider interval (9) implies

\[
 c^2=1-s^2\le2t-t^2<\frac1{30}<\frac1{25},
 \qquad c<\frac15,\qquad Q_x<-\frac35.
 \tag{13}
\]

The actual HB force on B points down and acts at its unique
lowest vertex Q. Its BK force points in direction -m at P.
Its genuine radial S-leaf force has zero origin moment. Thus
the unmodified true B3 moment equation is

\[
                 \mu_{HB}Q_x+\mu_{BK}\det(P,m)=0.
 \tag{14}
\]

But Q_x<0 and

\[
                     \det(P,m)=h m_y-m_x<0.
\]

Both real magnitudes are positive, so (14) is impossible.
This excludes the whole closed physical application range
0<=xi<=1, including either endpoint and a side-interior
B-owned mean. Therefore only case (i) of (11) remains.

## 6. Axis-parallel B and the entire strict leaf-vertex cover

Now B has actual minima x=h and y=t. Its pair forces point
left and down, so its genuine leaf direction has two strictly
positive components.

If B is axis-parallel,

\[
                         B=[h,h+1]\times[t,t+1].
\]

Its genuine leaf point is (X,t+1), whose squared norm exceeds
the actual H leaf norm (10) by 4t>0. Thus this frame is impossible.

For a tilted B, retain the full chart

\[
 Q=(h+c,t),\quad P=(h,t+s),\quad
 B=Q+[0,1](-c,s)+[0,1](s,c),\quad c,s>0.
 \tag{15}
\]

Its actual HB and BK applications are respectively Q and P.
The unchanged moment gives

\[
 \frac{\mu_{BK}}{\mu_{HB}}
      =\frac{h+c}{t+s}>0.
 \tag{16}
\]

Therefore c>-h>4/5, whence s<3/5. Since the leaf direction
is strictly northeast, its dot product with w=(s,c) is positive.
Its support is therefore either the right vertex

\[
                   R_B=(h+c+s,t+c),
\]

the upper vertex

\[
                   U_B=(h+s,t+c+s),
\]

or the intervening side with outward normal w. These are the
complete strict-vertex and aligned-leaf alternatives.

The upper vertex is impossible immediately:

\[
                       (U_B)_x=h+s<-\frac15,
\]

whereas a genuine radial leaf point in this direction has positive
x coordinate.

If the leaf point is the right vertex R_B, radiality and (16)
give the exact determinant identity

\[
 (h+c)(c-s)=s(t+s),\qquad
 \frac{\mu_{BK}}{\mu_{HB}}=\frac{s}{c-s},\qquad c>s.
 \tag{17}
\]

Since h+c<1/5 and t+s>s,

\[
 \frac{s}{1-s}\le\frac{s}{c-s}<\frac1{5s}.
\]

Thus 5s^2+s<1, implying s<3/8; at 3/8 the left side is
69/64>1. Consequently c>9/10.

Set eta=1-c and k=c+s-1=s-eta>0. The exact difference between
the two genuine leaf squared radii is

\[
 \begin{aligned}
 |R_B|^2-|p_H|^2
   &=2Xk+k^2+2t(c+1)-s^2\\
   &=2X(s-\eta)+\eta^2-2s\eta+2t(c+1).
 \end{aligned}
\]

Using X>1/6, t>0 and eta=s^2/(1+c)<10s^2/19 gives

\[
 \begin{aligned}
 |R_B|^2-|p_H|^2
 &>\frac{s}{3}-\left(\frac13+2s\right)\eta\\
 &>\frac{s}{3}-\frac{65}{114}s^2\\
 &>\frac{109}{912}s>0.
 \end{aligned}
 \tag{18}
\]

This contradicts the equal genuine radius d of the two leaf
applications. It covers the entire surviving continuous interval
0<s<3/8.

## 7. The aligned B-leaf side and every application endpoint

The only remaining possibility is that the B leaf direction is
w=(s,c). Its genuine application p_B=d w may initially be
any actual point of the exposed side between R_B and U_B.
No midpoint or endpoint on the root side is prescribed.

Its true force direction and moment equation (16) give

\[
                 c(h+c)=s(t+s).
 \tag{19}
\]

The actual support height of that side in direction w is

\[
                   d=1+s(h+c)+tc.
\]

Substitution of (19) gives

\[
                    \delta=d-1=\frac{t+s^3}{c}.
 \tag{20}
\]

Because delta<1/60 and t>0, this forces t<1/60 and
s^3<1/60. Since (4/15)^3>1/60, we have s<4/15. Expanding
(19) now yields

\[
 ch=st+2s^2-1
    <\frac1{225}+\frac{32}{225}-1
    =-\frac{64}{75}.
\]

As 0<c<1 and the right side is negative,

\[
                         h<-\frac{64}{75}<-\frac56,
\]

contradicting (5). This argument retains the entire actual leaf
side, including its endpoints. There is no other positive-quadrant
side normal of a tilted square.

All alternatives for the genuine B leaf have been exhausted,
proving Theorem 1.1.

## 8. Exact original join and reusable force scope

For the original SS hub-tip diamond, assume HC,CK,HK are shared
with the parallel pair at H. Their common side frame supplies
(3). K,C are physically circle-touching by their original positive
loads. H and B have their original genuine S leaves. The actual
H4 equation has precisely its leaf, its HB force and its two
leftward HK/HC forces. The actual B3 equation has precisely its
leaf and its HB/BK forces. Every hypothesis of the theorem therefore
holds.

The accepted strict d<1 exit handles the complete lower interval;
(9) independently excludes d=1 in the remaining column feature.
Thus this entire original physical feature is impossible over the
full radius window.

The local result is stronger in several directions: it allows
arbitrary positive degrees and circle weights at K,C, never uses
their force or moment equations, covers all actual HB/BK normals,
and permits any number of real parallel leftward H forces when
their complete aggregate is retained. It needs the exact B3
equation and the stated full force-direction cover at H; an
additional H force in another direction cannot be deleted.

The other parallel location in the shared boundary triangle,
at K, is not claimed here. Nor does this source prove that every
original owner feature is shared or close the whole SS gate.

## 9. Exact inputs

| Input | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine S-leaf radial applications, near-origin root points, full inward support segment and origin moments |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual HB normal has nonnegative dot product with the H-owned HK side normal |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd | Entire original strict d<1 hub-tip exit |

The elementary circle comparisons, entire tilted-frame cover
and all scalar estimates are given in the source itself. The
original accepted comparison head is
26d9e3042b733ff0796876a4607a7d834f4b630a.

No fixed means, sampled orientations, post-extraction normal
changes, force deletions, computational coefficient packets,
graph IDs, ledger edits, Lean invocation, CI workflow or remote
mutation are used.
