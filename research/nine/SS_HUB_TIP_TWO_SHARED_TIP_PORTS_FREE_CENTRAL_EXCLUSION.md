# Two shared ports at the S tip exclude a free central diamond contact

Date: October 26, 2026.

**Status: complete hand candidate, pending fresh independent review.**
The argument includes a degree-free geometric lemma for a fourth unit
next to three units in an L and a continuous disk-containment rigidity
lemma. Their original join excludes the whole S/S hub-tip feature
with HB and BK genuinely shared and HK free. It does not assume a
physical circle mask or contact owner at C.

## 1. Original scope and theorem

Retain the original positive component
\[
 HK,\ HB,\ HC,\ KB,\ KC,\ HL_H,\ BL_B,
\]
with genuine radial S leaves at H,B, positive circle loads at K,C,
true pair degrees H4,K3,B3,C2, and all three arbitrary completion
units. Work throughout
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \delta=\max(d-1,0)<1/60.
 \tag{1}
\]

**Theorem 1.1.** If the physical HB and BK intersections have positive
length, the actual HK contact cannot be a free vertex/vertex singleton.

All actual means on the two shared sides are retained. C's physical
circle mask and both of its contact types remain arbitrary until the
geometric containment argument determines them. No K3 equation is
replaced by a two-force equation.

## 2. A fourth unit next to an exact three-unit L

**Lemma 2.1 (missing quadrant).** Put
\[
 S=[-1,0]\times[-1,0],\quad
 E=[0,1]\times[-1,0],\quad
 N=[0,1]\times[0,1].
 \tag{2}
\]
If a fourth unit square T has disjoint open interior from S,E,N
and physically touches both S and N, then
\[
 \min_T y=0,\qquad \max_T x=0,\qquad
                      T\subseteq\{x\le0,\ y\ge0\}.
 \tag{3}
\]
There is no disk, circle-load or force premise.

**Proof.** Inspect an actual contact of T with S. A contact in the
relative interior of S's left side puts T in x<=-1, so T cannot
touch N. The bottom-side interior similarly puts T in y<=-1.
A right-side interior point already has S and E on opposite sides
and cannot belong to a third interior-disjoint square. A top-side
interior contact puts T in y>=0.

At either left corner, first consider the possibility that the S
corner lies in the relative interior of a T side. Its common inward
normal into T has nonpositive horizontal component. Along the actual
unit side through the contact, the possible horizontal increase is
strictly less than one, since the contact is side-interior; the
inward normal span cannot increase the horizontal coordinate.
Therefore max_T x<0, and T cannot reach N. A contact cannot be in
T's open interior, so only a T vertex remains at either left corner.

At the bottom-left corner with T vertex contact, the inward
right-angle sector of T must avoid the northeast inward quadrant of
S. Every such right-angle sector lies wholly in either the western
half-plane or the southern half-plane. Thus T is again in x<=-1 or
y<=-1 and cannot touch N.
At the bottom-right corner, the inward sectors of S and E fill
the northern half-plane; T must lie in y<=-1 and cannot reach N.
At the top-left corner with T vertex contact, its inward quadrant must be wholly west
of x=-1 or north of y=0; the west option cannot reach N.
At the common point O of all three original units, their inward
quadrants fill southwest, southeast and northeast. Any T containing
that point must have its whole inward quadrant in northwest.

For the elementary quadrant fact just used, a right-angle sector
avoiding the open southeast quadrant has its starting angle in
[0,pi], so it is either wholly north or wholly west. Rotation gives
the other corner versions. Since a convex square is contained in
the tangent sector or half-plane at any one of its points, these
local statements are whole-square statements.

The cases exhaust S's boundary and prove T is wholly in y>=0.
Its contact with S consequently gives min_T y=0 and a lowest
point with x in [-1,0].

If T is axis-parallel and max_T x>0, its horizontal interval meets
(0,1), while its vertical interval is [0,1], producing an interior
overlap with N. If T is not axis-parallel, its unique lowest vertex
is (a,0), -1<=a<=0. Its two inward side directions have positive
vertical coordinates and opposite horizontal signs. The edge to
its rightmost vertex has positive horizontal direction and vertical
increment strictly between zero and one. If max_T x>0, an interior
portion of that edge lies in 0<x<1,0<y<1. A small movement into T
then gives interior overlap with N. Thus max_T x<=0 in every frame.

Finally T touches N, whose x-coordinates are nonnegative, so max_T x
must equal zero. This proves (3). \(\square\)

The lemma allows T to touch the original units at shared faces,
side-interior singletons or vertex singletons. It chooses no normal.

## 3. Disk containment makes the missing-quadrant unit rigid

**Lemma 3.1.** Let t>=0 satisfy
\[
                       2t<1+1/\sqrt2.
 \tag{4}
\]
Suppose a unit square T satisfies
\[
  \min_T y=t,\qquad \max_T x=0,\qquad
  T\subseteq D_R,\qquad R^2\le1+(t+1)^2.
 \tag{5}
\]
Then
\[
                         T=[-1,0]\times[t,t+1].
 \tag{6}
\]
In particular, under (5) any tilted frame is impossible.

**Proof.** The axis-parallel case gives (6) directly. In any other
frame, label the positive side-coordinate magnitudes c>=s>0,
c^2+s^2=1. Up to square symmetries there are two possible sets
of vertices relative to P=(0,t):
\[
 \begin{array}{c|cccc}
 {\rm I}&(-s,0)&(-c-s,s)&(0,c)&(-c,c+s)\\
 {\rm II}&(-c,0)&(-c-s,c)&(0,s)&(-s,c+s).
 \end{array}
 \tag{7}
\]
These describe both signs of tilt, including c=s. Each comes from
the unique lowest vertex and the two inward upward side directions;
the condition max x=0 fixes its horizontal translation.

In case I, the top corner has squared-norm excess over
1+(t+1)^2 equal to
\[
 c^2+(t+c+s)^2-[1+(t+1)^2]
              =2cs-s^2+2t(c+s-1)>0.
 \tag{8}
\]
Here 2c>s, s>0, c+s>1 and t>=0.

In case II, use the left corner. Its squared-norm excess is
\[
 (c+s)^2+(t+c)^2-[1+(t+1)^2]
                   =2cs-s^2-2t(1-c).
 \tag{9}
\]
Since 1-c=s^2/(1+c) and c>=s,
\[
 2cs-s^2-2t(1-c)
 \ge s^2\left(1-\frac{2t}{1+c}\right)>0.
 \tag{10}
\]
The final strict inequality follows from c>=1/sqrt2 and (4).
Both tilted cases have a corner outside D_R, contradicting (5).
This proves the lemma continuously in the entire orientation range.
\(\square\)

## 4. Two real shared B ports and a free HK force an exact L

Assume the original feature in Theorem 1.1. Shared HB and BK make
the frames of H,B,K parallel. Their normals at B are side axes.

If the two normals are opposite, H and K are beyond opposite sides
of B and cannot touch each other. If they are equal, H,K lie in the
same parallel column next to one B side. For them to touch without
overlap their longitudinal translations differ by exactly one.
Their mutual contact is then a full shared side, not a free singleton.
Thus a free HK leaves only perpendicular B port normals.

Rotate and reflect so B-to-H is -E_1 and B-to-K is E_2. Write
B=[h,h+1]x[q,q+1]. Before using HK's actual contact type, its
neighbors have the parallel shared-side forms
\[
 \begin{aligned}
 H&=[h-1,h]\times[q+\eta,q+\eta+1],\\
 K&=[h+\zeta,h+\zeta+1]\times[q+1,q+2],
                  \qquad -1<\eta,\zeta<1.
 \end{aligned}
\]
Physical HK contact requires eta>=0 and zeta<=0. If eta>0 and
zeta<0, their interiors overlap. If exactly one is zero, their
intersection is a positive-length shared side. A free singleton
therefore forces eta=zeta=0. The real units are exactly
\[
 \begin{aligned}
 H&=[h-1,h]\times[q,q+1],\\
 B&=[h,h+1]\times[q,q+1],\\
 K&=[h,h+1]\times[q+1,q+2].
 \end{aligned}
 \tag{11}
\]
Their common point is P=(h,q+1). No aggregate mean has been set
equal to P. The actual strict H-to-K normal has both coordinates
strictly positive because the two actual vertex cones meet in the
open northeast quadrant.

Lemma 2.1 applied to the actual fourth unit C now gives
\[
 C\subseteq\{x\le h,\ y\ge q+1\},\qquad
             \max_Cx=h,\quad \min_Cy=q+1.
 \tag{12}
\]
This used only physical nonoverlap and the original HC,KC contacts.
In particular every actual H-to-C common normal has nonnegative
vertical component: its application is on H's top side, including
either top corner and every possible shared mean.

## 5. The complete B3 equation fixes its leaf and retains d=1

The strict d<1 interval of this original layout is already excluded
by the accepted distinct-root common-boundary-neighbor theorem.
Retain d>=1. Each genuine S root contains its actual inward-segment
point (d-1)e, so both H and B meet D_delta. Their real shared
separation line x=h therefore satisfies
\[
                              |h|\le\delta.
 \tag{13}
\]

The unchanged B3 force equation is
\[
               \lambda_B e_B-\mu_{BH}E_1+\mu_{BK}E_2=0,
                    \qquad \lambda_B,\mu_{BH},\mu_{BK}>0.
\]
Thus (e_B)_x>0 and (e_B)_y<0. The actual genuine leaf support is
the strictly exposed lower-right vertex of B:
\[
              p_{L_B}=(h+1,q),\qquad
              q<0,\qquad (h+1)^2+q^2=d^2.
 \tag{14}
\]
This is not a chosen side mean. On d=1, (13) gives h=0 and (14)
would give q=0, contradicting q<0. Hence this entire feature has
d>1. Throughout it,
\[
 q^2\le(1+\delta)^2-(1-\delta)^2=4\delta<1/15,
                 \qquad -4/15<q<0.
 \tag{15}
\]

## 6. The genuine H4 equation removes the aligned H leaf

The actual H-owned HB side meets the near-origin root B, and the
physical H/B/K triangle has boundary unit K. The reviewed
arbitrary-degree owner-direction theorem
S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md applies at
the real H4 and gives
\[
                              (e_H)_x<0.
 \tag{16}
\]
Its proof is physical and retains every actual H force.

The genuine H leaf is therefore one of the left upper or left lower
vertices of (11), or is aligned in direction -E_1 with its full
actual side mean. These exhaust H's actual frame.

If it were the upper-left vertex, comparison with (14) would give
\[
                         4h=2q+1.
\]
But 4h<=4delta<1/15, whereas (15) gives 2q+1>7/15.
Thus this complete feature is impossible.

If the H leaf were aligned in direction -E_1, its vertical force
component would be zero. The actual HB force also has zero vertical
component. The genuine HK force has strictly positive vertical
component by the strict free normal in Section 4. The genuine HC
force has nonnegative vertical component by (12). The vertical
component of the full H4 force sum is therefore strictly positive,
a contradiction.

The only remaining H leaf is its lower-left vertex. Comparing its
actual norm with (14) gives
\[
             (h-1)^2+q^2=(h+1)^2+q^2,\qquad h=0.
\]
Consequently
\[
 \begin{aligned}
 H&=[-1,0]\times[q,q+1],&
 B&=[0,1]\times[q,q+1],\\
 K&=[0,1]\times[q+1,q+2],&
 p_{L_H}&=(-1,q),\quad p_{L_B}=(1,q),\\
                         d^2&=1+q^2.
 \end{aligned}
 \tag{17}
\]
Every shared mean is still arbitrary. The only force projection used
at H was its real four-edge equation.

## 7. The actual loaded K fixes the containing-circle level

Put t=q+1. Equation (15) gives t>11/15>0. The physical K in (17)
has exactly one farthest corner, (1,t+1). Since its actual positive
circle load requires K to touch the containing circle,
\[
                           R^2=1+(t+1)^2.
 \tag{18}
\]
This follows from its obtained physical coordinates, without a mask
assumption or any K force equation.

Use d^2=1+q^2 and R^2=(d+1)^2+1/4. Expanding (18) gives
\[
                  4q=2d-\frac{11}{4},\qquad
                  q=\frac d2-\frac{11}{16}.
\]
Therefore d<61/60 implies
\[
                q<-43/240,\qquad
           0<t<197/240,\qquad
           2t<197/120<17/10<1+1/\sqrt2.
 \tag{19}
\]
The last strict comparison uses 1/sqrt2>7/10. Its purely rational
preceding reserve is 17/10-197/120=7/120.

The actual C obeys max_C x=0,min_C y=t by (12). Equations
(18)--(19) meet every hypothesis of Lemma 3.1. Hence
\[
                          C=[-1,0]\times[t,t+1].
 \tag{20}
\]
In particular any oblique C physical frame, with either circle mask
and any original HC/KC owners, has been excluded continuously.

## 8. Exact join to the reviewed shared-perimeter exclusion

Equations (17), (20) make all four actual outer diamond intersections
HB,BK,KC,CH full shared sides. Their actual positive aggregate means
are still their original means, not endpoints or midpoints.

The reviewed
SS_HUB_TIP_DIAMOND_SHARED_PERIMETER_EXCLUSION.md excludes this
entire original four-shared-perimeter feature with true H4,K3,B3,C2.
It retains the real central HK force, all means and the matched
junction choice. It uses the one previously fixed common selection,
which is unchanged here.

This final full-feature theorem contradicts the obtained physical
layout and completes Theorem 1.1. No C2 equation was applied at K,
no extra force at H was deleted, and no new generic normal choice
was made. The proof derives the four-shared physical feature before
invoking its exact complete exclusion.

## 9. Exact inputs and limitations

| Source | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Actual genuine S-leaf supports and inward segments |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd | Entire original hub-tip lower-domain exit |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | Actual arbitrary-degree H-owned HB leaf-direction consequence |
| SS_HUB_TIP_DIAMOND_SHARED_PERIMETER_EXCLUSION.md | d7e7cafe4b9dd636bbbef1e0857e3dda1605404a382c27623ca26d3f707dc4b2 | Whole resulting four-shared feature, with all real forces |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Strict actual free vertex normals and shared/singleton distinction |

Original accepted files are compared with head
26d9e3042b733ff0796876a4607a7d834f4b630a. The owner-direction
theorem has fresh independent review
ef11ab0d9e3adb0a574924bafd6b2ef4d296fbeeb17665fc478dbd127db860b8.
The shared-perimeter theorem has fresh independent review
fe0b4eeb89b9d78a926215c948ff48596139ea710e555ac1369bb8ea2fd24588.

The degree-free Lemmas 2.1 and 3.1 may be reused separately at their
stated physical scopes. The original join excludes only the complete
feature HB/BK shared and HK free. The remaining central owners and
other perimeter feature patterns stay under the same original gate.
No whole-gate tick, new graph ID, pose sample, computational
certificate, ledger edit, Lean run, CI workflow or remote mutation
is introduced.
