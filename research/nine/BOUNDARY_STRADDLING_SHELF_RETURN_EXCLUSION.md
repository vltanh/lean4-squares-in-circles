# A boundary unit straddling a two-unit shelf leaves no returning unit

Date: October 26, 2026.

**Status: complete reusable hand candidate, pending fresh independent
review.** The main theorem is purely physical: it excludes any fourth
contained unit touching the left shelf unit and the straddling boundary
unit. No force, positive degree or boundary mask at the proposed fourth
unit is needed. Its exact original join removes a whole three-shared
triangle feature of the S/S hub-tip diamond.

## 1. Exact shelf and geometric statement

Let
\[
 \begin{aligned}
 H&=[-1,0]\times[t-1,t],\\
 B&=[0,1]\times[t-1,t],\\
 K&=[k,k+1]\times[t,t+1],
 \end{aligned}
 \qquad -1<k<0,\quad 0\le t\le1.
 \tag{1}
\]
Assume these physical units are contained in D_R and K touches the
containing circle. Its actual farthest corner gives
\[
 R^2=m^2+(t+1)^2,\qquad
 m=\max(-k,k+1)<1.
 \tag{2}
\]
Both possible far horizontal coordinates and the tied case k=-1/2
are included.

**Theorem 1.1.** No fourth unit T contained in D_R, with open
interior disjoint from H,B,K, can physically touch both H and K.

The theorem retains every contact type, every tilted frame and
every position on a shared face. It requires no circle contact at T.

## 2. Complete routing at the shelf unit

First ignore containment in D_R and inspect any actual H/T contact
for a unit T touching K and avoiding all three original interiors.

A contact in H's left-side interior puts all of T in x<=-1,
which cannot reach K since k>-1. A contact in H's bottom-side
interior puts T in y<=t-1, below K. A contact in H's right-side
interior is impossible because H and B already occupy opposite
local half-planes there.

At the lower-left corner, if T has a vertex, its inward quadrant
must avoid H's northeast inward quadrant. It lies wholly west
of x=-1 or below y=t-1, and cannot reach K. If the point is in
the interior of a T side, the inward side normal into T has
nonpositive vertical component. The upward distance along either
portion of the actual unit side is strictly less than one; the
inward normal span cannot increase height. Thus max_T y<t,
again below K. The point cannot lie in T's open interior.

At the lower-right corner, H and B fill the northern tangent
half-plane, so T lies wholly below y=t-1 and cannot reach K.
At the upper-right corner (0,t), H and B fill the southern
half-plane while K fills the northern half-plane, since
k<0<k+1. A fourth unit cannot contain that point.

At the upper-left point
\[
                               P=(-1,t),
 \tag{3}
\]
a vertex of T has an inward quadrant either wholly west of x=-1
or wholly above y=t. The west alternative cannot reach K.
The remaining possibility there is a side-interior point of T.
Its inward unit side normal has the full form
\[
                         n=(-a,b),\quad
                    a,b\ge0,\quad a^2+b^2=1.
 \tag{4}
\]
These include the two limiting side axes; no arbitrary normal
is substituted for a physical side owner.

Finally an H top-side interior contact puts T wholly above y=t.
This exhaustive boundary cover proves that every potential T
has one of two forms:

* T lies wholly in y>=t and has min_T y=t; or
* the actual point P in (3) is on a T side, with the actual inward
  unit side axis (4).

Before any radius estimate, the same cover also proves that every
possible H/T application lies on H's top edge, including its
upper-left corner. Therefore every actual H-to-T common normal
has nonnegative vertical component. This routing consequence holds
for all real translations of the shelf, independently of R,t.

For the quadrant statement used above, a right-angle sector avoiding
an open coordinate quadrant is contained in one of the two opposite
closed coordinate half-planes. For a side-interior point the separate
unit-side argument was used instead; a half-plane tangent cone was
not replaced by a quadrant.

## 3. Every unit above the shelf exceeds the actual radius

Suppose the first form holds. T has a lowest point on H's top
edge, with horizontal coordinate at most zero, which is strictly
less than k+1.

If T is axis-parallel and max_T x>k, its horizontal interval
overlaps (k,k+1) and its vertical interval [t,t+1] overlaps K.
If T is tilted, its unique lowest vertex has one inward side
leading to its rightmost vertex. That edge has positive horizontal
increment and vertical increment strictly between zero and one.
If max_T x>k, an interior part of this edge has
k<x<k+1 and t<y<t+1, again giving interior overlap with K
after a small movement into T.

Thus max_T x<=k. Physical contact with K requires the reverse
inequality, so the actual supports are
\[
                         \max_T x=k,\qquad \min_T y=t.
\]
The coordinate-minimum interior-point theorem, reflected in x,
puts the actual point
\[
                              (k-1,t+1)\in T.
 \tag{5}
\]
But 1-k>max(-k,k+1)=m for every -1<k<0. Hence
\[
                     (k-1)^2+(t+1)^2
                            >m^2+(t+1)^2=R^2.
\]
This contradicts containment, including all axis-parallel and
tilted frames. No chosen physical vertex is needed in (5).

## 4. The remaining side contact also exceeds the radius

Now let P=(-1,t) lie on the actual T side with inward unit axis
n=(-a,b) from (4). The opposite-side point
\[
                               P+n\in T
\]
is actual: a square has width one in its own side-normal direction,
and translating any point of one side by that inward unit axis
reaches the opposite side at the same transverse coordinate.
This includes side endpoints as well as interior positions.

Its squared norm is
\[
                   |P+n|^2=t^2+2+2(a+tb).
 \tag{6}
\]
Since a,b>=0 and a^2+b^2=1, a+b>=1. With 0<=t<=1,
\[
                 a+tb-t=a-t(1-b)
                    \ge a-(1-b)=a+b-1\ge0.
\]
Consequently
\[
 |P+n|^2\ge t^2+2+2t
             =1+(t+1)^2
             >m^2+(t+1)^2=R^2.
 \tag{7}
\]
The strict final gap uses m<1, not strictness in the side-axis
or t inequalities. Thus a=0, b=0, t=0 and t=1 walls are all
retained when compatible with the hypotheses.

Both exhaustive forms from Section 2 contradict containment.
This proves Theorem 1.1 without a force equation or boundary
premise at T.

## 5. Original S/S diamond feature with K above both roots

Retain the complete original component
\[
             HK,\ HB,\ HC,\ KB,\ KC,\ HL_H,\ BL_B
\]
with two genuine S leaves, true H4,K3,B3,C2, positive circle loads
at K,C and all three arbitrary completion units, throughout
\[
                  79/40\le R\le\sqrt{1105}/16.
\]
Assume HB,HK,BK are all genuinely shared, and the two actual
shared forces directed from H,B toward K are parallel with the
same direction. This is precisely the feature where the parallel
normal pair of the three-shared triangle occurs at K.

After rotating/reflection, all three square frames are parallel,
K is above both roots, and the actual shared sides have
\[
 \begin{aligned}
 H&=[h-1,h]\times[q,q+1],\\
 B&=[h,h+1]\times[q,q+1],\\
 K&=[h+k,h+k+1]\times[q+1,q+2],
                       \qquad -1<k<0.
 \end{aligned}
 \tag{8}
\]
The equality of the root heights is forced by their contacts
with the same actual lower side of K. Positive overlap with both
root tops is exactly -1<k<0. These are physical supports; the
actual positive means on all three sides remain arbitrary.

The strict d<1 interval of this whole original layout is already
excluded by the accepted distinct-root theorem. On d>=1 the real
S-root inward segments give |h|<=delta=d-1. The unchanged B3
force equation, with B-to-H normal -E_1 and B-to-K normal E_2,
makes its real leaf the lower-right vertex:
\[
                p_{L_B}=(h+1,q),\qquad
                q<0,\qquad (h+1)^2+q^2=d^2.
 \tag{9}
\]
At d=1 this forces h=q=0, contradicting q<0. Therefore d>1, and
\[
                         -4/15<q<0,\qquad
                         q^2\le4(d-1)<1/15.
 \tag{10}
\]

Apply the reviewed arbitrary-degree H-owner-direction theorem to
the real H-owned HB side and its physical common boundary neighbor
K. It gives (e_H)_x<0. The H leaf is consequently its upper-left
vertex, lower-left vertex or the aligned left side.

The upper-left vertex would give
4h=2q+1, but 4h<1/15 and 2q+1>7/15 by (10), impossible.
For an aligned left leaf, the full H4 vertical equation has zero
leaf and HB components, a strictly positive HK component and a
nonnegative HC component. The latter sign is exactly the
translation-invariant physical routing consequence of Section 2,
applied to the actual C touching H,K. This contradicts the
unchanged H4 equation.

The H leaf must therefore be its lower-left vertex. Comparing its
norm with (9) gives h=0. Put t=q+1. The actual units in (8)
now have exactly the shelf form (1), with
\[
                           11/15<t<1.
\]
K is genuinely boundary, and the actual C is a distinct contained
unit physically touching H,K and avoiding B. Theorem 1.1 excludes
it. This closes the entire stated original three-shared-triangle
feature, retaining every actual mean and all circle-weight masks.

The proof never applies a C2 equation at K or removes HC from H4.
Its principal physical theorem in fact needs no C load at all.

## 6. Exact inputs and remaining scope

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_SQUARE_COORDINATE_MINIMUM_INTERIOR_POINT.md | 9011a40a6b811dd62069fb4f5336a04196746ca148845a8fce0e75e14763b938 | The actual reflected point (max x-1,min y+1) of every unit |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine S supports and inward segments |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd | Entire original hub-tip lower exit |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | Genuine arbitrary-degree H owner direction |

The elementary coordinate-point source is a required independent
review dependency. Original accepted inputs are compared with head
26d9e3042b733ff0796876a4607a7d834f4b630a. The H owner theorem's
separate full review remains pinned at
ef11ab0d9e3adb0a574924bafd6b2ef4d296fbeeb17665fc478dbd127db860b8.

The main shelf theorem applies to arbitrary physical units at its
stated exact coordinates. The original join removes the complete
parallel-at-K three-shared triangle feature. It does not remove
the other parallel locations, central singleton owners, or the
whole original S/S hub-tip gate. All nine units and the three
completion units remain.

No new normal selection, shared-mean choice, physical-mask
simplification, graph ID, gate tick, numerical certificate,
orientation sample, ledger edit, Lean invocation, CI workflow or
remote mutation is introduced.
