# The distinct-S wall has capacity three on its full physical slider

Date: October 26, 2026.

**Status: complete whole-slider capacity extension and original-domain
joins, pending fresh independent review.** The exact accepted upper
and lower capacity proofs extend to 0<=t<2x, with the explicit
boundary-point argument below at t=0. Their narrower statement
inherited a lower endpoint from a five-body stress classification;
that endpoint is not a premise of either geometric proof.

This source verifies the extension explicitly and applies it to the
genuine H4/K3 S/S diamond. Together with a continuous return-unit
exclusion and the reviewed shelf theorem, it excludes the entire
HB/BK/HK shared triangle. C and all three arbitrary completion units
are counted together as four further physical units. No actual force
at H or K is deleted to obtain a five-body stress.

## 1. The expanded purely physical capacity theorem

Put
\[
 x=\frac{\sqrt{70}-8}{4},\quad
 \delta=x^2,\quad d=1+\delta,\quad u=1-\delta,\quad
 R^2=(d+1)^2+\frac14.
 \tag{1}
\]
Thus
\[
                  8x+2x^2=\frac34,\qquad
                  \frac1{11}<x<\frac1{10}.
\]
Let a physical packing contain the five actual units
\[
 \begin{aligned}
 A&=[\delta,d]\times[t-1,t],\\
 B&=[-u,\delta]\times[2x-1,2x],\\
 C&=[-u,\delta]\times[2x-2,2x-1],\\
 L_A&=[d,d+1]\times[-1/2,1/2],\\
 L_B&=de_B+[0,1]e_B+[-1/2,1/2]Je_B,
                    \quad e_B=(-u,2x)/d,
 \end{aligned}
 \tag{2}
\]
with the full interval
\[
                                0\le t<2x.
 \tag{3}
\]

**Theorem 1.1.** At most three further arbitrary unit squares can
be contained in D_R with disjoint open interiors from the five units
in (2) and from one another, for every t in (3).

The theorem imposes no stress or force equations on the five units.
It does not require
t>=x(1-2x)/(1-x). All further frames, circle masks, contact types
and relative locations are arbitrary.

## 2. Exact transfer of the whole upper-pocket proof

The accepted DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md has the same
physical coordinates (1)--(2), with the narrower inherited slider.
Its complete proof uses t only for the following geometric screen:
\[
 0\le t<2x<1
 \quad\Longrightarrow\quad
 \begin{cases}
 O\in\operatorname{int}B,\\
 [O,de_B]\subset B,\\
 [O,de_A]\subset A\cup B,\quad e_A=E_1.
 \end{cases}
 \tag{4}
\]
These statements hold throughout (3). In particular the east ray
is covered by B on 0<=X<=delta and by A on delta<=X<=d
because y=0 lies in the closed interval [t-1,t]. At t=0 it
is the upper boundary of A, but it remains a barrier to another
square's open interior: an open neighborhood containing a point
of that edge also meets A's open interior immediately below it.
Thus no additional square's open interior can contain any point
of that ray. The two actual
radial leaves and their outer-face screens complete the two
whole-ray barriers.

All remaining ingredients of that four-section proof depend only
on the fixed x,delta,d,R and the actual physical units, not on t:

| Upper source section | Exact input retained on (3) |
| --- | --- |
| Section 1 | The two whole-ray screens (4), center radius at most d+1/2<151/100, and wedge angle phi=pi-2 arctan x<170 degrees |
| Section 2 | Every unit wholly in y>=0 with center radius at most 2/3 contains (0,2/11) in its open interior; this point lies in the fixed B |
| Section 3 | Each upper extra center of radius in [2/3,151/100] is more than 40 degrees from each real radial terminal |
| Section 4 | Any two such centers at angular separation at most 30 degrees have distance strictly below one |

Thus every actual upper extra has center radius >2/3. Its center
angle lies in an interval of length
phi-80 degrees<90 degrees. Four such centers would have three
successive gaps strictly exceeding 30 degrees, impossible.

This is exactly the accepted upper-pocket capacity proof on its
unchanged quantitative domains. The extension does not infer a
whole-square region from a center sign; the original whole-ray
screen still places the entire open square in the angular sector.
No force-derived lower slider endpoint is used.

## 3. Exact transfer of the whole lower-region proof

Write
\[
 f=1-2x,\qquad v=2-2x,\qquad m=d+1/2.
\]
The fixed lower column and the actual central rectangle used in
DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md are
\[
 \mathcal K=B\cup C=[-u,\delta]\times[-v,2x],
 \qquad
 \mathcal H=[-u,d]\times[-f,0]\subseteq A\cup B.
 \tag{5}
\]
The inclusion is valid on the full interval (3): A's lower
height t-1 is below 2x-1=-f, and its upper height t is at least
zero. At t=0 the whole closed central rectangle is still present;
all its interior points below y=0 remain in the interior of the
physical union. No sharper lower bound on t is required.

The exact fixed inequalities in that source remain
\[
 \begin{gathered}
 d<101/100,\quad m<151/100,\quad
 4/5<f<5/6,\quad 9/5<v<2,\quad v>d,\\
                    R^2=u^2+v^2,\qquad
                    d^2+v^2=R^2+4\delta>R^2.
 \end{gathered}
 \tag{6}
\]
Its complete seven-section lower proof transfers as follows:

| Lower source section | Exact retained input and conclusion |
| --- | --- |
| Section 1 | The fixed column in (5), the fixed left-leaf center and the radius bound force every lower-sector center right of the column, with X>=delta+1/2 |
| Section 2 | The east-ray screen in (4), the real rectangle in (5), and fixed right leaf prove whole-square y<=0 and the complete center bounds delta+1/2<=X<d, f+1/2<=-Y<m<v |
| Section 3 | The fixed column gives the positive-tilt horizontal bound. For negative tilt, a top point with delta<X<d and -f<Y<=0 overlaps the actual A because t-1<-f and t>=0, with the y=0 boundary case handled below |
| Sections 4--5 | The exact fixed inequalities (6) exclude wrapping around the right end or below the column for every remaining oblique orientation |
| Section 6 | The remaining whole quadrant x>=delta,y<=-f has a corner of squared norm at least d^2+v^2>R^2, including the aligned limit |
| Section 7 | These cases exhaust the lower sector by the actual whole-square routing |

At t=0, the sole needed endpoint clarification concerns a proposed
top extreme at height exactly zero in lower Sections 3--4. The
whole-square screen has already put the extra in y<=0. If that
top point has horizontal coordinate strictly inside the relevant
central obstacle interval, the extra has interior points arbitrarily
close to it below zero. Those points lie in the interior of A or
of the actual central rectangle in A union B, contradicting physical
nonoverlap. Thus a boundary contact at y=0 cannot evade either
the negative-tilt exclusion or the right-wrap routing. Points at
the horizontal obstacle endpoints retain the same weak inequalities
as in the accepted proof.

This covers the only boundary change from t>0. The lower ray screen
in Section 2 remains valid by the same open-neighborhood argument
already given in Section 2 here. Every other inequality concerns
fixed x,delta,d,f,v,m and the unrestricted extra square's actual
frame and center, with no lower t bound.

Consequently no lower-sector unit exists anywhere on (3).
Together with Section 2, this proves Theorem 1.1 for the entire
expanded physical slider.

The new coordinate-minimum point theorem supplies an optional
single-line verification of the last quadrant step: reflect y,
then an actual unit in x>=delta,y>=f contains a point whose
squared norm is at least (delta+1)^2+(f+1)^2=d^2+v^2.
The accepted complete lower proof already establishes that step,
so this optional simplification is not a prerequisite of the
capacity extension.

## 4. Original diamond: parallel shared ports at the genuine B3 tip

Now return to the original positive S/S hub-tip diamond
\[
              HK,\ HB,\ HC,\ KB,\ KC,\ HL_H,\ BL_B,
 \tag{7}
\]
with true H4,K3,B3,C2, positive circle loads at K,C and all three
additional physical units. Assume HB,BK,HK are genuinely shared,
and B's two nonleaf shared normals are parallel.

Here R is again arbitrary in the original window and
d=sqrt(R^2-1/4)-1; the fixed values in (1) are not assumed.

Opposite B side normals would put H,K beyond opposite sides of B,
so they could not touch. The parallel normals therefore have the
same direction. Rotate so both B-to-H and B-to-K are -E_1.
The full B3 force equation makes its genuine leaf direction E_1.
Its actual radial support and width give
\[
                    B=[d-1,d]\times[t-1,t],
                             \qquad 0\le t\le1.
 \tag{8}
\]
The endpoint values are initially retained because the real leaf
mean (d,0) can be at a side endpoint.

Shared contacts make H,K parallel to B and put both in the same
left column. They have disjoint interiors and a shared mutual side,
so their vertical translations differ by exactly one. Reflect
vertically if necessary to put H above K:
\[
 \begin{aligned}
 H&=[d-2,d-1]\times[T-1,T],\\
 K&=[d-2,d-1]\times[T-2,T-1].
 \end{aligned}
 \tag{9}
\]
Every actual mean on all three shared sides is still arbitrary.

The original d<1 domain is already excluded by the distinct-root
common-boundary-neighbor theorem. On d>=1, write delta=d-1.
The actual H-owned HB side and the physical common boundary
neighbor K let the arbitrary-degree owner-direction theorem apply
at the real H4. It gives (e_H)_x<0.

At d=1 this makes the H leaf direction -E_1: its actual support
point has first coordinate -1 and radius one, hence second
coordinate zero. The two genuine leaves are then antipodal.
The accepted full-window antipodal-leaf/boundary-pair corollary
excludes this exact original component, because K,C are the
only other positive circle loads and physically touch. Thus the
d=1 wall has not been omitted.

Retain d>1, put delta=d-1 and temporarily x=sqrt(delta).
Then 0<delta<1/60 and 0<2x<4/15. An aligned H leaf to the left
would require support 1-delta=d=1+delta, impossible. The only
real H features are therefore its upper-left or lower-left vertex.
Their transverse radial coordinate has absolute value 2x.

## 5. The circle equation forces the exact wall without shortening H4 or K3

If the H leaf is at the lower-left vertex, its vertical coordinate
is -2x and T=1-2x. The actual K in (9) has farthest corner
\[
                         (-(1-\delta),-1-2x).
\]
Every K corner then has squared norm strictly below
\[
                   1+(19/15)^2=586/225<17/4\le R^2,
\]
contradicting K's genuine circle contact. Thus this entire lower
leaf feature is impossible.

The H leaf must be its upper-left vertex, with
\[
                 T=2x,\qquad p_{L_H}=(-(1-\delta),2x).
\]
The actual K is now
\[
                       K=[-(1-\delta),\delta]
                                      \times[2x-2,2x-1].
\]
Its unique farthest corner is (-(1-delta),2x-2), and physical
circle contact gives
\[
 (1-x^2)^2+(2-2x)^2=(2+x^2)^2+\frac14.
\]
The exact simplification is
\[
                           8x+2x^2=\frac34.
 \tag{10}
\]
The positive root is exactly the x in (1). All fixed physical
coordinates of H,K and both genuine leaves therefore agree with
(2), under the correspondence
\[
      A_{\rm wall}=B_{\rm diamond},\quad
      B_{\rm wall}=H_{\rm diamond},\quad
      C_{\rm wall}=K_{\rm diamond}.
 \tag{11}
\]

This derivation used physical shared supports, the actual B3
direction, the physical H-owner direction and K's containing-circle
point. It used no H3 or K2 equation and imported no five-body
positive-stress classification.

## 6. The full real B3 moment supplies exactly the expanded slider

The actual B in (8) must overlap both H and K in positive-length
shared sides. With the obtained fixed heights, this gives
\[
                                0\le t<2x.
 \tag{12}
\]
The lower zero endpoint must still be checked.

Let Y and Z be the actual heights of the BH and BK aggregate
applications. Their complete intervals give
\[
                      Y\le t,\qquad Z\le2x-1<0.
\]
Both actual B-to-neighbor normals are -E_1 and the real leaf
has zero origin moment. The full B3 origin equation is therefore
\[
                        \mu_{BH}Y+\mu_{BK}Z=0,
                            \qquad \mu_{BH},\mu_{BK}>0.
\]
It forces Y>0 and hence t>0. No H/K force equation or mean
value is needed. The entire actual slider lies in
\[
                                0<t<2x,
\]
which is contained in the expanded closed-lower-endpoint capacity
domain of Theorem 1.1.

The five distinct actual units H,B,K,L_H,L_B are consequently
a physical wall core in that domain. The original C and the three
arbitrary additional units are four distinct further physical
unit squares. Theorem 1.1 permits at most three. This contradiction
closes the whole stated parallel-at-B shared-triangle feature
with all nine units retained.

The actual C forces on H and K were never removed. C is counted
as a genuine physical completion unit, alongside the three others,
only after a degree-free capacity theorem is available for the
obtained five-unit physical configuration.

## 7. Parallel shared ports at the genuine H4 hub

Now suppose the parallel pair of the same shared triangle occurs
at H. Keep all four actual H forces. Rotate so H is the right
unit and its shared forces toward B,K both point left. Reflect
vertically so B is above K. The actual parallel-frame supports are
\[
 \begin{aligned}
 H&=[h,h+1]\times[t-1,t],\\
 B&=[h-1,h]\times[T-1,T],\\
 K&=[h-1,h]\times[T-2,T-1],
                 \qquad T-1<t<T.
 \end{aligned}
 \tag{13}
\]
The strict slider bounds are exactly the positive overlaps of H
with both units in the left column. Both genuine roots meet
D_delta on d>=1, so |h|<=delta. The strict d<1 domain is
excluded by the same original distinct-root theorem as in Section 4.

The unchanged true B3 equation has its B-to-H normal E_1 and
B-to-K normal -E_2. It makes B's genuine leaf the upper-left
vertex:
\[
            p_{L_B}=(h-1,T),\quad T>0,\quad
                      d^2=(h-1)^2+T^2.
 \tag{14}
\]
At d=1 the small shared support gives h=0 and then T=0,
impossible. Thus d>1. Also
\[
                         0<T<4/15.
\]
The actual K has its unique farthest corner at (h-1,T-2),
so physical circle contact gives
\[
 R^2=(h-1)^2+(T-2)^2,\qquad
                       T=\frac{11}{16}-\frac d2<\frac3{16}.
 \tag{15}
\]
The second identity follows by subtracting (14), since
R^2-d^2=2d+5/4.

The actual H-owned HB side has normal -E_1 and the physical
common boundary neighbor K. The arbitrary-degree H-owner theorem
gives (e_H)_x>0. Its possible genuine leaf supports are therefore
the two right vertices or its aligned right side. The lower-right
vertex would have vertical coordinate t-1<-11/15 by (13)--(14),
whereas its radial norm and |h|<=delta force
|t-1|^2<=4delta<(4/15)^2. Thus that feature is impossible.

### 7.1. The complete aligned H4 feature uses the closed capacity endpoint

If H is aligned with its real rightward leaf, then h+1=d, so
h=delta. The real mean (d,0) gives 0<=t<=1. Equations (14)--(15)
then force T=2sqrt(delta) and the same exact wall radius equation
(10). The actual shared HK side gives t<T=2x. Consequently
\[
                              0\le t<2x.
\]
The physical five-unit core H,B,K,L_H,L_B is exactly (2),
with the obvious root labels. Theorem 1.1, including its explicitly
proved t=0 endpoint, permits at most three further units.
The actual C and the three extras are four. This excludes the
whole aligned H4 feature without using an H3 moment or choosing
one of its shared means.

### 7.2. A tilted H leaf fixes the sign of the remaining return region

If H is not aligned with its leaf, only its upper-right vertex
remains:
\[
              p_{L_H}=(h+1,t),\qquad t>0,\qquad
                         d^2=(h+1)^2+t^2.
\]
Comparing with (14) gives
\[
              4h=T^2-t^2>0,\qquad
                   0<t<T<3/16,\qquad h>0.
 \tag{16}
\]
Every actual C touching H,K and avoiding B must lie wholly below
H, with
\[
                              \max_C y=t-1.
 \tag{17}
\]
Here is the complete contact cover, independent of any C force.

The left side of H is covered by the B/K column. At its interior
points the two sides fill the plane locally; at their junction
the two left quadrants still fill the left half-plane. At H's
upper-left corner, B fills the left half-plane and H fills the
southeast quadrant, so any further unit there would lie northeast,
above K. At H's lower-left corner, K fills the left half-plane
and H fills the northeast quadrant, so a further unit must lie
southeast, as in (17).

A top-side interior contact puts the further unit above y=t,
strictly above K's top T-1. A right-side interior contact puts it
right of x=h+1, beyond K's right edge h. Neither can reach K.

At the upper-right corner, a further vertex-contact quadrant is
wholly above or right, and cannot reach K. At the lower-right
corner, a further vertex-contact quadrant is wholly right or
below; only the below option can reach K. If either right corner
is in the side interior of the further unit instead, its inward
normal has nonnegative horizontal component, and the possible
leftward span along that unit side is strictly less than one.
Thus its minimum x is strictly above h, so it cannot reach K.
The actual bottom-side contacts give (17) directly. This exhausts
all sides, corners and either type of neighbor support.

### 7.3. Every orientation of the return unit exceeds the circle

Put v=2-T>1 and Delta=T-t in (0,3/16). If the actual C in (17)
is wholly in x>=h, reflect y and apply the coordinate-minimum
point theorem to this full orthant. It gives
\[
 R^2\ge(h+1)^2+(2-t)^2
           >(1-h)^2+(2-T)^2=R^2,
 \tag{18}
\]
where the strict difference is
4h+(2-t)^2-(2-T)^2>0 by (16). Thus a possible C would have
to wrap to x<h.

An axis-parallel C cannot wrap: its top side is at t-1, its
horizontal interval meets H's bottom, and any part left of h
overlaps the interior of K, whose height interval contains t-1.
For a tilted C, its unique top vertex is (X,t-1), with
h<=X<=h+1. Write its two inward downward axes as
\[
                 (-c,-s),\quad(s,-c),\qquad
                   c,s>0,\quad c^2+s^2=1.
\]
No ordering of c,s is imposed.

Its leftmost vertex is (X-c,t-1-s). If it has x<h, it also has
x>h-1 because X>=h and c<1. Its height is below K's top T-1,
so nonoverlap forces it at or below K's bottom T-2. Hence
\[
                           s\ge1-\Delta>13/16.
 \tag{19}
\]
In particular s>c. The actual bottom corner consequently has
\[
                 x\ge h+s-c>0,\qquad -y\ge v+c.
\]
Its squared radius exceeds the actual circle value:
\[
 \begin{aligned}
 &(h+s-c)^2+(v+c)^2-[(1-h)^2+v^2]\\
 &\qquad=c^2+2c(v-s)+2h(1+s-c)>0.
 \end{aligned}
 \tag{20}
\]
Every term has the asserted sign: c>0, v>1>=s, h>0, and
1+s-c>0. This is a whole-orientation identity, not a pose
sample or a scalar packet.

Both possibilities contradict containment. Thus no actual C
can touch H,K in the retained tilted-H feature. This closes
the other H-parallel branch while keeping the genuine H4,
K3,B3,C2 equations and all actual side means.

## 8. Every location of the parallel pair is now covered

For three pairwise shared unit squares, all frames are parallel.
Among the three unoriented side axes, two agree. They meet at
one of H,B,K; opposite normals there would put the other units
beyond opposite sides and prevent their mutual contact. Thus
the parallel pair has the same direction. The third shared edge
is perpendicular, since two same-side unit neighbors meet along
their transverse side. Exactly the three parallel locations
H,B,K exhaust this physical triangle.

Sections 4--6 exclude the location B. Section 7 excludes location
H, retaining the true higher-degree H4 and the closed aligned
slider wall. The already reviewed
BOUNDARY_STRADDLING_SHELF_RETURN_EXCLUSION.md excludes location
K, with its complete original force and geometric cover.

Consequently the full original S/S hub-tip diamond cannot have
\[
                  \boxed{HB,\ BK,\ HK\text{ all genuinely shared}.}
 \tag{21}
\]
No singleton owner was called shared, and all other positive
perimeter and central contact features remain under the same
original gate.

## 9. Exact source provenance and verification boundary

The complete accepted upper and lower sources were freshly fetched
and read in full at comparison head
26d9e3042b733ff0796876a4607a7d834f4b630a.

| Source | SHA256 | Git blob |
| --- | --- | --- |
| DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md | 9865cd82e3d177b52d663c38a5e2d049558d0c75295c81f153fa0375b9ad030e | 4ea84b7f582966c84759ab7f4271c42790c435fc |
| DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md | c0e6029fd1949d02383a5b774f426b49bec92210339d0aebf7b34b0c52cfd157 | 97afc035a42082269449856d973418e07ae04b61 |

The old stress-derived lower slider endpoint occurs in
DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md, Section 7, SHA256
eb81a560492c95d84a54627bfea14690956e4bf16f67b190c81c9938038aa443,
Git blob 1fc55dc53d936181a87cde12b661ded590fb9e0c. That old
five-body force classification is not a premise of Sections 4--6
and is not applied to the original higher-degree diamond.

| Other input | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Actual genuine S support, mean and aligned radial interval |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | H4 physical owner direction |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd | Complete original d<1 exit and genuine antipodal d=1 force-sum exit |
| UNIT_SQUARE_COORDINATE_MINIMUM_INTERIOR_POINT.md | 9011a40a6b811dd62069fb4f5336a04196746ca148845a8fce0e75e14763b938 | Full orthant radius bound in the tilted-H return exclusion |
| BOUNDARY_STRADDLING_SHELF_RETURN_EXCLUSION.md | 28f136149689e531aab2aa9b729abd621eaec3f5af99464c97b3c3bdaa3fa829 | Complete remaining parallel-at-K shared-triangle location |

The coordinate-point source has full independent review
d92fe0d7e0abe91d711b0b43be1b9786d73f84ef3319a0a15b56adc4ba24e6ad;
the shelf source has full independent review
d5efc9c36597c9fa011c39b99bdc3ed778469fda3e3c6e8cf976620688597902.

The capacity extension and complete shared-triangle join introduce no
normal selection, numerical certificate, pose subdivision, graph ID
or gate tick. Other physical shared/singleton contact features remain
under the same original S/S hub-tip gate. No
shared mean, circle atom, positive force or physical body is
deleted. No Lean build, CI workflow or remote mutation was used.
