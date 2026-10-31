# A far-wall boundary neighbor cannot span backward across a unit channel

Date: October 28, 2026 UTC. Author: broad_load_channels continuation.
Comparison head: `234b4f0d03d772031dfc90a739fbe5b45351a3b8`.

**Status: complete proposed uniform physical theorem, complete boundary
triangle/channel consequence, and complete original D02.L0145 exclusion;
frozen for full root and separate independent mathematical review.**
No original flag is edited by this source. No computational exclusion
certificate is introduced.

The new physical theorem has no force or degree premise. It preserves
both tilt signs of its far-wall unit and every original contact mean
and support owner of the spanning unit. A single pair of continuous
scalar inequalities bounds all four actual corners at once. The
literal original application retains the loaded true-degree-two body 5
and every force at the actual true-degree-two body 4; neither is turned
into an unloaded transmitter.

Root contributed the backward-support-reach observation and suggestions
for the physical bypass route, and checked the corner-bound identities
during development. Root is a mathematical contributor and cannot be
the sole independent reviewer. The author's earlier complete triangle
channel reduction is used only at its separately reviewed exact scope.

## 1. The whole physical far-wall strip

Put

\[
Q_*=\frac{1105}{256}.
\]

Let K be any actual unit square contained in the disk `D_R(O)`, with
`R^2<=Q_*`. Choose any orthonormal coordinates centered at the actual
O, and assume

\[
                         K\subseteq\{x\ge59/60\}.
\tag{1}
\]

**Far-wall strip theorem.** Every actual point of K satisfies

\[
                              |y|<\frac{13}{20}.
\tag{2}
\]

There is no physical circle-contact, stress, degree or selected-normal
premise. The wall may be strictly behind the actual support, and both
own-frame signs and the axis endpoint are included.

The complete current theorem
`GENERAL_FAR_WALL_59_60_SQUARE_BOUNDS.md` supplies

\[
C\ge s\ge0,\quad C^2+s^2=1,\quad
s<1/10,\quad C>99/100,
\tag{3}
\]

where C,s are the larger and smaller nonnegative horizontal projections
of K's own axes. Write its actual minimum x-coordinate as `x_0>=59/60`.
The additional elementary estimate

\[
                  C=\sqrt{1-s^2}\ge1-s^2\ge1-s/10
\tag{4}
\]

holds over the full interval in (3).

It suffices to exclude `max_K y>=13/20`; reflection of the entire physical
coordinates then proves the lower bound. There are exactly two tilt signs.

In the first, use own axes `(C,s),(-s,C)`. The actual highest corner has
x-coordinate `x_0+C>148/75`. If its y-coordinate were at least 13/20,
its squared norm would exceed Q_*, because

\[
\left(\frac{148}{75}\right)^2+
\left(\frac{13}{20}\right)^2-Q_*
=\frac{199}{1440000}>0.
\tag{5}
\]

In the second sign, use axes `(C,-s),(s,C)`. If the actual highest corner
has height t, the actual upper-far corner has coordinates

\[
                      (x_0+C+s,\ t-s).
\]

For `t>=13/20`, its two coordinates are bounded below by the positive
quantities `119/60+9s/10` and `13/20-s`, by (4). Their squared sum is

\[
\left(\frac{119}{60}+\frac{9s}{10}\right)^2+
\left(\frac{13}{20}-s\right)^2
=\frac{7841}{1800}+\frac{227}{100}s+\frac{181}{100}s^2.
\tag{6}
\]

Every additional term is nonnegative, and

\[
                      \frac{7841}{1800}-Q_*
                         =\frac{2287}{57600}>0.
\tag{7}
\]

Thus this actual corner also contradicts containment. At s=0 either
description proves the strict inequality. Reflection includes the entire
negative-y domain. Since a linear coordinate attains its extrema at actual
corners, (2) holds on the whole closed K.

## 2. A sharp support reach fact, with all means retained

Let B be any actual minimum-g support point of a unit square Y, where
g is a unit vector. If `g_x>=0`, then every z in Y satisfies

\[
                             B_x-z_x\le1.
\tag{8}
\]

At a vertex B, choose the two orthonormal inward own edges u,v. Their
g-components are nonnegative. If both u_x and v_x were strictly negative,
the expansion `g=(g.u)u+(g.v)v` would have negative x-component, since
at least one coefficient is positive. Thus at most one edge contributes
a negative x displacement; its magnitude is at most one. Maximizing
backward displacement over the actual square gives (8).

At a side-interior point B, g is that side's inward own normal and the
actual square is

\[
                 B+[0,1]g+[-\tau,1-\tau]j,
\qquad0\le\tau\le1,
\]

for an own tangent j. The normal segment has nonnegative x displacement;
the original tangent interval has length one and projected backward
extent at most one. Its actual endpoints are also covered by the vertex
argument. This proves (8) for every original support owner and mean.

Consequently, if an actual point of Y has x-coordinate less than h and
its unchanged minimum-g support point B has `B_x>=h+1`, then

\[
                                  g_x<0.
\tag{9}
\]

No force equation or generic-normal rule is involved. In a positive
contact application, the original selected normal is used unchanged.

## 3. The uniform spanning-unit theorem

Keep a real h with

\[
                               |h|<1/60.
\tag{10}
\]

Let Y be any actual unit square, and keep an actual minimum-g support
point B and its original unit normal. Suppose

\[
 B_x\ge h+1,\qquad |B_y|<13/20,\qquad
 \text{some actual point of Y has }x<h.
\tag{11}
\]

**Spanning-unit theorem.** Every actual point of Y satisfies

\[
                              |z|^2<17/4.
\tag{12}
\]

Y need not be physically boundary, loaded, degree two, or a member of
any particular positive graph. Its original normal, actual support point,
whole support-side mean and frame are retained. Containment of Y in a
circle is not a premise of this purely physical conclusion.

### 3.1. The complete frame and support cover

By (8)--(11), `g_x<0`. Reflect the whole y-coordinate if necessary so
`g_y>=0`; both bounds on B_y and all physical data in (10)--(11) are
preserved. Write `g=(-u,v)` with u>0,v>=0.

Y's horizontal width is strictly greater than one by its two actual
points in (11), so Y is not axis aligned. It has a unique actual lowest
vertex A and the two upward own edges

\[
                     (c,s),\quad(-s,c),
\qquad c,s>0,\quad c^2+s^2=1.
\tag{13}
\]

There is no order imposed between c and s. The two diagonal orientations
c=s and both one-sided axis limits remain in the domain.

The second edge has strictly positive g-component `us+vc>0`. Therefore
the actual minimum-g support face has zero coefficient on that edge:
it is contained in the lower-right edge from A to `A+(c,s)`. In particular
the unchanged point B has exactly the form

\[
                         B=A+\tau(c,s),\qquad0\le\tau\le1.
\tag{14}
\]

This includes a Y-owned side with its full actual mean and a unique
rightmost vertex, including a free vertex normal. If the minimum face
were the lowest vertex alone, the forthcoming strict inequality would
exclude it for a proved reason.

Write `B=(\beta,\gamma)`. Y's actual leftmost vertex is

\[
                  (\beta-\tau c-s,\ \gamma-\tau s+c).
\]

Its x-coordinate is less than h by (11), so

\[
                      \tau c+s>\beta-h\ge1.
\tag{15}
\]

In particular tau>0. No actual contact has been replaced by an endpoint
of its mean interval; tau is the original parameter in (14).

### 3.2. One scalar bound for the top corner

From (15),

\[
c+(1-\tau)s
<c+\frac{s(c+s-1)}c
=s+\frac{1-s}c
=s+\sqrt{\frac{1-s}{1+s}}.
\tag{16}
\]

For the entire interval `0<=s<=1`,

\[
                   s+\sqrt{\frac{1-s}{1+s}}<\frac87.
\tag{17}
\]

To verify this uniformly, `8/7-s` is positive, so squaring reduces the
inequality to positivity of

\[
P(s)=49s^3-63s^2+s+15
=49(s-6/7)^2(s+3/7)+s-3/7.
\tag{18}
\]

If `0<=s<=3/7`, the last expression is at least
`49(3/7)^2(3/7)-3/7=24/7>0`. If `3/7<=s<=1`, both terms are
nonnegative and cannot vanish simultaneously. This proves the strict
bound on the full closed interval, with no sampled angle or sign packet.

### 3.3. One quadratic bound for the rightmost corner

The identity

\[
                   s\le\frac47s^2+\frac7{16}
\tag{19}
\]

follows from `(4/7)(s-7/8)^2>=0`. On the full actual circle
`c^2+s^2=1`, another exact identity gives

\[
\frac{11}{5}-\left(\frac{61}{35}s^2+2cs\right)
=\frac{11}{5}(c-5s/11)^2+\frac{s^2}{385}>0.
\tag{20}
\]

Combining (19)--(20) proves

\[
                  s^2+2cs+\frac{13}{10}s<\frac{443}{160}.
\tag{21}
\]

These identities include every original tilt and the full side-mean
range; no interval subdivision in a physical angle is needed.

### 3.4. All four actual corners are strictly within the same fixed disk

For the bottom vertex A, `\beta>=h+1`, tau<=1 and (15) imply

\[
                    h<A_x<h+s<h+1.
\]

Thus `|A_x|<61/60`. Its height is `\gamma-\tau s`, of absolute
value less than 33/20. Its squared norm is therefore strictly below

\[
             \left(\frac{61}{60}\right)^2+
             \left(\frac{33}{20}\right)^2
             =\frac{6761}{1800}<\frac{17}{4},
\tag{22}
\]

with reserve `889/1800`.

The leftmost vertex has x-coordinate less than h and at least
`h+1-c-s`. Since `sqrt(2)<17/12`, these give absolute x-coordinate
less than 13/30. Its height `\gamma+c-\tau s` has absolute value
less than 33/20. Its squared norm is strictly below

\[
             \left(\frac{13}{30}\right)^2+
             \left(\frac{33}{20}\right)^2
             =\frac{10477}{3600}<\frac{17}{4},
\tag{23}
\]

with reserve `4823/3600`.

The top vertex is

\[
            (\beta+(1-\tau)c-s,\ \gamma+(1-\tau)s+c).
\]

Its x-coordinate is at least `h+1-s>h` and less than `h+c<h+1`.
Its height is greater than gamma and, by (16)--(17), less than
`13/20+8/7=251/140`. Thus both signs of its height are covered, and
its squared norm is strictly below

\[
             \left(\frac{61}{60}\right)^2+
             \left(\frac{251}{140}\right)^2
             =\frac{374669}{88200}<\frac{17}{4},
\tag{24}
\]

with the strict uniform reserve `181/88200`.

The rightmost vertex is

\[
                (\beta+(1-\tau)c,\ \gamma+(1-\tau)s).
\]

Its x-coordinate is positive and less than `h+c+s`. The absolute
value of its height is less than `13/20+s`, including when that
height is negative. Since `c+s<=sqrt(2)<3/2` and `|h|<1/60`, its
squared norm is strictly below

\[
\begin{aligned}
 &(c+s)^2+(13/20+s)^2+1/20+1/3600\\
 &=1+169/400+s^2+2cs+(13/10)s+1/20+1/3600\\
 &<1+169/400+443/160+1/20+1/3600
   =\frac{30539}{7200}<\frac{17}{4}.
\end{aligned}
\tag{25}
\]

The final reserve is `61/7200`. The term 1/20 is the valid strict
upper bound for `2|h|(c+s)`; no sign of h was assumed.

All four actual corners satisfy the same strict target bound. Convexity
of squared norm, or its maximum over the convex hull of these actual
vertices, gives (12) on the whole closed unit Y. This proves the
spanning-unit theorem.

## 4. Broad physical consequence for a far-wall contact

Let Q and Y be actual interior-disjoint unit squares, with Q contained
in `D_R(O)`, `R^2<=Q_*`. Assume for some real `|h|<1/60` that

\[
                  Q\subseteq\{x\ge h+1\},
\qquad Q\cap Y\ne\varnothing,
\qquad \min_{z\in Y}z_x<h.
\tag{26}
\]

Keep any original common separating normal g from Q into Y and its
actual application B in their contact. If the contact carries positive
stress, these are the original selected data; no replacement is made.
The purely physical version may take any common supporting line at the
actual contact, and the proof works for every such choice.

Every actual B lies in Q, hence `B_x>=h+1` and `|B_y|<13/20` by
Section 1, since `h+1>59/60`. It is a minimum-g support point of Y.
Section 3 applies to the unchanged B and gives

\[
                              Y\subset\operatorname{int}D_{\sqrt{17}/2}(O).
\tag{27}
\]

In particular, when `R^2>=17/4`, the actual Y cannot physically touch
the containing circle. This is a full physical conclusion at the weak
endpoint `R^2=17/4` as well. There is no degree, positive load, force
ratio, proper-concurrence, circle-mask or diagonal-avoidance hypothesis
in this consequence. An actual boundary contact cannot be rescued by
giving its circle corner zero weight.

## 5. Uniform boundary triangle with a channel and a boundary bypass

Now retain the original same-nine certificate and radius window, all
original units, full force and torque equations, actual normals and
means, every physical circle mask and arbitrary completion squares.
Suppose there are distinct actual units U,V,W with positive triangle
edges UV,UW,VW, such that

* U is unloaded and its whole positive neighborhood is exactly V,W,T_1;
* V has true positive degree two with exactly U,W as its neighbors;
* V and W physically touch the containing circle;
* the original positive path `U--T_1--...--T_k--Q`, k>=1, has every
  T_i a genuine unloaded true-degree-two body, with all its actual widths
  and original application means retained;
* an actual physical boundary unit Y, distinct from these units, touches
  Q and at least one of V,W.

The full original degrees, loads and other forces at Q,W,Y are arbitrary.
Neither Q nor Y is required to have degree two. Additional physical
contacts, positive chords allowed by those true degrees, and all actual
completion units stay present.

**Uniform channel/boundary-bypass theorem.** These data are impossible.

Apply only Theorem A of the exact separately reviewed source
`BOUNDARY_TRIANGLE_HUB_TWO_UNLOADED_CHANNELS_COMPLETE_EXCLUSION.md`.
It preserves the full U3 and V2 equations and every real transmitter.
With n the original forward channel normal and P the original U/T_1
application, it proves that every possible survivor has

\[
R^2>17/4,\qquad d=\sqrt{R^2-1/4}-1>1,
\qquad\epsilon=d-1<1/60,
\tag{28}
\]

\[
k=1,\quad w_{T_1}=1,\quad
-\epsilon\le h=n\cdot(P-O)\le\epsilon,
\tag{29}
\]

\[
Q\subseteq\{n\cdot(z-O)\ge h+1\},\qquad
n\cdot(z-O)<h\quad\text{for every actual }z\in V\cup W.
\tag{30}
\]

The discarded lower radius, k>=2, and diagonal-width domains are already
excluded by that whole theorem, including all critical endpoints.
This invocation uses no second unloaded channel and no monotonicity in
loads. The actual physical clearance conclusions for U and T_1 remain
valid but are not needed below.

Use n as the x-axis. Because Y physically touches V or W, (30) gives
an actual point of Y with x<h. Its actual Q contact is on x>=h+1.
Thus the complete physical consequence (26)--(27) makes the whole Y
strictly interior to radius sqrt(17)/2. This contradicts Y's actual
circle contact at the unchanged radius in (28). No equation at Y or Q
was used or shortened. This proves the entire uniform theorem.

The same statement covers actual channels with one through four internal
units whenever they fit among the same nine original bodies. Longer
channels are excluded by the inherited width bound, while the one-unit
case is excluded by the new physical spanning theorem. This is one
uniform motif, not a contraction of a longer body graph.

## 6. Literal complete original D02.L0145 application

The exact original six-body outer hexagon has positive rim edges

`01,12,23,34,45,50`

and the positive chord `02`. Its entire positive circle-load set is
`{0,1,4,5}`. The three other actual physical units remain arbitrary and
unchanged. Use the literal roles

\[
                     U=2,\quad V=1,\quad W=0,
\quad T_1=3,\quad Q=4,\quad Y=5.
\tag{31}
\]

The full true-degree and load data are:

| Actual body | Entire positive neighbors | True degree | Original total circle load |
| --- | --- | ---: | --- |
| 0=W | 1,2,5 | 3 | Positive |
| 1=V | 0,2 | 2 | Positive |
| 2=U | 0,1,3 | 3 | Zero |
| 3=T_1 | 2,4 | 2 | Zero |
| 4=Q | 3,5 | 2 | Positive |
| 5=Y | 0,4 | 2 | Positive |

The actual triangle is `2--1--0--2`, with V and W physically boundary
by their positive total loads. The actual first channel is `2--3--4`,
and body 3 is genuinely unloaded true degree two. Body 5 physically
touches Q=4 and W=0 through the original positive edges 45 and 50.
Its positive load guarantees an actual circle corner; every individually
zero physical circle coefficient remains part of its full mask.

Every hypothesis of Section 5 is therefore literal. In particular Y=5
remains loaded, its full original degree-two equations remain, Q=4 retains
its entire actual two-force star and all circle atoms, and W=0 retains
its genuine degree three. No body or force is dropped. The contradiction
is to the physical boundary status of the actual body 5.

The graph stabilizer also contains the reflection `i -> 2-i mod 6`,
which sends the load set 0145 to 1234. The corresponding unchanged
roles are

`U=0,V=1,W=2,T_1=5,Q=4,Y=3`.

It has exactly the same hypotheses. Thus the proof covers the entire
original load orbit, all coordinate frames, original owners and means,
all physical circle masks, all positive force ratios and all three
arbitrary completion units.

The accepted same-nine lower-window entry handles any earlier R<=2
domain before the inherited certificate window is used. Theorem A also
explicitly handles its whole R^2<=17/4 interval. There is no missing
small-radius, critical, aligned, diagonal-width or zero individual
corner-weight endpoint.

## 7. Exact source identities and scope

| Complete input | Bytes | SHA256 | Exact operative use |
| --- | ---: | --- | --- |
| `GENERAL_FAR_WALL_59_60_SQUARE_BOUNDS.md` | 4515 | `be4bf3f299be99a0f65e07d3ee9c6ac96d6e5abad88c1ec50598b3ee090c1ff9` | Full force-free frame bounds at the actual 59/60 wall, both tilt signs and axis endpoint |
| `BOUNDARY_TRIANGLE_HUB_TWO_UNLOADED_CHANNELS_COMPLETE_EXCLUSION.md` | 20796 | `51ae5c3473e69b321a87ae9c44b8710aea9db7dc5f159412196a778fb71aa024` | Only complete Theorem A: original one-channel width/radius reduction and strict whole-return separation; not its second-unloaded-channel theorem |
| `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` | 11952 | `cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1` | Exact original D02 graph, L0145 load orbit, true degrees and all-nine completion contract |
| `LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md` | 13069 | `3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90` | Complete same-nine radius entry, with its separately accepted analytic prerequisites |

The three published inputs match the exact current234 tree blobs. The
Theorem A source is local and separately reviewed: its complete independent
review is
`REVIEW_BOUNDARY_TRIANGLE_TWO_UNLOADED_CHANNELS_COMPLETE_INDEPENDENT_234_2026_10_28.md`,
SHA256 `a64637bc2ce41167c246fd0c713051b4a950f0d94e37d258185d143513ba3262`.
Root acceptance and this source's own separate independent review remain
required before new authoritative adoption. The full earlier selected-
certificate and triangle/channel prerequisites retain their original
accepted domains; no new transitive audit is claimed by this source.

## 8. Exact prospective credit and surviving obligations

After full root and separate independent acceptance, this proof supplies
exactly one new whole original fine closure:

`M6.B6.HEXAGON.D02.L0145: false -> true`.

It creates no new fine identifier and changes no denominator. No whole
D02 coarse cell closes: the other original smaller-load rows need their
own full hypotheses and proofs. The earlier local L014 theorem is a
distinct closure, and the already published L01345 closure receives no
duplicate credit here. No subset or superset of the load set is declared
closed by monotonicity.

The uniform physical and channel results can be joined to any further
literal original caller with their stated hypotheses. They already cover
all orientations and all contact owners at once, with four printed
strict rational corner reserves. No numerical pose scan, optimization
output, external sign packet, adaptive subdivision or computational
exclusion certificate is an operative premise.

This source makes no authoritative ledger edit, no claim that the global
sharp theorem or its equality classification is closed, and no assertion
of Lean integration. No Lean compilation, CI, workflow, remote write,
merge or change to an accepted manuscript accompanies it.
