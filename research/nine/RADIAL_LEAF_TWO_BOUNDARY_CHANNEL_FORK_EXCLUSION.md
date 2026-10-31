# A radial-leaf root cannot feed two boundary normal channels

Date: October 26, 2026.

**Status: accepted complete hand proof after independent saved-source
and original-domain review.** See
REVIEW_RADIAL_LEAF_FORK_ROOT_2026_10_26.md and
REVIEW_RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_C6_2026_10_26.md.
The theorem covers both full genuine radial-leaf forms, all original
root poses and every channel mean. Its whole C5-plus-leaf consequence
excludes the complete block-load orbit 23, with no computational
certificate. The far endpoints may have arbitrary additional positive
forces; their force equations are not replaced by degree-two equations.

**Current stronger implication:** the independently reviewed
RADIAL_LEAF_DISTINCT_BOUNDARY_CHANNEL_STAR_EXCLUSION.md allows
arbitrary root degree, provided every nonleaf force is an actual
unloaded normal channel to a physical boundary body and at least
two far endpoint bodies are distinct. Its exact grouping permits
repeated endpoints without deleting any original force. The full
two-channel proof and original C5 joins below remain valid.

Throughout,

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad \delta=d-1.
\tag{1}
\]

The exact radius comparisons already proved in
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md give

\[
                       d<\frac{61}{60},\qquad
                       \delta<\frac1{60}.
\tag{2}
\]

## 1. Full physical premises and common channel estimates

Let A be a physically circle-clear unit square of true positive degree
three. One of its positive neighbors is a genuine radial S or D leaf L.
Its other two positive edges start actual normal channels with distinct
physical far endpoints B,C. Each channel contains at least one true
unloaded degree-two transmitter. All internal channel forces and
applications are the unchanged ones from the selected certificate.
The endpoints B,C physically touch the containing circle, whether or
not their total circle weights are positive.

Write e for the outward radial direction from A to L, lambda>0 for
that pair-force magnitude, n_1,n_2 for the two actual unit channel
directions from A, and mu_1,mu_2>0 for their magnitudes. Let p_i be
their actual applications on A and h_i=h_A(n_i)=n_i dot p_i. The
actual root equations are

\[
  \lambda e+\mu_1n_1+\mu_2n_2=0,
  \qquad
  \mu_1\det(p_1,n_1)+\mu_2\det(p_2,n_2)=0.
\tag{3}
\]

All directions in (3) point outward from A, in the sign convention
of the original physical stress equations. The leaf's origin moment
is zero because its actual application is radial. A has no omitted
fourth force and no circle force. Taking moments about any other
point, with the actual leaf term included, is therefore legitimate.

For Q_1=B,Q_2=C, the original channel equations give reserves w_i>=1
and the true support containments

\[
 A\subseteq\{x:n_i\cdot x\le h_i\},\qquad
 Q_i\subseteq\{x:n_i\cdot x\ge h_i+w_i\}.
\tag{4}
\]

Every contained unit-square center satisfies the sharp bound

\[
                         |c_Q|\le d+\frac12.
\tag{5}
\]

Indeed its farthest corner gives
R^2>=|c_Q|^2+|c_Q|+1/2. Every directional halfwidth is at least
1/2, so (4)--(5) imply

\[
   h_i+w_i+\frac12\le n_i\cdot c_{Q_i}\le d+\frac12,
                  \qquad h_i\le\delta.
\tag{6}
\]

The genuine leaf root satisfies
dist(0,A)<=max(delta,0), by Lemma 2.1 of
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md. If delta<0, then 0 belongs
to A, so h_i>=0 contradicts (6). Hence every putative fork has

\[
                     1\le d<\frac{61}{60},\qquad
                     0\le\delta<\frac1{60}.
\tag{7}
\]

The proof now exhausts the D, tilted-S and aligned-S root domains.
The actual transmitter widths need never be fixed to one, and all
shared-side application endpoints remain in their original supports.

## 2. The entire D-leaf fork is impossible

Rotate e east. The selected genuine D leaf gives the full root form

\[
 A=[\rho-1,\rho]\times[-b,a],\qquad
 \rho=R-\sqrt2,\qquad a,b>0,\quad a+b=1.
\tag{8}
\]

The actual leaf application is (rho,0), in the relative interior of
A's right side. The elementary window comparisons give

\[
                         \frac12<\rho<\frac34.
\tag{9}
\]

For the first inequality use R>=79/40 and sqrt(2)<57/40; for the
second use R<25/12 and sqrt(2)>4/3. Thus both horizontal support
distances rho and 1-rho exceed 1/4. Since the vertical interval
contains zero, every unit normal n satisfies

\[
                         h_A(n)>\frac14|n_x|
             \quad\hbox{if }n_x\ne0,
\tag{10}
\]

with the corresponding weak inequality when n_x=0. Equations
(6)--(7) force, for both actual channels,

\[
                     |(n_i)_x|<\frac1{15},\qquad
                     |(n_i)_y|>\frac{14}{15}.
\tag{11}
\]

The second comparison follows by squaring: 1-1/225=224/225 is
greater than 196/225. The vertical coordinate of (3) requires the
two nonzero vertical components to have opposite signs. Interchange
the channels if necessary, so that n_1 points upward and n_2 downward.
Their root supports then obey

\[
 h_1+h_2\ge a(n_1)_y+b|(n_2)_y|
           >\frac{14}{15}(a+b)=\frac{14}{15}.
\tag{12}
\]

But (6)--(7) give h_1+h_2<=2delta<1/30, a contradiction. This D
argument does not even require that B,C touch the circle.

## 3. Every tilted S-leaf root has a strict torque obstruction

For a tilted S root, its actual leaf application p=d e is a vertex.
Choose the inward orthonormal root side axes f_1,f_2 and, if necessary,
exchange them so that

\[
 A=p+[0,1]f_1+[0,1]f_2,
 \qquad e\cdot f_1=-a,\quad e\cdot f_2=-b,
 \qquad a\ge b>0,\quad a^2+b^2=1.
\tag{13}
\]

This is the entire tilted family and its reflection, not a small-angle
restriction. Let (x,y) be an actual channel normal in these own axes.
Its root support is exactly

\[
                  h_A(n)=-d(ax+by)+\max(x,0)+\max(y,0).
\tag{14}
\]

Since a>=1/sqrt(2)>2/3 and b<=1/sqrt(2)<3/4, (7) gives

\[
                          da>\frac23,\qquad
                          1-db>\frac{19}{80}.
\tag{15}
\]

First, no channel can have x<=0,y>=0. Equation (14) would give

\[
 h_A(n)=da|x|+(1-db)y
       >\frac{19}{80}(|x|+y)\ge\frac{19}{80}>\delta,
\tag{16}
\]

contrary to (6). This includes both axes bounding that quadrant.

Second, if x,y>0 and y>=x, then y>=1/sqrt(2)>2/3 and

\[
 \begin{split}
 h_A(n)&=(1-da)x+(1-db)y\\
       &> -\delta x+\frac{19}{80}y\\
       &\ge\left(\frac{19}{80}-\delta\right)y
        >\frac{53}{360}>\delta.
 \end{split}
\tag{17}
\]

Here 1-da>=1-d=-delta and
(19/80-1/60)(2/3)=53/360. Thus every feasible channel with y>0
has x>y>0.

For an actual support application p+X f_1+Y f_2, define its signed
own-frame moment about p as

\[
                              m=Xy-Yx.
\tag{18}
\]

The physical determinant is det(f_1,f_2) times m, the same nonzero
orientation factor for both channels. The complete support-face cover
is now:

| Feasible normal feature | Actual support coordinates | Moment m |
| --- | --- | --- |
| x>y>0 | (X,Y)=(1,1) | y-x<0 |
| x>0,y<0 | (X,Y)=(1,0) | y<0 |
| x<0,y<0 | (X,Y)=(0,0) | 0 |
| x>0,y=0 | X=1, Y in [0,1] | -Yx<=0 |
| x=0,y<0 | Y=0, X in [0,1] | Xy<=0 |

The other quadrant and its axes were excluded by (16), while (17)
excludes the remaining positive-quadrant half. Therefore every actual
channel has m<=0, including every shared-side endpoint or mean.

In the axes (13), the f_2-coordinate of the actual force equation is

\[
                         \mu_1y_1+\mu_2y_2=\lambda b>0.
\tag{19}
\]

At least one channel has y_i>0. Its moment is strictly negative by
the first row of the table. Consequently
mu_1 m_1+mu_2 m_2<0. The actual leaf applies at p, so its moment
about p is zero. This contradicts the full root torque equation.

Thus no tilted S fork exists.

### 3.1. The D and tilted-S conclusions permit arbitrary root degree

There is a precise, size-independent extension of Sections 2--3.
Suppose every positive root force other than one genuine radial leaf
comes from a nonempty finite collection of actual normal channels of
reserve at least one. All their internal bodies must remain true
unloaded degree-two transmitters, and their far endpoints may have
arbitrary degrees and circle masks. Then the leaf cannot be D, and
its S root cannot be tilted.

For D, (10)--(11) apply separately to every channel. Vertical force
balance forces at least one upward and at least one downward channel.
Apply (12) just to that pair: its support sum still exceeds 14/15
and is at most 2delta. The other actual forces are not deleted from
the force equation which supplies the opposite-sign pair.

For tilted S, the complete moment table applies separately to every
channel. The sum of all their weighted second components equals
lambda b>0, so at least one channel has the strictly negative moment
in the first row. All other moments are nonpositive, contradicting
the unchanged full root torque equation. Neither extension requires
that a far endpoint touch the circle.

The aligned-S proof below retains the exact two-channel hypothesis.
Its pairwise force/torque identities must not be assigned to a root
with additional channel forces. Thus the full S/D theorem keeps the
true degree-three root premise of Section 1; only the two explicitly
proved leaf/root forms have the arbitrary-degree extension just stated.

## 4. Aligned S roots: neither channel can point right or vertically

The remaining full S root domain is

\[
                A=[\delta,d]\times[-b,a],\qquad
                a,b\ge0,\quad a+b=1,
\tag{20}
\]

with actual leaf application p=(d,0). Both endpoint sliders a=0 or
b=0 remain. Suppose one channel has nonnegative horizontal component.
Its horizontal component cannot be one with zero vertical component:
the only such unit direction is e, whose support d exceeds delta.
Reflect the whole configuration across the horizontal axis if needed
so this channel points upward. The force equation makes the other
channel point downward with strictly negative horizontal component.

Write their positive weighted components as

\[
 \mu_1n_1=(X,v),\qquad
 \mu_2n_2=(-Y,-v),\qquad
 X\ge0,\ v>0,\quad Y=X+\lambda>X.
\tag{21}
\]

Their true root applications are

\[
                     p_1=(\xi,a),\qquad
                     p_2=(\delta,-b),\qquad
                     \delta\le\xi\le d.
\tag{22}
\]

When X>0, xi=d; when X=0, the whole upper-side mean interval
is retained. The full torque equation about the actual leaf application
p gives exactly

\[
                  v(\xi-\delta)=aX+bY=X+b\lambda.
\tag{23}
\]

Because 0<=xi-delta<=1,

\[
                         v\ge X,\qquad v\ge bY.
\tag{24}
\]

The first inequality gives (n_1)_y>=1/sqrt(2). Its horizontal
support term is nonnegative, so (6) forces

\[
                    a\le\sqrt2\,\delta<\frac1{30},
                    \qquad b>\frac{29}{30}.
\tag{25}
\]

The second inequality of (24) gives

\[
 |(n_2)_y|=\frac{v}{\sqrt{Y^2+v^2}}
           \ge\frac{b}{\sqrt{1+b^2}}
           \ge\frac{b}{\sqrt2}>\frac23b.
\tag{26}
\]

Hence the second actual support satisfies

\[
 \begin{split}
 h_2&=-\delta|(n_2)_x|+b|(n_2)_y|\\
    &> -\delta+\frac23b^2
     >-\frac1{60}+\frac23\left(\frac{29}{30}\right)^2
      =\frac{1637}{2700}>\frac1{60}>\delta,
 \end{split}
\tag{27}
\]

contradicting (6). Thus both actual channel normals have strictly
negative horizontal component throughout (20).

## 5. Both aligned-S channel directions are within five degrees of west

If either channel's vertical component is zero, both are zero by
(3), so both actual unit directions are west. Otherwise, after
interchanging channels, write

\[
        n_1=(-\cos\phi,\sin\phi),\qquad
        n_2=(-\cos\psi,-\sin\psi),\qquad
                       0<\phi,\psi<\frac\pi2.
\tag{28}
\]

Their support applications are the actual upper-left and lower-left
vertices of A. The vertical force and torque equations give

\[
  \mu_1\sin\phi=\mu_2\sin\psi,\qquad
  a\mu_1\cos\phi=b\mu_2\cos\psi.
\tag{29}
\]

Thus a,b are both positive and

\[
                     a=\frac{\tan\phi}{\tan\phi+\tan\psi}.
\tag{30}
\]

If phi>=psi, then a>=1/2. The first channel's support bound is

\[
           -\delta\cos\phi+a\sin\phi\le\delta,
           \qquad a\sin\phi\le\delta(1+\cos\phi)\le2\delta.
\tag{31}
\]

Consequently sin(phi)<=4delta<1/15, and the same bound holds for
sin(psi). If psi>=phi, the identical argument uses b and the second
channel. This proves the whole-domain bound

\[
                      \phi,\psi<\frac\pi{36}.
\tag{32}
\]

Here is an elementary exact comparison for the last step. If
t=sin(pi/36), then 3t-4t^3=sin(pi/12)>1/4, whence t>1/12>1/15.
The inequality sin(pi/12)=(sqrt(6)-sqrt(2))/4>1/4 follows from
sqrt(6)>1+sqrt(2), or equivalently 3>2sqrt(2). Sine is strictly
increasing on [0,pi/2]. The west-parallel case also satisfies (32)
with both angles zero. No limit angle or mean has been discarded.

## 6. The two actual boundary endpoints would violate forty-degree separation

The root point (delta,0) belongs to (20). For either channel,
h_i>=delta(n_i)_x>=-delta. Therefore (4)--(7) give the strict
center bounds

\[
        n_i\cdot c_{Q_i}\ge h_i+w_i+\frac12
                      \ge\frac32-\delta>\frac{89}{60},
        \qquad |c_{Q_i}|\le\frac32+\delta<\frac{91}{60}.
\tag{33}
\]

Every endpoint center is nonzero, and its angular distance beta_i
from its channel direction satisfies

\[
                           \cos\beta_i>\frac{89}{91}
                                        >\cos\frac\pi{12}.
\tag{34}
\]

For the fixed second comparison, use sqrt(3)<7/4 to obtain
cos^2(pi/12)=(2+sqrt(3))/4<15/16, while
16 times 89^2=126736 is greater than 15 times 91^2=124215.
Both quantities being compared are positive. Thus beta_i<pi/12.

Combining (32) and (34), each endpoint center direction is at angular
distance strictly less than

\[
                       \frac\pi{36}+\frac\pi{12}=\frac\pi9
\tag{35}
\]

from west. Their mutual minor angular separation is therefore
strictly less than 2pi/9. But B,C are distinct interior-disjoint
physical circle-touching unit squares. CENTERED_INNER_ARC.md proves
that every such pair has minor center separation strictly greater
than 2pi/9 throughout (1). This contradiction excludes the whole
aligned S family.

This last argument uses physical circle contact only. It retains
two physical circle corners with unequal or zero individual weights
and physically boundary endpoints with zero total circle load. No
contact between B and C is needed for the local fork theorem.

## 7. Complete theorem and exact original C5 load-orbit join

Sections 2--6 exhaust every genuine leaf type and every root pose.

**Two-boundary-channel fork theorem.** Under the full premises of
Section 1, no physical selected certificate exists in (1).

In the original C5-plus-leaf graph, use cycle order

\[
                         0-1-2-3-4-0,
                  \qquad\hbox{with genuine leaf }0-L.
\tag{36}
\]

For the complete block-load representative 23, bodies 1 and 4 are
true unloaded degree-two transmitters. The physically clear root 0
has exactly its three actual positive edges to L,1,4. Its channels
are 0--1--2 and 0--4--3. Their distinct far endpoints 2,3 are
positively loaded and therefore physically circle-touching. All
premises of the fork theorem hold with their original forces, means
and occupied squares.

The entire original block-load orbit 23 is therefore excluded, with
both full leaf types. The exact pre-existing gates are

| Original gate | Complete whole-domain exit |
| --- | --- |
| M6.B5L.C5.L23.S | Sections 3--6, including all aligned and tilted S roots |
| M6.B5L.C5.L23.D | Section 2, with the full D side-interior root slider |

The reflection of the rooted C5 exchanges 1 with 4 and 2 with 3,
so it is already included. This exit is distinct from the earlier
12 and 14 channel/bypass exclusions in the original load cover.
It adds no new gate and does not close the other rooted-C5 load
orbits 13,123,124,1234 or the whole C1.5.b1 cell.

The root theorem also applies to larger components whenever the root
retains its true degree three, its two other edges begin the specified
unchanged normal channels, and the distinct far endpoints are physically
boundary. No endpoint force is deleted to arrange these premises, and
no larger coarse graph gate is inferred without its own exhaustive
original-family join.

All three original additional physical squares remain fixed and
arbitrary in the C5 application. The proof excludes the physical core
itself, so it requires no completion-capacity certificate. It uses no
pose sample, finite sign grid, Lean compilation or CI.

## 8. Size-independent propagation to a cycle with one genuine leaf

Suppose the entire positive component consists of a simple cycle C_k
and one genuine leaf at its root A. All other physical squares remain
arbitrary. At every nonroot cycle vertex the true positive degree is
two, and A has precisely its two cycle edges and the leaf edge.

The complete positive component has at least three positively
circle-loaded bodies, by the existing two-load component exclusion
TREE_AND_TWO_LOAD_COMPLETION.md. The leaf is loaded and A is
physically circle-clear. Hence at least two distinct nonroot cycle
vertices are positively loaded.

If both immediate cycle neighbors of A were unloaded, follow each
cycle direction from A until its first positively loaded vertex.
Every internal body on either path is an actual unloaded degree-two
transmitter, so the original force/torque equations make each path a
normal channel with reserve at least one. The two first loaded
endpoints are distinct: in the linear order obtained by cutting the
cycle at A they are the first and last loaded vertices, and at least
two loaded vertices exist. Both endpoints physically touch the circle.

All premises of Section 1 therefore hold, contradicting the fork
theorem. Consequently:

**Cycle-leaf neighbor-load corollary.** In every such positive
component, at least one of the leaf root's two immediate cycle
neighbors carries positive circle load.

The statement is independent of cycle length. Its original six-to-nine
body applications have the following exact physical counts:

| Exact positive graph | Positive component size | Other original physical units |
| --- | --- | --- |
| C5 with one genuine leaf | 6 | 3 |
| C6 with one genuine leaf | 7 | 2 |
| C7 with one genuine leaf | 8 | 1 |
| C8 with one genuine leaf | 9 | 0 |

For every row, the complete both-neighbors-unloaded load family is
excluded. Both full leaf types and every normal channel width and mean
remain covered. The C5 consequence in Section 7 is the first currently
open original load-orbit application.

This is a genuine simultaneous load-family exclusion, not a claim
that any whole larger cycle-leaf graph is closed. A chord, another
bridge attachment, or a positive force at an internal path vertex
can change its true degree and must be checked separately before
using the corollary. No extra original roadmap label is introduced
or counted by this propagation statement.
