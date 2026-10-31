# Every nonzero minimizing stress component must contain a cycle

**Status:** independently reviewed hand exclusion of the entire positive-tree
branch, with the lower-radius source stated explicitly. The classification,
physical-core construction and capacity inputs have separate mathematical
reviews. Positive components containing cycles remain open; no unrestricted
ten-square lower bound is claimed.

This note adapts three manuscripts from the n=9 branch, all read at the fixed
commit `901678d95a5197017db81343c7d0182661cc92fc`:

- [Tree body localization](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/TREE_BODY_LOCALIZATION.md).
- [Tree radius quantization](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/TREE_RADIUS_QUANTIZATION.md).
- [Finite tree completions](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/TREE_FINITE_COMPLETIONS.md).

Their smaller upper-radius window cannot simply be replaced by 9/2. An
additional five-body family occurs, and an explicit physical stress below
shows it is real.

## 1. The theorem and its hypotheses

Consider ten interior-disjoint unit squares in the origin-centered disk of
radius R, where

\[
                         79/40\le R\le3/\sqrt2.            \tag{1}
\]

At a minimizing packing, use the physical force-and-torque stress certificate
specified in [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md). In
particular off-origin point-only vertex/vertex positive edges are not bridges.
Let G be a nontrivial connected component of its positive aggregated body-pair
graph, and suppose G is a tree. The following results are conditional on that
graph hypothesis. They do not force a selected component to be a tree.

**Expanded tree theorem.** Before physical completion bounds are applied,
there are exactly these radius and incidence alternatives:

1. R^2=17/4. Every unloaded body has the origin on its boundary, every loaded
   body is a radial side terminal, and the numbers (s,v) of unloaded bodies
   with side-interior and vertex incidence at the origin are one of

   \[
                    (2,0),(1,1),(1,2),(0,2),(0,3),(0,4).
   \]

2. R^2=q_kappa, the exact value defined in Section 5. The component is the
   five-square family described there, with one transverse slide parameter.

**No-tree consequence.** No ten-square minimizer satisfying (1) can have
such a nontrivial positive tree component. The capacity theorems first reduce
the six boundary-incidence cases to the staggered four-square S-S chain;
[WIDE_NECK_THREE_POINT_STABBING.md](WIDE_NECK_THREE_POINT_STABBING.md)
excludes its ten-square completion. The complete bound in
[KAPPA_CORE_COMPLETION.md](KAPPA_CORE_COMPLETION.md) excludes the additional
five-body family. Section 7 also rules out isolated loaded bodies, so every
nonzero stress component has a cycle. Entirely unstressed squares are still
physical packing obstacles and are not claimed to lie on cycles.

The lower bound in (1) is an explicit premise, not a consequence of area.
A global application must supply it from a separately stated theorem.

**Declared existing-theorem route to that premise.** At main commit
`cd9127ff04e089909cc460d817ea28c4b1eb9ea9`,
[Eight.lower_bound and radius_eq_stationary](https://github.com/vltanh/lean4-squares-in-circles/blob/cd9127ff04e089909cc460d817ea28c4b1eb9ea9/SquaresInCircles/Eight/Uniqueness.lean)
give sqrt(qStar)<=R for any eight-square subpacking, while
[ExactFamily.qStar_limits](https://github.com/vltanh/lean4-squares-in-circles/blob/cd9127ff04e089909cc460d817ea28c4b1eb9ea9/SquaresInCircles/Eight/ExactFamily/Stationary.lean)
gives 7831/2000<qStar. Since

\[
                   7831/2000-(79/40)^2=119/8000>0,
\]

deleting two squares supplies R>79/40 for any ten-square packing. This is
an explicit dependency on the existing n=8 theorem and its stationary-radius
bracket. The bracket proof uses generated exact interval bounds in that
source; this paragraph does not claim a new independent hand proof of the
lower window or a new local Lean build.

## 2. Tree body localization in the enlarged window

Put

\[
 A=\sqrt{R^2-1/4}-1,\qquad B=R-\sqrt2,
 \qquad \delta=\max(R-2,0).
\]

The needed bounds throughout (1) are

\[
 \frac9{10}<A<\frac{17}{16},\qquad
 \frac12<B\le\frac1{\sqrt2}<\frac34,
 \qquad\delta<\frac18,
 \qquad A^2<\frac54.                                     \tag{2}
\]

For the upper A bound, sqrt(17)/2-1<17/16 is equivalent to
sqrt(17)<33/8, whose squares differ by 1/64. The lower A and B bounds
follow by substitution at 79/40. The other comparisons are immediate by
squaring. These replace the smaller constants in the n=9 source.

Every edge of G is a radial bridge. At a nonzero application point p=re,
orient its geometric labels so the inner square supports e dot x<=r and
the outer square lies in e dot x>=r. The outer square has p as its unique
nearest point to zero; the inner square meets the delta disk. A square
meeting that disk is circle-clear. At most four packing squares meet it,
by the bridge-cover theorem already proved in PHYSICAL_TREE_REDUCTIONS.

Every unloaded body of G meets the delta disk. Indeed, if it did not, it
would be outer at every incident bridge. All incident forces would act at
its unique nearest point, in the same direction and with the same sign;
without circle load they could not balance. Thus there are at most four
unloaded bodies. Loaded bodies are disjoint from that disk and are outer
at every incident edge. All their forces likewise share their nearest point.
Combining those parallel forces, the loaded-leaf proof applies unchanged:

| Loaded type | Center | Common inward application point |
| --- | --- | --- |
| S | (A+1/2)e | Ae |
| D | (B+1/sqrt(2))e | Be |

A D body has degree one: at its vertex contact every neighbor must contribute
a side interior, and two neighboring square half-plane tangent cones would
overlap. An S body has degree at most two. If it has two neighbors, they
contribute two right-angle tangent cones filling the opposite half-plane at
its inward side midpoint. A loaded body is not assumed to be a graph leaf
before this argument.

### 2.1 Every unloaded body avoiding zero is one side transmitter

Let U be an unloaded body that does not contain zero. At a radial outward
support point p, one of U's own center coordinates has absolute value greater
than 1/2. Reverse that axis to make its coordinate positive. Every point of U
has positive coordinate there, so support in the direction p uses the far
face and gives that coordinate of p greater than one. Hence ||p||>1.

U has an incoming bridge. Otherwise the unit vector toward its nearest point
has positive scalar product with all its outgoing radial forces, preventing
balance. Incoming forces all act at that nearest point and have one direction.
There must also be an outgoing force. Its neighbor cannot be unloaded, because
its nearest-point radius would exceed one, whereas every unloaded body meets
the delta disk. The neighbor is therefore an S terminal: B<1 rules out D.
Consequently A>1.

In U's own axes let its center be (x,y), with x>1/2. If |y|>1/2, an outgoing
support point would have both coordinate magnitudes greater than one, contrary
to A<sqrt(2). Thus |y|<=1/2, and the incoming force point is (x-1/2,0).
Outgoing points lie on x=x+1/2>1 and have norm A. A nonzero second coordinate
would be at a vertex. To balance vertical forces, both signs would have to
occur, and they would be the endpoints +/-1/2 of that side. This would give
A^2>(1)^2+1/4, contrary to (2).

All outgoing points therefore have second coordinate zero. The exact form is

\[
 c_U=(A-1/2)e+bJe,\quad |b|\le1/2,
 \qquad p_{in}=(A-1)e,\quad p_{out}=Ae.                    \tag{3}
\]

There is one outgoing S terminal, centered at (A+1/2)e; two distinct terminals
with this geometry would coincide. Every incoming neighbor contains zero.
Another origin-avoiding unloaded neighbor would have an outgoing point of
radius greater than one, whereas ||p_in||=A-1<1/16. A loaded neighbor has
contact radius A or B, also impossible there.

It follows that some unloaded body contains zero. There is an unloaded body
because a bridge cannot join two loaded bodies, and (3) supplies an origin-
containing predecessor whenever the first unloaded body avoids zero.

## 3. Boundary incidence still forces squared radius 17/4

First note that every D terminal has a neighbor containing zero in its open
interior. In coordinates with its radial direction horizontal, its inward
point (B,0) lies in the relative interior of its neighbor's right side. That
neighbor has horizontal interval [B-1,B], which contains zero strictly since
0<B<1, and its vertical interval contains zero strictly as well.

Suppose now that no unloaded body contains zero in its open interior. There
are no D terminals. Any contact between two origin-containing bodies has
application point zero: their separating line goes through zero, and radiality
makes the application point parallel to its normal. All other contact radii
on an origin-containing unloaded body are A, or, if A>1, a=A-1 from (3).

If A>1, put

\[
 a=A-1,\qquad c=\sqrt{A^2-1}.
\]

The enlarged-window bounds still give

\[
 0<a<1/16,\quad 0<c<3/8,\quad c>a,\quad a+c<1.            \tag{4}
\]

For a vertex-origin unloaded square, rotate its coordinates to [0,1]^2.
Its only nonzero radial outward support points are (1,0),(0,1),(1,1), of
radii 1,1,sqrt(2). Since 9/10<A<17/16 and a<1/16, only A=1 can match.
If A differed from one, all positive forces would act at zero, with normals
in the negative coordinate cone, and could not balance.

For a side-origin unloaded square, write it as

\[
                         [-\alpha,1-\alpha]\times[0,1],
                         \qquad0<\alpha<1.
\]

Its nonzero radial outward support points are the two bottom vertices,
(0,1), and the two top vertices. Forces at zero are vertical and downward.

- If A<1, an S contact can only be a bottom vertex with alpha=A or
  1-alpha=A. Since A>9/10, at most one of these holds. Its horizontal force
  cannot be canceled by the zero-point forces.
- If A>1, an S contact at a top vertex requires alpha=c or 1-alpha=c.
  A short arm at a bottom vertex requires alpha=a or 1-alpha=a. The four
  alternatives are pairwise incompatible by (4), so again there is at most
  one nonzero horizontal force direction and it cannot balance.

Thus any boundary-origin body forces A=1 and R^2=17/4. Formula (3) then
excludes all origin-avoiding unloaded bodies. All unloaded bodies have zero
on their boundaries, and every loaded body is an S terminal at (3/2)e.

There are at least two unloaded bodies: one would make the component a star,
excluded in this radius window by PHYSICAL_TREE_REDUCTIONS. If s of them
contain zero in a side interior and v at a vertex, disjoint tangent-cone
interiors give 2s+v<=4, while s+v>=2. This yields exactly the six pairs in
the theorem, including all side-parameter endpoints in the appropriate
vertex-incidence rows.

## 4. An origin-interior body produces one additional family

Suppose H contains zero in its open interior. No other packing square can
contain zero, even on its boundary. By (3), every other unloaded body is one
side transmitter from H to an S terminal. Shared loaded terminals between
two such arms, or between a direct and a two-edge arm, would create a cycle.
The component is therefore a star with some arms subdivided once.

If A<=1, or if no subdivided arm occurs, this is an ordinary star, excluded
by the no-star theorem because 79/40>sqrt(2)+1/2. Thus A>1 and H has a radial
support point of radius a=A-1, where 0<a<1/16. All its positive contact radii
are a, A, or B.

### 4.1 The short-arm contact cannot be a vertex

If that point is a vertex, choose H's signs so

\[
 p=(p_1,p_2),\quad p_1,p_2>0,\quad p_1^2+p_2^2=a^2,
 \qquad H=[p_1-1,p_1]\times[p_2-1,p_2].
\]

The adjacent vertices have radii strictly between 1-a and sqrt(1+a^2):
larger than B and a, and smaller than A=1+a. The opposite vertex has squared
norm greater than 2(1-a)^2>A^2, using a<1/16. The side distances are p_i<a
and 1-p_i in (1-a,1); none equals a,A, or B, because B<3/4<1-a.
The sole possible positive contact direction on H would be that of p,
which cannot balance. This vertex case is excluded.

### 4.2 The side-interior contact forces a fifth body and an exact radius

Put its side-interior contact at (a,0), and write

\[
                 H=[a-1,a]\times[t,t+1],\qquad -1<t<0.
\]

A direct S contact cannot lie in a side interior, whose distance from zero
is less than one. At a right vertex, radius A would require vertical magnitude
sqrt(A^2-a^2)=sqrt(1+2a)>1, impossible. At a left vertex it requires vertical
magnitude

\[
                              d=2\sqrt a<1/2.             \tag{5}
\]

Both signs cannot be vertices because their gap 2d is less than the side
length one. Hence at most one S contact exists on H.

D contacts can only be on horizontal sides: vertical-side distances a and
1-a are different from B. Other short arms also have vertical normals; no
other vertex can have radius a, and the opposite vertical side has distance
1-a. The known short arm has a positive horizontal force, so an S contact
at the left vertex must occur to balance it. Reflect vertically so that it
is at (a-1,d). Now H has vertical interval [d-1,d].

The S force has a positive vertical component. There is no second S contact.
A downward short arm would require 1-d=a, impossible because 1-d>1/2>a.
A downward D contact is therefore necessary and forces

\[
                         B=1-d,
              \qquad B+2\sqrt{A-1}=1.                     \tag{6}
\]

There is no additional upward D contact because d<1/2<B. An upward short
arm would require d=a, impossible for 0<a<1/16 and d=2sqrt(a). Thus H has
exactly three positive contact directions: the right short arm, the upper-
left S terminal, and the downward D terminal.

There is only one right transmitter. Two would lead to the same right S
terminal by (3), giving a cycle H-U_1-S-U_2-H. The component consequently
has exactly five bodies.

The decisive difference from the n=9 window is (6): there, the inequality
1-d>B ruled out this final downward force. In the present window it can
hold with equality, so discarding it would make the classification false.

## 5. Exact five-body family, complete slide range, and a positive stress

Let d be the unique positive root of

\[
             d^4+32(1+\sqrt2)d+20-32\sqrt2=0.              \tag{7}
\]

The polynomial is strictly increasing for d>=0, negative at 8/25 and
positive at 1/3. These signs follow using 7/5<sqrt(2)<10/7. Therefore

\[
                         8/25<d<1/3.
\]

Define

\[
 a=d^2/4,\quad A=1+a,\quad B=1-d,\quad
 R_\kappa=1+\sqrt2-d,\quad q_\kappa=R_\kappa^2.            \tag{8}
\]

Equation (7) gives

\[
                         R_\kappa^2=(2+a)^2+1/4,
\]

so (8) is exactly equivalent to (5)-(6). In particular
17/4<q_kappa<9/2. Numerically q_kappa is approximately 4.35748157034;
this approximation is not used in any proof.

Put

\[
 C=(1-a)/A,\qquad S=d/A,\qquad n=(-C,S),\qquad k=1/\sqrt2.
\]

Here C^2+S^2=1 because (1-a)^2+d^2=(1+a)^2. The complete five-square
family, up to rotation and reflection, consists of:

| Body | Center | Orientation |
| --- | --- | --- |
| H | (a-1/2,d-1/2) | Coordinate axes |
| U | (A-1/2,b) | Coordinate axes |
| E | (A+1/2,0) | Coordinate axes; radial S terminal |
| L | (A+1/2)n | Side axes n,Jn; radial S terminal |
| D | (0,-(B+k)) | Diagonals on the coordinate axes; radial D terminal |

The exact transverse parameter range for physical nonoverlap is

\[
                        d-1/2-a\le b\le1/2.              \tag{9}
\]

### 5.1 Verify all physical constraints

H is the rectangle [a-1,a]x[-B,d], and U is [a,A]x[b-1/2,b+1/2]. Their
shared side contains (a,0). U and E similarly share a vertical side containing
(A,0). H and L are supported at H's upper-left vertex (a-1,d)=An with normal
n; it is the midpoint of L's inward side. H and D meet at (0,-B), the top
vertex of D and a relative side-interior point of H.

The remaining pairs except U,D separate in coordinates. L's rightmost
coordinate is a-1+S/2<0, so it is left of U and E. L's bottom coordinate
is d-C/2>-B, so it is above D. E's left coordinate A>1 exceeds D's right
coordinate k<1. H and E have a horizontal gap.

Only U,D require the parameter condition. D is the diamond

\[
                         |x|+|y+B+k|\le k.
\]

For a<=x<=k its upper boundary is y=-B-x. Since U's top is nonnegative,
it avoids D exactly when its bottom is at least -B-a. This is
b>=1/2-B-a=d-1/2-a. If the inequality fails, points with x>a sufficiently
close to a and just below that diamond boundary lie in both interiors.
Together with the contact requirement |b|<=1/2, this proves (9).

All five squares lie in D_(q_kappa). H lies inside (-1,1)^2, while U's
largest squared vertex norm is at most A^2+1<q_kappa. The two S terminals
have outer vertices of squared norm (A+1)^2+1/4=q_kappa, and the D terminal's
outer diagonal vertex has norm R_kappa. Its other vertices are nearer.
Thus every parameter in (9) gives an actual physical packing of these five
squares.

### 5.2 Exhibit a positive physical tree stress

Use the four positive body-pair edges H-U, U-E, H-L, H-D at the actual
points (a,0),(A,0),An,(0,-B), respectively. Assign contact magnitudes

\[
                       C,\quad C,\quad1,\quad S.
\]

The forces on H balance because

\[
                              C(1,0)+n+S(0,-1)=0.
\]

The equal opposing forces on U balance on the horizontal line through zero.
On the loaded squares give total circle weights

\[
          \lambda_E=\frac{C}{2(A+1)},\qquad
          \lambda_L=\frac1{2(A+1)},\qquad
          \lambda_D=\frac{S}{2R_\kappa}.
\]

For each S terminal split its weight equally between its two outer circle
vertices; D has its one outer diagonal vertex. These circle resultants
balance the corresponding contact forces. Every force application line is
radial, so moments about the origin vanish, and force balance then gives
torque balance about each body center. Normalize all weights by the positive
sum lambda_E+lambda_L+lambda_D to obtain total circle weight one.

The four positive edges form a tree. There is no off-origin point-only
vertex/vertex edge. At the lower endpoint of (9), U and D may acquire an
additional contact, but it has zero stress in this certificate. This explicit
certificate verifies the exceptional family's physical meaning; it does
not show that a ten-square completion exists or that the five-square packing
is globally optimal for five squares.

## 6. Capacity reductions at squared radius 17/4

The six boundary-origin rows reduce as follows for ten squares:

| Origin incidences (s,v) | Ten-square completion outcome |
| --- | --- |
| (2,0) | The four-square S-S staggered chain; total capacity at most nine |
| (1,1) | Three-or-more loaded terminals excluded; two loaded bodies give the same excluded chain boundary |
| (1,2) | Capacity at most eight by the cardinal-cage theorem |
| (0,2) | Capacity at most nine by the two-origin-vertex theorem |
| (0,3) | Capacity at most eight by the three-origin-vertex theorem |
| (0,4) | Capacity at most eight by the central-block theorem |

For (2,0), the two origin-side tangent half-planes are complementary. Their
axes agree, each body's only radius-one radial outward support point is its
outer side midpoint, and the component is exactly the S-S chain. The (1,1)
row follows from
[ONE_ORIGIN_VERTEX_THREE_TERMINALS.md](ONE_ORIGIN_VERTEX_THREE_TERMINALS.md)
and the two-loaded tree theorem. The (0,2) and (0,3) rows are the independently
proved bounds in
[THREE_ORIGIN_VERTEX_SQUARES.md](THREE_ORIGIN_VERTEX_SQUARES.md).

For completeness, the two remaining capacity imports from the pinned
finite-completions source have unchanged hypotheses q=17/4:

- Four origin-vertex bodies fill a central solid block [-1,1]^2. Any
  additional center has norm at most 3/2 and distance at least 1/2 from
  that block, leaving only (+/-3/2,0),(0,+/-3/2). Equality in the center
  radius inequality aligns each additional square, so total capacity is eight.
- In (1,2), the origin cones fill the entire angle. The side-origin body
  forces the upper cardinal S terminal; global circle-force balance forces
  the lower one. If no horizontal terminal occurred, the tree would have
  two loaded bodies but three unloaded bodies, contradicting the two-loaded
  path theorem. Thus all four cardinal terminals are present. The pinned
  cardinal-cage theorem allows at most four additional squares, without
  orientation assumptions, and gives capacity eight.

The cardinal-cage proof uses inscribed-disk clearance to put any extra center
in [-1/2,1/2]^2 or a diagonal pocket x,y>=1, up to signs. In a diagonal pocket,
write its frame (c,s),(-s,c), c>=s>=0. Avoiding the upper cardinal obstacle
forces x>=1/2+(c+s)/2. Its upper-right vertex then has squared norm at least

\[
 (1/2+c)^2+(1+(c+s)/2)^2
 =3/2+(2c+s)+(c^2+cs/2)>17/4,
\]

because 2c+s>=2 and c^2+cs/2>=3/4 cannot both be equalities. Thus no diagonal
pocket is possible. Four half-unit center quadrants in the central box each
have diameter below one, giving the claimed additional capacity four.

## 7. Exclude every nonzero tree component and retain the cyclic gap

The independently reviewed theorem in
[KAPPA_CORE_COMPLETION.md](KAPPA_CORE_COMPLETION.md) proves total capacity
at most nine for every member of (8)-(9), including all independently
oriented additional squares. The exceptional family is therefore fully
excluded from a ten-square packing.

The other remaining family is now excluded by
[WIDE_NECK_THREE_POINT_STABBING.md](WIDE_NECK_THREE_POINT_STABBING.md): every
staggered four-square S-S chain at q=17/4 has total capacity at most nine.
This counts every unstressed additional square. Therefore all nontrivial
positive tree components in (1) are excluded.

To state the graph consequence precisely, call a component **stress-supported**
if one of its bodies has a positive contact force or positive circle weight.
A component with a positive edge cannot have total circle weight zero. Dot
each body's force balance with its center and sum over that component. With
zero circle load the result would be

\[
                  0=-\sum_e\mu_e\bigl(h_i(d_e)+h_j(d_e)\bigr)<0,
\]

where the h_i are the squares' directional halfwidths and every mu_e is
positive. This is impossible.

An isolated loaded body is impossible as well. Its force balance says that
zero is a positive weighted mean of its circle-contact vertices. Thus the
square contains the origin. But its circle-contact vertex is distance R
from zero, exceeding the square diameter sqrt(2) under (1). An isolated
body with no circle weight and no contact force is entirely unstressed and
is outside the asserted stress support; it remains part of the packing.

Every stress-supported component therefore has at least one edge. The
no-tree theorem forces it to contain a cycle. Normalization gives positive
total circle weight, so at least one such cyclic component exists.

This does not prove that every positive edge lies on a cycle: a cyclic
component may still contain bridges and attached trees. It also does not
make the simple body-pair graph planar; the separate contact-incidence
network is the planar object. Those distinctions remain necessary for the
next argument.

The declared n=8 source supplies the lower window, leaving the physically
realizable cyclic stress components and all their unstressed-square
completions as the remaining stress-route gap. An assembly insisting on a
fresh independent hand proof of the lower window would additionally need
to replace that declared source dependency.
