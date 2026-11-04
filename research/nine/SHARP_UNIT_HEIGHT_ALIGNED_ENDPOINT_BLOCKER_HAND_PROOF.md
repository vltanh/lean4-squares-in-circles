# A sharp unit-height blocker at an aligned endpoint

November 4, 2026 (UTC). This is a separate strengthening of the previously
frozen `1/8` blocker. It leaves that source and its exact companion unchanged.
It is a local physical theorem, not a complete mask exclusion.

## 1. The exact theorem

Let D, X and G be actual aligned unit squares with centers

\[
D=(1,0),\qquad X=(0,v),\qquad G=(1/2,-1),\qquad 0\le v\le1.
\]

Then no fourth physical unit square C, with arbitrary independent frame,
can be disjoint in open interior from D, X and G and satisfy the strictly
weak original center-cone comparison C→D:

\[
d:=1-x\ge |y|,\qquad d<h+1/2,                         \tag{1}
\]

where C has center \((x,y)\) and actual horizontal/vertical halfwidth h.
All physical contacts and both endpoints of the v interval are included.
The upper constant 1 is sharp: Section 5 gives physical counterexamples
with v arbitrarily close to 1 from above, retaining strict weakness.

For C's original frame set

\[
a\ge b\ge0,\quad a^2+b^2=1,\quad
h=(a+b)/2,\quad j=(a-b)/2.
\]

Thus \(h+j=a\le1\), \(h-j=b\), \(0\le j\le1/2\), and
\(1/2\le h\le1/\sqrt2<1\). Its top and bottom vertices have coordinates
\((x\pm j,y\pm h)\), with opposite horizontal signs; its rightmost vertex
has coordinates \((x+h,y\pm j)\). These alternatives retain both physical
chiralities. At a horizontal or vertical side face, the corresponding
endpoints of that face have the displayed forms.

Every pair of disjoint physical unit squares has center distance at least
one, because of their contained open radius-1/2 disks. Applied to C,D and
the cone in (1), this gives

\[
d\ge1/\sqrt2>0,\quad x<1,
\quad x>1/2-h>-1/2.                                  \tag{2}
\]

## 2. The rectangle already occupied by D and G

The aligned squares D and G together contain the open rectangle

\[
U=(1/2,1)\times(-3/2,1/2).                            \tag{3}
\]

Away from its horizontal seam y=-1/2, each point of U is in the open
interior of D or G. No point of the closed C can lie inside U. Indeed any
such point has nearby points in the open interior of C still inside U;
one can choose one off the seam, contradicting physical nonoverlap.
This argument keeps contact faces weak and does not treat the seam itself
as an interior point of either individual aligned square.

There is a useful boundary version: if a rightmost vertex R of C lies in
\((1/2,1]\times(-3/2,1/2)\), and C's center has x<1, then C also meets U
in open interior. For R_x<1 this follows immediately. For R_x=1, a strict
segment point sufficiently close to R on the segment to C's center has
horizontal coordinate in (1/2,1) and retains a vertical coordinate strictly
between -3/2 and 1/2. It is interior to C. An arbitrarily small perturbation
inside C and U avoids the seam if needed.

## 3. The complete case x<=0

If x<=0, strict weakness gives x>1/2-h. Hence both the top and bottom
vertices have horizontal coordinates strictly between -1/2 and 1/2:

\[
x-j>1/2-h-j=1/2-a\ge-1/2,
\]

and \(x+j\le j\le1/2\), with equality impossible. Such equality would
require x=0,j=1/2,h=1/2, contradicting x>1/2-h. The open segment joining
these opposite vertices is interior to C and lies in X's open horizontal
strip. Physical nonoverlap with X therefore requires

\[
y+h\le v-1/2\quad\hbox{or}\quad y-h\ge v+1/2.       \tag{4}
\]

The cone and strict weakness give

\[
y-h\le1-x-h<1/2\le v+1/2,
\]

so only the first alternative in (4) remains. Since v<=1,

\[
y+h\le1/2.                                          \tag{5}
\]

In this case b>0: b=0 would imply a=1,h=1/2 and then x>0 by strict
weakness. Let R=(x+h,y+epsilon*j) be a rightmost vertex of C. Then

\[
1/2<R_x\le h<1,
\]

\[
R_y\le y+j\le1/2-h+j=1/2-b<1/2,
\]

and the lower cone bound gives

\[
R_y\ge y-j\ge x-1-j
>1/2-h-1-j=-1/2-a\ge-3/2.                            \tag{6}
\]

Thus R lies in U, contradicting Section 2. Every equality in the allowed
physical contact or v bounds has been retained.

## 4. The complete case x>0

First suppose y>=0. C,D center separation gives

\[
y^2\ge1-(1-x)^2=2x-x^2>x^2,
\]

because 0<x<1. Hence y>x. The original cone also gives y<=1-x. For every
0<=v<=1, the convex function \(v\mapsto|y-v|\) is bounded by its endpoint
maximum, so

\[
|y-v|\le\max\{y,1-y\}\le1-x.
\]

Consequently C,X have

\[
|c_C-c_X|^2\le x^2+(1-x)^2=1-2x(1-x)<1,
\]

a contradiction. Thus y<0.

For the actual rightmost vertex R=(x+h,y+epsilon*j), (2) and
\(h\le1/\sqrt2\le d\) give

\[
1/2<R_x=x+h=1-d+h\le1.
\]

Also

\[
R_y\le y+j<j\le1/2,
\qquad
R_y\ge y-j\ge x-1-j>-3/2,                            \tag{7}
\]

where the last strict inequality uses x>0 and j<=1/2. Therefore R lies in
the boundary strip covered by Section 2, and C's center satisfies x<1.
This again contradicts nonoverlap with D,G.

The delicate endpoint R_x=1 is included explicitly. It can occur when the
original C frame is diagonal and the C,D center-distance lower bound is
equality; the strict segment construction in Section 2 still enters U.
Together with Section 3, this exhausts the entire original-frame domain.

## 5. The upper height constant is sharp

The following exact family demonstrates that a larger v bound cannot be
asserted from these local physical hypotheses alone. Choose any rational
half-angle parameter t with 0<t<=2/5 and put

\[
a=\frac{1-t^2}{1+t^2},\qquad b=\frac{2t}{1+t^2},\qquad
h=(a+b)/2,\qquad j=(a-b)/2,\quad r=1/2+h,
\]

\[
\varepsilon=b^2/100,\quad
y=1/2-j+\varepsilon,\quad
d=r-\frac{b\varepsilon}{a},\quad
x=1-d,\quad v=y+r=1+b+\varepsilon.                   \tag{8}
\]

C has original frame \(u_C=(a,-b),v_C=(b,a)\). All other squares are
aligned at their stated centers. The denominator a is positive and
a>=b throughout the chosen parameter interval.

The identity

\[
b(1/2-j)=r(1-a)
\]

gives \(a d+b y=r\). Thus C,D are physically separated on C's actual
owned axis \((a,-b)\), exactly at contact. Their projection gap remains
strictly weak because \(r-d=b\varepsilon/a>0\). The center cone holds:

\[
d-y=a-\varepsilon(1+b/a)>0,
\]

using a>=7/10, b/a<=1 and epsilon<=1/200. Also y>0, so d>|y|.

X,C have exact vertical projection gap \(v-y=r=h+1/2\).
G,C have vertical projection gap

\[
y+1-r=1-a+\varepsilon>0.
\]

The three aligned pairs D,X; D,G; X,G also separate on coordinate axes.
Thus all four original physical units have disjoint interiors. Every t>0
has v>1, and v tends to 1 as t tends to zero. This is a local sharpness
control, not a packing in the original Q disk and not a counterexample to
any full-nine mask theorem.

The weak marked-equality face must also remain: at v=1, aligned C=(0,0)
is disjoint from aligned D=(1,0), X=(0,1), G=(1/2,-1), and obeys the C→D
cone with gap exactly h+1/2=1. It is excluded only by the retained strictly
weak CD predicate.

## 6. Permitted use in the full caller

The already frozen near-horizontal full-caller theorem is an immediate
special case. More generally, once an accepted original B–X–D row/cap
argument proves equality, aligns X,D,G, gives x_D-x_X=1 and the cap pair
G=(x_D-1/2,y_D±1), it suffices to retain

\[
|y_X-y_D|\le1.
\]

Common vertical reflection selects G below D. Put v=y_X-y_D. Since
\(-1\le v\le1\), their signed vertical center gap v+1 is in [0,2].
Their horizontal center gap is 1/2, so physical aligned X/G separation
requires \(|v+1|\ge1\). It follows that v>=0. Thus the whole closed
bound |y_X-y_D|<=1 is safe.
The blocker then excludes the unchanged original C with its strict weak
cone into D, without assuming actual BC, a large CD height gap, or a
preassigned G-height sign.

This is an equality terminal. It does not itself produce the preceding
row inequality, its signed cap prerequisites, or a universal routing of
all nine originals into such a row. Those must remain explicit in every
caller. No original-cell or mask closure is claimed. No Lean, Lake or CI
was run.

## Committed evidence

[Portable exact companion and independent controls](computer_assisted/sharp_unit_height_blocker.tar.xz) ·
[Source and archive identities](computer_assisted/sharp_unit_height_blocker_manifest.json) ·
[Fresh root replay](computer_assisted/sharp_unit_height_blocker_root_replay.json) ·
[Independent continuous proof review](SHARP_UNIT_HEIGHT_BLOCKER_INDEPENDENT_REVIEW.md).

Extract and run `python -B -S verify_all.py` from `sharp_unit_height_blocker`.
The root separately extracted the archive, checked every frozen input and
replayed both exact companions. The normalized complete report is
byte-identical to the author's and independent relocated reports.
The continuous geometric proof supplies the exclusion; finite exact
controls verify its algebra and stated contact and sharpness examples.
