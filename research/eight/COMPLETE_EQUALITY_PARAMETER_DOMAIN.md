# The complete equality family: five rigid squares and an explicit five-parameter domain

## 1. The classification and its input

Let \((q_*,y_*,t_*)\) be the unique admissible stationary solution
selected by [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md).
The selected squared radius is approximately
\(3.91553413751747532652\); the decimal is not its definition.

The following classification uses the unrestricted terminal capture as
an input. That input is proved in the exact computer-assisted
[unrestricted assembly](UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md). Its
replacement by a hand proof is the remaining global hand gate. The
classification and the parameter calculations in this note are hand
arguments; they introduce no further search or subdivision premise.

**Equality theorem.** Up to a Euclidean isometry and relabeling, every
packing of eight unit squares attaining the least radius
\(R_* = \sqrt{q_*}\) is exactly one of the configurations in the
explicit parameter domain (8) below. Conversely, every parameter choice
in (8) gives an attaining packing.

There is one stationary radius, position, and outer tilt. Five exterior
squares are rigid; the other two exterior squares translate in prescribed
directions. The eighth square can both translate and rotate. The full
family has five continuous parameters and contains the open box proved
in Section 6. In particular, equality does not specify an isolated
packing, even after isometries and relabeling are factored out.

All terminating decimals below are exact rational numbers.

## 2. The five anchors and two exterior sliders

Use the following exact quantities:

\[
\begin{aligned}
x_1&=\sqrt{q_*-y_*^2},&
x_2&=\sqrt{q_*-(y_*+2)^2},&x_3&=x_2-3,\\
y_3&=\sqrt{q_*-x_3^2},&y_4&=y_3-2,&
x_4&=-\sqrt{q_*-y_4^2},\\
c&=\cos t_*,&s&=\sin t_*,&
e&=(c,s),\quad f=(-s,c),\\
h_1&=cx_1+sy_*-2-c,&
h_2&=-sx_4+cy_4-1-s.&
\end{aligned}                                                    \tag{1}
\]

A unit square with center \(P\) and frame \(\alpha\) is
\(P+[-1/2,1/2]e_\alpha+[-1/2,1/2]f_\alpha\), where
\(e_\alpha=(\cos\alpha,\sin\alpha)\) and
\(f_\alpha=(-\sin\alpha,\cos\alpha)\).

The centers and frames of the seven exterior squares are:

| Square | Center | Frame |
|---|---|---|
| \(A\) | \((x_1-1/2,y_*+1/2)\) | \(0\) |
| \(B\) | \((x_2-1/2,y_*+3/2)\) | \(0\) |
| \(D\) | \((x_3+1/2,y_3-1/2)\) | \(0\) |
| \(E\) | \((x_4+1/2,y_4+1/2)\) | \(0\) |
| \(H\) | \((h_1+1/2)e+(h_2+1/2)f\) | \(t_*\) |
| \(T\) | \((x_2-3/2,z)\) | \(0\) |
| \(G\) | \(P_H+e+\eta f\) | \(t_*\) |

Write \(x_c=x_2-3/2\). Define three explicit constants:

\[
\boxed{
z_+=\sqrt{q_*-(x_c+1/2)^2}-\frac12,\qquad
\eta_-=-h_2-\sqrt{q_*-(h_1+2)^2},\qquad
\eta_+=-h_2-\frac{13}{12}.}
                                                               \tag{2}
\]

Their approximate values are \(z_+=1.36599564\),
\(\eta_-=-.44504969\), and \(\eta_+=.34665361\).
These approximations play no role in the definition.

The necessary exterior ranges are

\[
\boxed{\frac7{12}\le z\le z_+,\qquad
       \eta_-\le\eta\le\eta_+.}                              \tag{3}
\]

Section 4 proves both necessity and that these ranges already ensure
containment and every one of the 21 exterior pair separations. The
remaining restrictions are precisely the seven explicit inequalities
involving the eighth square.

## 3. A parameter domain with no unquantified geometric conditions

Give the central square center \((x,y)\). A single quarter-turn
fundamental interval for its frame is parametrized by

\[
1-\sqrt2\le w<\sqrt2-1,\qquad
C=\frac{1-w^2}{1+w^2},\qquad S=\frac{2w}{1+w^2}.
                                                               \tag{4}
\]

Thus its frame is \(\theta=2\arctan w\), with
\(-\pi/4\le\theta<\pi/4\), and its two unit axes are
\((C,S)\) and \((-S,C)\). Capital \(S\) in this note is a sine;
it is not the terminal proof's mismatch sum.

For a vector \(d=(d_x,d_y)\), define the following elementary functions:

\[
\begin{aligned}
M_0(d)&=\max\{|d_x|,|d_y|,|Cd_x+Sd_y|,|-Sd_x+Cd_y|\},\\
M_t(d)&=\max\{|cd_x+sd_y|,|-sd_x+cd_y|,
                         |Cd_x+Sd_y|,|-Sd_x+Cd_y|\},\\
W_0&=\frac{1+C+|S|}{2},\\
W_t&=\frac{1+cC+sS+|cS-sC|}{2}.
\end{aligned}                                                   \tag{5}
\]

The omitted absolute value around \(cC+sS\) is justified:
\(|\theta-t_*|<\pi/2\), because \(t_*<.125\) and
\(-\pi/4\le\theta<\pi/4\). Also \(C>0\).

Let

\[
d_i=P_i-(x,y),\qquad i=A,B,D,E,H,T,G,                           \tag{6}
\]

where every \(P_i\) is the explicit expression in the preceding table.
There are no unspecified centers in (6).

The central-core inequalities are

\[
|Cx+Sy|<\frac5{12},\qquad |-Sx+Cy|<\frac5{12}.                 \tag{7}
\]

Here is the complete parameter domain:

\[
\boxed{
\begin{gathered}
1-\sqrt2\le w<\sqrt2-1,\qquad
\frac7{12}\le z\le z_+,\qquad
\eta_-\le\eta\le\eta_+,\\
|Cx+Sy|<\frac5{12},\qquad |-Sx+Cy|<\frac5{12},\\
M_0(d_A),M_0(d_B),M_0(d_D),M_0(d_E),M_0(d_T)\ \ge W_0,\\
M_t(d_H),M_t(d_G)\ \ge W_t.
\end{gathered}}                                                 \tag{8}
\]

The notation in each of the last two lines means that every listed
quantity satisfies the bound. All five free real numbers are
\((x,y,w,z,\eta)\); all other numbers are fixed by (1)--(2).

Formula (8) is an exact, finite description of the full joint domain,
including its boundary contacts and every possible central frame. It
requires only evaluating the displayed radicals, rational functions,
absolute values and maxima. In particular, it has no existential pose,
unlisted separating-axis choice, root search or optimization instruction.
For a fixed \(w\), it is a finite union of explicitly given intersections
of linear halfplanes in \((x,y,z,\eta)\): each of the seven maximum
inequalities is a disjunction of its eight signed linear inequalities.
If a polynomial form is preferred, separate at \(w=0\) and
\(w=\tan(t_*/2)\), and multiply by \(1+w^2>0\).
The result is a finite semialgebraic domain with fixed algebraic
coefficients.

The domain is allowed to have different contact patterns and different
components. No assertion that all central orientations form one interval,
or that the free parameters form an independent rectangle globally,
is needed or used.

## 4. Proof of the exterior range theorem

### 4.1. Necessity

The independently reviewed
[equality pullback](EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md) retains the
initially selected signed witnesses through the boundary deformation,
then reapplies the stationary dual directly to the original centers.
It proves (1) and the center/frame table for the original packing.
It also retains the cyclic order \(H,G,A,B,T,D,E\).

The original central square contains the closed radius-\(1/12\) disk in
its open interior. Every exterior square consequently avoids that disk.
The sector between the rays of \(B,D\) lies in the upper halfplane;
therefore \(z>0\). The sector from \(H\) to \(A\) lies in
\(f\cdot P<0\); therefore \(f\cdot P_G<0\). These sector statements
follow, for example, from the strict coordinate bounds in Section 5.
Their bounding rays have counterclockwise gaps less than \(\pi\).

Now \(0<x_c<1/2\). The distance from the origin to square \(T\)
is \(\max(z-1/2,0)\). Core avoidance gives \(z\ge7/12\).
Containment is equivalent to

\[
(x_c+1/2)^2+(z+1/2)^2\le q_*,
\]

which gives its upper bound in (3).

In its own frame, the center of \(G\) is

\[
\xi=h_1+\frac32\in(0,1/2),\qquad
\zeta=h_2+\frac12+\eta<0.
\]

Core avoidance gives \(\zeta\le-7/12\), or
\(\eta\le\eta_+\). Its farthest squared vertex norm is

\[
(\xi+1/2)^2+(-\zeta+1/2)^2
  =(h_1+2)^2+(-h_2-\eta)^2.
\]

Because \(-h_2-\eta>0\), containment gives
\(\eta\ge\eta_-\). This proves (3). The weak core endpoints
are harmless: the strict inequalities (7) and the actual separation
conditions in (8) automatically exclude an exterior square touching
the radius-\(1/12\) disk.

### 4.2. Sufficiency for all seven exterior squares

The four standard anchors \(A,B,D,E\) and the tilted anchor \(H\)
are contained. Their farthest vertices are the five points defining
the stationary family, all of norm \(\sqrt{q_*}\). The signs needed
to select those vertices follow from Section 5. The two calculations
above prove containment of \(T,G\) throughout (3).

The five standard squares \(A,B,T,D,E\) form three separated columns.
Indeed \(x_1>x_2\) and \(-x_4>3-x_2\). The intervals of \(T\)
are bounded horizontally by \(x_2-2,x_2-1\); \(D\)'s right edge
is \(x_2-2\), and \(B\)'s left edge is \(x_2-1\). The other
two column edges are farther away. Within the left and right columns,
\(D,E\) and \(A,B\) have exact vertical contacts. These facts cover
all ten pairs among the five standard squares, independently of \(z\).

Put \(W=(1+c+s)/2\). The exact center identities

\[
e\cdot(P_G-P_H)=1,\quad
e\cdot(P_A-P_G)=W,\quad
e\cdot(P_A-P_H)=W+1,\quad
f\cdot(P_E-P_H)=W                                      \tag{9}
\]

give four further pair separations. They follow directly by substituting
(1), and hold for every \(\eta\).

For \(E,G\), the leftmost horizontal coordinate of \(G\) decreases
with \(\eta\). At \(\eta=\eta_+\), it is

\[
c(h_1+1)+\frac{s}{12}>-.355,
\]

whereas the right edge of \(E\) is \(x_4+1<-.90211\).
Thus these squares are separated horizontally throughout (3).

Finally the top of \(H\) is
\(s(h_1+1)+c(h_2+1)<0\). The top of \(G\) increases with
\(\eta\); its maximum over (3) is

\[
s(h_1+2)-\frac{c}{12}<-.004<0.                         \tag{10}
\]

The bottoms of \(B,D,T\) are all positive: respectively
\(y_*+1\), \(y_3-1\), and \(z-1/2\ge1/12\).
This separates each of \(H,G\) from each of \(B,D,T\), giving
the last six pairs. The count is \(10+4+1+6=21\).

### 4.3. Completion of the equivalence

For a unit square, the sum of half-widths along any one of the two
squares' axes is
\((1+|\cos(\theta-\alpha)|+|\sin(\theta-\alpha)|)/2\).
The separating-axis theorem therefore gives exactly (5), (8) for each
central/exterior pair, with weak inequalities correctly allowing boundary
contacts. These are the remaining seven pairs, so all 28 are covered.

The conditions (7) say exactly that the central square contains the
closed radius-\(1/12\) disk in its open interior. They also make
central containment automatic: its farthest squared vertex norm is

\[
(|Cx+Sy|+1/2)^2+(|-Sx+Cy|+1/2)^2
 <2(11/12)^2=\frac{121}{72}<q_*.
\]

Thus (8) is sufficient for an actual eight-square packing in the
radius-\(R_*\) disk. It attains the least radius by the unrestricted
lower bound and the five fixed boundary vertices. Necessity follows
from the equality pullback, (3), the central-core theorem, the quarter-turn
frame convention and the same separating-axis theorem. This proves
the classification, with precisely the global input stated in Section 1.

## 5. Short rational bounds used in the classification

For completeness, all numerical inequalities used above are consequences
of eight displayed radical brackets and the broad terminal's ordinary
strong-convexity estimate. This also proves the nontrivial interior
example in the next section without assuming a numerically isolated root.

The hand [sharp radius bracket](HUMAN_SHARP_CEILING_BRACKET.md) implies
\(3.9155341<q_*<3.9155342\). At the rational test values

\[
\bar y=-.92065,\qquad \bar z=.0619,\qquad
\bar t=2\arctan\bar z,
\]

the four successive radicals in (1) have the following brackets,
uniformly over this entire rational \(q\) interval. Every integer in
the next table is divided by \(10^{12}\).

| Radical at the test values | Lower numerator | Upper numerator |
|---|---:|---:|
| \(x_1\) | 1751552933113 | 1751552961661 |
| \(x_2\) | 1658474503120 | 1658474533269 |
| \(y_3\) | 1454593909385 | 1454593971565 |
| \(-x_4\) | 1902121525118 | 1902121569235 |

Each bracket is two integer-square comparisons in the preceding
radicand interval. Substitution into the explicit derivatives of
\(F=h_1^2+h_2^2-q\) gives

\[
|F_y(q,\bar y,\bar t)|<.000027,\qquad
|F_t(q,\bar y,\bar t)|<.000010.                       \tag{11}
\]

The broad stationary proof gives \(F_{yy}>6\),
\(|F_{yt}|<6\), and \(M_{tt}>3/4\), where
\(M(q,t)=F(q,Y(q,t),t)\) and \(F_y(q,Y(q,t),t)=0\).
Consequently, at \(q=q_*\),

\[
|Y(q_*,\bar t)-\bar y|<.000027/6,
\quad |M_t(q_*,\bar t)|<.000037,
\quad |t_*-\bar t|<\frac43(.000037)<.00005.
\]

Also \(|Y_t|<1\), so \(|y_*-\bar y|<.0000545\).
The sine and cosine are 1-Lipschitz. Their values at \(\bar t\)
are rational functions of \(\bar z\), as in (4). It follows that

\[
-.92071<y_*<-.92059,\qquad
.99231<c<.99242,\qquad .12327<s<.12338.                 \tag{12}
\]

The same four radical formulas on this rectangle have these brackets;
again divide the numerators by \(10^{12}\):

| Radical on (12) | Lower numerator | Upper numerator |
|---|---:|---:|
| \(x_1\) | 1751521394645 | 1751584497506 |
| \(x_2\) | 1658435453040 | 1658513580258 |
| \(y_3\) | 1454557893773 | 1454629982384 |
| \(-x_4\) | 1902111197789 | 1902131894451 |

Rational addition and multiplication then give:

| Quantity | Strict lower bound | Strict upper bound |
|---|---:|---:|
| \(x_1\) | 1.75152 | 1.75159 |
| \(x_2\) | 1.65843 | 1.65852 |
| \(y_3\) | 1.45455 | 1.45464 |
| \(-x_4\) | 1.90211 | 1.90214 |
| \(h_1\) | -1.36797 | -1.36748 |
| \(h_2\) | -1.43022 | -1.42976 |
| \((P_H)_x\) | -.74678 | -.74604 |
| \((P_H)_y\) | -1.03026 | -1.02954 |

In particular, all the signs, sectors and farthest-vertex choices used
in Section 4 are strict. Formula (10) and the bound on \(G\)'s left
edge follow directly by using (12) and the last table; no extra radical
evaluation is needed for them.

## 6. A five-dimensional box of noncongruent optimal packings

The following parameters can vary **independently** throughout a full
closed box:

\[
\boxed{
\begin{aligned}
.139&\le x\le .141,&-.001&\le y\le .001,\\
.099&\le w\le .101,&1.349&\le z\le1.351,\\
-.321&\le\eta\le-.319.&&
\end{aligned}}                                                  \tag{13}
\]

This gives central frames near \(2\arctan(1/10)\), strictly different
from both outer frames. The four rational endpoint values

\[
\frac{1-.101^2}{1+.101^2}\le C\le
\frac{1-.099^2}{1+.099^2},\qquad
\frac{2(.099)}{1+.099^2}\le S\le
\frac{2(.101)}{1+.101^2}
\]

follow from monotonicity. Here \(cS-sC>0\), so the absolute value in
\(W_t\) has a fixed sign. With (12) and the eight printed brackets,
direct rational substitution gives the following strict separation
reserves. The named normal points from the central square toward the
listed exterior square.

| Pair | Chosen unit normal | Lower bound for projected center gap minus support sum |
|---|---|---:|
| central, \(A\) | \((1,0)\) | .020 |
| central, \(B\) | \((C,S)\) | .020 |
| central, \(D\) | \((-S,C)\) | .036 |
| central, \(E\) | \((-1,0)\) | .450 |
| central, \(H\) | \((-C,-S)\) | .031 |
| central, \(G\) | \((s,-c)\) | .192 |
| central, \(T\) | \((0,1)\) | .257 |

For example, the \(B\) row is the single rational interval comparison
\(C((P_B)_x-x)+S((P_B)_y-y)-(1+C+S)/2>.020\).
The \(H\) row uses
\(W_t=(1+cC+sS+cS-sC)/2\). These formulas and the printed intervals
specify all seven comparisons without a sampling argument.

Moreover

\[
|Cx+Sy|<.139,\qquad |-Sx+Cy|<.030,
\]

so the core inequalities are strict. Both exterior sliders are strictly
inside the circle: their squared-radius reserves are

\[
\begin{aligned}
q_*-(x_c+1/2)^2-(z+1/2)^2&>.055,\\
q_*-(h_1+2)^2-(-h_2-\eta)^2&>.448.
\end{aligned}
\]

The core signs also hold strictly. Thus (13) is contained in (8).
These are finitely many fixed rational comparisons; the accompanying
[arithmetic transcription](verify_equality_parameter_domain.py) checks
the very same bounds with integer fractions and supplied radical brackets.

Because every inequality involving the five free parameters is strict
in this example, the family has local dimension five. The passage
\(w\mapsto\theta\) has nonzero derivative, and independent changes
of the two central coordinates, its frame and the two slider coordinates
change the corresponding square poses independently.

These changes do not disappear under congruence. In (13), exactly the
five anchors touch the bounding circle. Four have frame zero and the
fifth is \(H\), with its distinct frame. An isometry between two
packings in this box must preserve the unique least enclosing circle,
whose center is the origin. It must preserve the common frame of the
four standard boundary squares and hence fix the remaining boundary
square \(H\). A rotation preserving the standard frame is a quarter
turn; none except the identity fixes the nonzero center \(P_H\).
A reflection preserving the standard frame has an axial or diagonal
mirror line through the origin. The strict bounds for \(P_H\) show
that its center lies on none of those lines. Therefore no such
reflection fixes \(H\). The isometry is the identity, and the unique
central square and the two distinct exterior slider roles recover the
five parameters. Distinct points of the box are noncongruent packings.

For clarity, uniqueness of the least enclosing circle is elementary:
if two different centers enclosed the same vertices at a common least
radius, their midpoint would enclose them at a strictly smaller radius,
by the identity for the squared distance to a midpoint.

## 7. Exact meaning of uniqueness

The complete equality conclusion consists of three statements:

1. The stationary root \((q_*,y_*,t_*)\) is unique in the admissible
   family, by the global analytic family theorem.
2. Every attaining original packing has the five anchors and the two
   outer orientation groups in (1), up to isometry and relabeling, by
   the fixed-witness equality pullback and the global terminal capture.
3. Every remaining freedom, including arbitrary allowed central
   rotations and all limiting contacts, is exactly the five-parameter
   domain (8), with a proved converse. Its open subset (13) rules out
   isolated-pose uniqueness.

Thus the equality classification introduces no additional unresolved
geometric parameter condition. Its only non-hand input at present is
the same unrestricted global capture still being converted for optimality.
