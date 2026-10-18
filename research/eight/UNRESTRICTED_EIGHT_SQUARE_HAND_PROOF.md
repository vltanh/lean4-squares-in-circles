# Eight unit squares in a circle: the sharp radius and every equality packing

## Assembly status

**The unrestricted sharp-radius theorem and the complete equality
classification are proved below. Every gate is discharged by the hand
arguments and fixed rational tables supplied with this manuscript.**
The candidate mismatch chain is complete:

\[
S<13/50\Longrightarrow S<1/10\Longrightarrow S<3/200
\Longrightarrow S<1/1000.
\]

Its final two full tables and independent domain reviews are bound in
`MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json` and
`MISMATCH_015_TO_001_AFFINE_HAND_MANIFEST.json`. The complete separator-owner
and tilt capture, sharp terminal, radius transfer and original-position
equality argument then apply. No mathematical gate remains pending in
this dependency chain.

Some frozen component notes retain historical sentences saying that a
global capture was pending or was then supplied by a computer-assisted
assembly. Those sentences record their earlier external input. Here that
input is discharged by the completed hand chain below, as recorded in
`UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json`. No historical status
sentence imports an additional certificate into the present dependency
graph. The frozen inputs are kept unchanged so their independent-review
hash bindings remain valid.

The sources named below are mathematical appendices to this proof. Their
finite arithmetic consists of supplied rational comparisons and fixed
one-variable polynomial tables, with explicitly proved support formulas
and complete closed domain covers. Programs transcribe and independently
check that arithmetic; an optimizer, a state-subdivision tree, or an
execution-success assertion is not a premise. In particular, the earlier
central-core subdivision certificate, piecewise-linear four-type
certificate, radial-necklace exclusions, and 123-box capture are not used
anywhere in this assembly. This is a long tabular hand proof: the fixed
tables are part of the supplied proof, not omitted numerical evidence.

## 1. Exact statement and the selected constant

A packing means eight closed unit squares with pairwise disjoint open
interiors. Boundary contacts are permitted. Its containing circle may
have any center. Translate that center to the origin and write \(q\)
for the squared containing radius.

Here is an exact definition of the proposed sharp constant. For
\(R=\sqrt q<2\), use the positive radicals

\[
\begin{aligned}
r&=\sqrt{q-u^2},&w&=\sqrt{q-v^2},\\
U&=\sqrt{q-(2-u)^2},&V&=\sqrt{q-(2-v)^2},\qquad U+V=3,
\end{aligned}                                                     \tag{1.1}
\]

and set

\[
\begin{aligned}
k_1&=2-\cos t\,(r-1)+u\sin t,\\
k_2&=1+v\cos t-(w-1)\sin t,\\
F(q,u,t)&=k_1^2+k_2^2-q.
\end{aligned}                                                     \tag{1.2}
\]

In position derivatives, \(v\) is the function of \(q,u\) determined
by (1.1). The global family theorem proves that there is a unique
admissible simultaneous stationary zero

\[
 F=F_u=F_t=0,
 \quad (79/40)^2\le q\le9789/2500,
 \quad \tfrac12<v<u<1,
 \quad 0<t<\arctan(1/5).
                                                               \tag{1.3}
\]

Call it \((q_*,u_*,t_*)\), and put \(y_*=-u_*\). All radicals in
(1.1) are positive at this solution. The exact selection and uniqueness
in (1.3) are proved by
[HUMAN_FIVE_CORNER.md](HUMAN_FIVE_CORNER.md),
[HUMAN_FAMILY_ENCLOSURE.md](HUMAN_FAMILY_ENCLOSURE.md), and
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md). Their argument
proves strict convexity of the complete position problem, positivity of
the reduced tilt curvature at every relevant critical point, and strict
monotonicity of the minimized defect with radius. It does not select a
root by its decimal approximation or assume that arbitrary packings have
the five-corner structure.

We use the exact ceilings

\[
 q_-:=\frac{7831}{2000},\qquad
 Q_1:=\frac{1957767069}{500000000},\qquad
 Q_0:=\frac{9789}{2500}.
                                                               \tag{1.4}
\]

The hand stationary calculation and the two explicit test-pose bracket
in [HUMAN_BROAD_TERMINAL_ARITHMETIC.md](HUMAN_BROAD_TERMINAL_ARITHMETIC.md)
and [HUMAN_SHARP_CEILING_BRACKET.md](HUMAN_SHARP_CEILING_BRACKET.md) give

\[
 q_-<q_*<Q_1<Q_0<4.
                                                               \tag{1.5}
\]

More precisely, with the displayed terminating decimal interpreted as
an exact rational number,

\[
3.91553413751747532652-2\cdot10^{-16}
 <q_*<
3.91553413751747532652+10^{-16}.
                                                               \tag{1.6}
\]

The bracket follows from eight supplied rational square-root brackets
and two test values of \(F\). Ordinary strong convexity bounds the
minimum below the positive test value; a negative test value bounds the
minimum above. Global family uniqueness identifies the intervening zero.
Thus (1.6) introduces no numerical root-isolation premise.

The rational bounds for \(\pi\) used below are elementary. Put
\(T_n(x)=\sum_{j=0}^{n-1}(-1)^j x^{2j+1}/(2j+1)\).
Machin's identity and alternating sums give

\[
2\pi=32\arctan(1/5)-8\arctan(1/239)
<32T_7(1/5)-8T_4(1/239)<6.28318531<710/113.
\]

Both final comparisons are exact rational substitutions. Also
\(\pi<22/7\) follows from
\(22/7-\pi=\int_0^1x^4(1-x)^4/(1+x^2)\,dx>0\).

**Theorem.** Every packing of eight unit squares in a circle has radius
at least

\[
                            R_*:=\sqrt{q_*}.
                                                               \tag{1.7}
\]

Packings at this radius exist. Up to a Euclidean isometry and relabeling,
every equality packing is exactly one of the configurations in the
explicit five-parameter domain of Section 12. Its converse is proved
there as well. The radius, stationary position, outer tilt, and five
exterior anchors are unique in this normalized description; equality
does not give an isolated packing.

The construction and the strict five-dimensional box in Section 12 are
proved at the selected family root by fixed hand comparisons. Sections
2–11 prove the unrestricted lower bound and recover the full stated
structure of every equality packing. Section 12 proves the converse and
shows why uniqueness must be expressed as this complete family.

## 2. A unique central square contains the one-twelfth disk

Put \(\rho=1/12\). We first use two geometric results that apply to
the original eight squares, before retaining only neighboring pairs.

### 2.1. Central existence by angular measure

For a square \(K\), let \(L_r(K)\) be its total angular measure on
the centered circle of radius \(r\), including all connected
components. The one-square theorem in
[HUMAN_GLOBAL_GEOMETRY_CLOSURE.md](HUMAN_GLOBAL_GEOMETRY_CLOSURE.md)
states that, if \(K\) is contained in the disk of squared radius
\(98/25\) and its open interior does not contain the origin, then

\[
                 3L_1(K)+L_{5/4}(K)\ge\pi.
                                                               \tag{2.1}
\]

Equality is possible only, after a rotation or reflection, for
\([x,x+1]\times[-1/2,1/2]\), where
\(0\le x\le(\sqrt{21}-4)/4\). Each equality square has
\(L_1=\pi/3\) and \(L_{5/4}=0\). The proof splits a canonical
square by the signs of its near-side coordinates and whether its near
primary coordinate is below \(1/4\). All arc formulas, including
the disconnected possibilities on the larger circle, are explicit.
The useful monotonicity factorization is

\[
P_r(X)-P_r(Y)
=(X-Y)\{(r^2-1)(X+Y)+(X+Y)^2-Q(X+Y)+Q\},
\quad P_r(z)=z^2\{r^2-(z-1)^2\},
                                                               \tag{2.2}
\]

where \(X^2+Y^2=Q<4\). The bracket is positive because
\(s^2-Qs+Q=(s-Q/2)^2+Q(1-Q/4)>0\).

For pairwise interior-disjoint squares, \(\sum L_r\le2\pi\).
Boundary intersections have measure zero, since a circle meets the
finitely many straight square sides in finitely many points. If no square
contained the origin in its open interior, summing (2.1) would force
equality for all eight squares. Their unit-circle measures would then
sum to \(8\pi/3>2\pi\), a contradiction. Therefore precisely one
square contains the origin in its open interior.

### 2.2. The positive core is a geometric theorem

The hand strengthening at \(q\le Q_0\) is

\[
\boxed{\text{The closed disk }|p|\le1/12
\text{ lies in the central square's open interior.}}
                                                               \tag{2.3}
\]

Here is the structure of the complete argument in
[HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md](HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md).
Normalize the central center to \((a,u)\),
\(0\le u\le a<1/2\), and let \(\Delta=1/2-a\). Translating
the circle center to a nearest central side would leave no open central
square there. Since

\[
Q_0+4/1000+10^{-6}<98/25,
\]

the central-existence theorem implies \(\Delta>1/1000\). Every
other square, in unsigned own-frame coordinates \((A,B)\) with
\(A\ge B\ge0\), consequently has
\(A\ge1/2+\Delta/\sqrt2>5007/10000\).

The three polynomial lemmas in
[CENTRAL_BAND_COMMON_POINT_LEMMAS.md](CENTRAL_BAND_COMMON_POINT_LEMMAS.md)
give an actual segment in every such exterior square:

\[
 V=\{(11/12,y):|y|\le7/20\}
                                                               \tag{2.4}
\]

after rotating its center ray to the positive horizontal axis. They also
give strict pair-angle floors \(3741/5000\), or \(19/25\) when
the primary coordinate exceeds \(107/200\). These are common-point
statements, proved by two explicit polynomials of degrees six and four;
the companion prints their complete 19 fixed Bernstein rows.

If \(5/12\le a\le9/20\), a connected interval of rotations of
(2.4), of width greater than \(347/200\), meets the central square.
If \(9/20\le a<1/2\), the corresponding width exceeds
\(899/500\). Connectedness is proved by radial projection inside a
rectangle, not inferred from its endpoints. The exact widths follow
from three elementary calculus ranges and the single decreasing
quartic displayed in that proof.

No exterior center ray may lie in the forbidden interval: its segment
lies in its own open square. Ordering the seven rays in the complementary
arc leaves six gaps. In the two cases, the combined required angles are
strictly greater than, respectively,

\[
\frac{347}{200}+6\frac{19}{25}=\frac{1259}{200}>\frac{44}{7}>2\pi,
\qquad
\frac{899}{500}+6\frac{3741}{5000}
=\frac{7859}{1250}>\frac{44}{7}>2\pi.
                                                               \tag{2.5}
\]

Both are impossible. Hence \(a<5/12\), which proves (2.3).
Every other closed square has distance **strictly greater** than
\(1/12\) from the origin. A point of intersection with the core would
lie in the central open square and would be approached by interior points
of the other square. Compactness gives the strict distance assertion.

## 3. A boundary neighbor cycle with fixed original witnesses

We now keep the seven exterior squares and their cyclic consecutive-pair
conditions. Nonconsecutive pairs may overlap after the following
deformation. Any impossibility for this larger class applies to the
original packing.

An exterior center has radius \(r\ge7/12\), because the square's
open inscribed radius-\(1/2\) disk avoids the core. Containment gives
\(r^2+r+1/2\le Q_0\), hence \(r<71/50\). Consecutive centers
have distance at least one. On the radial rectangle
\([7/12,71/50]^2\),

\[
\frac{r^2+s^2-1}{2rs}\le\frac{17443}{21300}
 <\frac{41}{50}\le\cos(3/5).
                                                               \tag{3.1}
\]

The maximum is at a corner: fixing either variable gives an increasing
function or one with a sole interior minimum. Thus the smaller angle of
each consecutive pair exceeds \(3/5\). Their seven directed gaps
sum to \(2\pi\), so no one gap can reach \(\pi\): the other
six would sum to more than \(18/5>\pi\).

Choose one genuinely feasible signed separating axis on each original
neighbor edge, once for the entire argument. Fix all true square frames.
When one center is moved, its two selected incident inequalities are two
fixed halfplanes. If their inward unit normals are \(n_1,n_2\), a
nonzero common recession direction is \(n_1+n_2\) unless they are
opposite; in the latter case take a perpendicular direction. Move along
that ray until the first contact with either the outer containment center
body or the forbidden core center body. The former is the intersection
of four closed radius-\(\sqrt q\) disks and is compact; the latter
is a rounded square. The first contact exists, remains admissible, and
preserves both selected inequalities.

Do this for each center not already on a boundary. Previously fixed
centers remain fixed. Equation (3.1) prevents any crossing of consecutive
rays; the seven-gap argument prevents a gap reaching \(\pi\).
After at most seven moves every square touches the containing circle or
the core, and the true frames, cyclic order, and all seven initially
selected witnesses have been retained. This is
[CYCLIC_RADIAL_BOUNDARY_REDUCTION.md](CYCLIC_RADIAL_BOUNDARY_REDUCTION.md),
with the fixed-witness choice made explicit. Its proof works at every
containing squared radius below \(Q_0\) for which the starting
configuration is admissible.

Choose a quarter-turn-equivalent canonical frame for each final center.
Its own-frame coordinates are

\[
 (a,-\sigma b),\quad a\ge b\ge0,\quad
 \alpha=\sigma\arctan(b/a),\quad u=\sigma b/a\in[-1,1].
                                                               \tag{3.2}
\]

The resulting two exact radial curves are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=q,\\
C:&a=7/12\quad(0\le b\le1/2),\\
  &(a-1/2)^2+(b-1/2)^2=1/144
       \quad(1/2\le b\le1/2+\sqrt2/24).
\end{array}                                                     \tag{3.3}
\]

At a canonical-axis tie or a sign cut, make one choice for a vertex and
keep that choice on both incident edges. All boundary kinds are retained:
none of the arguments below discards one of the \(2^7\) radial words.
The initial deformation need not preserve \(u\); it preserves the
true frames. The following radial expansion does preserve \(u\).

## 4. Moving between the three radius levels

Boundary theorems at \(Q_0\), candidate tables at \(Q_1\), and the
sharp terminal at an actual subsharp radius must be connected explicitly.
The required monotonicity is a hand lemma about each true signed axis.

For a fixed center ray and relative frame angle \(\alpha\), the
outer radius solves

\[
r^2+B r+1/2=q,\qquad
B=\cos\alpha+|\sin\alpha|\in[1,\sqrt2].
\]

For \(5/2\le q\le4\), direct substitution and differentiation give

\[
\frac45<r<\frac32,\qquad
\frac14\le r_q=\frac1{\sqrt{B^2+4q-2}}\le\frac13.
                                                               \tag{4.1}
\]

A core center is fixed and has radius at most
\(\sqrt2/2+1/12<4/5\). Thus expanding an outer center also
preserves core avoidance.

Fix any initially feasible signed pair axis and its width \(w\ge1\).
For two outer centers its projection has the form \(ur_A+vr_B\),
with \(|u|,|v|\le1\). When both coefficients are nonnegative,
feasibility implies \(u+v>2/3\), so the derivative exceeds \(1/6\).
If their signs differ, write the projection as \(ur_A-sr_B\), with
\(u,s\ge0\). Whenever it is at least one, (4.1) gives

\[
u>\frac23+\frac8{15}s,
\qquad s<\frac58,
\qquad
\frac{d}{dq}(ur_A-sr_B)
 >\frac16-\frac s5>\frac1{24}.
                                                               \tag{4.2}
\]

For a core–outer pair, writing the projection as
\(ur_O+vr_C\) gives \(u>2/15\) and derivative greater than
\(1/30\). A core–core projection is unchanged. The pair width is
unchanged in every case. By continuity, no initially feasible axis can
cross its threshold downwards as the radius increases.

**Expansion lemma.** Expanding all outer radii from
\(q_a\in[5/2,4]\) to \(q_b\in[q_a,4]\), while holding core
centers fixed, preserves every initially feasible signed separator,
center ray, relative tangent, true frame, quarter word, and physical
center-angle sum.

This is the continuous lemma in
[HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md](HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md).
To use a boundary theorem at \(Q_0\) for a boundary cycle at
\(Q_1\), expand the latter to \(Q_0\). Its frame, angle, and
quarter-word conclusions hold for the same unchanged quantities at
\(Q_1\). Recovering that earlier cycle requires no general inward
monotonicity claim: it was feasible before expansion. The same observation
will recover the subsharp cycle at the end of the proof.

## 5. The complete hand frame concentration theorem

Work first on the boundary curves at \(Q_0\). The common-point
polynomials in [SEVEN_QUARTER_WORDS.md](SEVEN_QUARTER_WORDS.md) show
that any exterior square whose center ray is within \(19/50\) of
a fixed ray contains the point of that ray at radius \(103/100\)
in its open interior. Therefore every consecutive smaller center angle
exceeds \(19/25\). For a physical seven-cycle,

\[
\frac{19}{25}<\delta_i<2\pi-\frac{114}{25}<\frac{3\pi}{4},
\qquad \sum_i\delta_i=2\pi.
                                                               \tag{5.1}
\]

The support-cap lemma in
[HUMAN_CIRCULAR_CAP_AND_AXIS_ELIMINATION.md](HUMAN_CIRCULAR_CAP_AND_AXIS_ELIMINATION.md)
and the backward-axis lemma in
[COMMON_POINT_AND_THREE_QUARTER_ANGLE.md](COMMON_POINT_AND_THREE_QUARTER_ANGLE.md)
leave exactly the four possible forward signed projections displayed in
Section 7. They exclude the other four even if more than one axis is
feasible. The common-point argument applies to arbitrary admissible
centers; it is not a boundary contact assumption.

The four-type hand theorem partitions the outer curve by \(|u|\):
\(L=[0,1/4]\), \(M=[1/4,3/7]\), \(H=[3/7,1]\), and puts the
whole core curve in type \(C\). There are explicit real state markers
\(\psi\), defined in
[HAND_EXTERIOR_FRAME_CONCENTRATION.md](HAND_EXTERIOR_FRAME_CONCENTRATION.md),
for which every feasible adjacent pair satisfies

\[
\delta-\frac9{50}h(\phi)+\psi_{\rm next}-\psi_{\rm source}
 >\Gamma_{XY},
\qquad
h(x)=\frac{|\sin x|+|\cos x|-1}{2},
                                                               \tag{5.2}
\]

where \(\phi\) is the difference of canonical frames. In the explicit
row and column order \((C,L,M,H)\), the lower-bound matrix is

\[
\Gamma=
\begin{pmatrix}
.9200&.9100&.9005&.8833\\
.9100&.9100&.9005&.8833\\
.9005&.9005&.8912&.8926\\
.8833&.8833&.8926&.9099
\end{pmatrix}.
                                                               \tag{5.3}
\]

All decimals in this proof are exact rationals. The ten whole-pair
proofs and their independent reviews are bound by
[FOUR_TYPE_HAND_COVERAGE_INVENTORY.md](FOUR_TYPE_HAND_COVERAGE_INVENTORY.md).
They cover every radial/sign/source-axis case, including type boundaries;
(5.2) is the completed hand theorem, not the older sampled-state or
piecewise-linear certificate.

For completeness, the finite odd-cycle step has a short proof. Subtract
\(a=.8833\) from each entry of (5.3). Every residual is nonnegative.
Every triangle has total at least \(p=.0265\), and every loop except
the M loop has residual at least \(p\). The M loop has residual
\(.0079\); entering and leaving M costs at least
\(2(.0093)\), so their sum is \(p\). A closed odd walk on four
vertices has a loop or an odd triangle. If all seven vertices of the walk
are M, its residual is \(7(.0079)>p\). Otherwise one of the preceding
cases gives total residual at least \(p\). Hence every seven-step
closed walk has weight at least

\[
                         7a+p=\frac{3881}{625}.
                                                               \tag{5.4}
\]

Sum (5.2), choosing one marker at each vertex. With
\(U=\sum h(\phi_i)\), the markers telescope, and (5.4) gives

\[
2\pi-\frac9{50}U>\frac{3881}{625},
\qquad
U<\frac{10394}{25425}<\sqrt2-1.
                                                               \tag{5.5}
\]

The exact upper bound uses \(2\pi<710/113\). On the orientation
circle of circumference \(\pi/2\), the shortest distance
\(d\in[0,\pi/4]\) satisfies
\(h(d)\ge2(\sqrt2-1)d/\pi\). Thus the total shortest variation
is less than \(\pi/2\), the winding is zero, and the frames have
real lifts with range \(D<\pi/4\). The two paths between their
extreme lifts, and the triangle inequality for the concave metric h,
give \(U\ge2h(D)\). Finally the hand Taylor comparison gives

\[
2h(7/10)>
\frac{2945220061}{7200000000}
>\frac{10394}{25425}.
\]

Consequently

\[
                              \boxed{D<7/10.}
                                                               \tag{5.6}
\]

By Section 4, the same frame lifts, center gaps, and forward-axis
conclusions apply to a boundary cycle at \(Q_1\). In particular no
boundary theorem has been applied to the wrong outer radius.

## 6. All quarter words except 0101011 are excluded

Let \(\beta_i\) be the cyclic center arguments and let \(\theta_i\)
be the real frame lifts of range \(D<.7\). Choose integers \(m_i\)
so that the canonical frame satisfies

\[
\beta_i+\alpha_i=\theta_i+m_i\pi/2,
\qquad m_{i+7}=m_i+4.
\]

Put \(k_i=m_{i+1}-m_i\). Then

\[
\phi_i=k_i\pi/2+\theta_{i+1}-\theta_i,
\quad
\delta_i=\phi_i+\alpha_i-\alpha_{i+1},
\quad \sum k_i=4.
                                                               \tag{6.1}
\]

Equation (5.1) implies \(k_i\in\{0,1,2\}\). A value at most
\(-1\) would give \(\delta_i<D<.7\); a value at least three
would give \(\delta_i>\pi-.7>2\pi-114/25\). Three consecutive
zeros are impossible, since their gaps would sum to more than
\(57/25\), whereas (6.1) bounds that sum by \(D+\pi/2<.7+\pi/2\).
There is at most one 2: two of them would leave five zeros in two cyclic
runs and hence three consecutive zeros.

The elementary zero-run enumeration in
[SEVEN_QUARTER_WORDS.md](SEVEN_QUARTER_WORDS.md) now gives, up to
cyclic relabeling and reflection, precisely

\[
0010012,\quad0010102,\quad0010201,\quad0011002,
\quad0010111,\quad0011011,\quad0101011.
                                                               \tag{6.2}
\]

All the exclusions in the next table are whole boundary-cycle
theorems at \(Q_0\), for every radial assignment and every allowed
sign and separator. Their marker labels are chosen consistently per
vertex, so the summed cost is exactly \(\sum\phi_i=2\pi\).

| Quarter word | Hand lower bound for the summed cost | Strict reserve over a rational upper bound for \(2\pi\) |
|---|---:|---:|
| Each of the four words containing 2 | \(1259/200\) | \(1259/200-44/7=13/1400\) |
| 0010111 | \(31417/5000\) | \(31417/5000-710/113=121/565000\) |
| 0011011 | \(125671/20000\) | \(125671/20000-710/113=823/2260000\) |

For the first row, the common signed markers are

\[
L_O=-\frac9{100}+\frac{13}{200}a+\frac{203}{200}b,
\qquad L_C=\frac{73}{10}(7/12-a)+\frac{291}{250}b.
\]

The whole-pair costs \(\phi+\sigma L_s-\tau L_t\) exceed
\(391/400,157/200,163/200\) for quarter increments 0, 1, 2,
respectively. Four zeros, two ones and one two give \(1259/200\).
The three full-angle hand lemmas are assembled in
[COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md](COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md).

For 0010111, the role-dependent affine markers give cost greater than
\(359/400\) on edge 2 and \(17953/20000\) on each other edge.
[SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md](SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md)
assembles all 304 retained-axis cases. Its final outer quarter proof
combines six complete contact neighborhoods with 140 fixed scalar
regimes; all complementary angle chains are closed and fully covered.

For 0011011, the exact quadratic role markers give cost greater than
\(17953/20000\) on every edge.
[WRONG_0011011_WHOLE_WORD_HAND_PROOF.md](WRONG_0011011_WHOLE_WORD_HAND_PROOF.md)
assembles all 76 radial/sign pair cases, or 39 reflection orbits, with
304 retained-axis cases. The component proofs cover the entire stated
angles by monotonicity, exact contact curves, curvature, and supplied
fixed polynomial comparisons. The independently reconstructed finite
cover includes every endpoint and reflected coefficient identity.

These strict bounds contradict the telescoping identity in each case.
Expanding a \(Q_1\) boundary cycle to \(Q_0\) preserves its word,
so only

\[
                              k=0101011
                                                               \tag{6.3}
\]

is possible at \(Q_1\) as well. No enumeration of a smaller set of
radial necklaces is used.

## 7. Candidate coordinates and the six complete tangent exclusions

Use the cyclic roles

\[
(H,G,A,B,T,D,E)=(0,1,2,3,4,5,6),\quad k=(0,1,0,1,0,1,1).
                                                               \tag{7.1}
\]

For source center \((a,-\sigma b)\), target center
\(R_\phi(A,-\tau B)\), put
\(W=(1+|\sin\phi|+|\cos\phi|)/2\). The four retained
signed SAT margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,&&\text{source }+f,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,&&\text{target }+e,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,&&\text{target }+f,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W,&&\text{source }-e.
\end{aligned}                                                     \tag{7.2}
\]

At least one margin is nonnegative on each edge. All axis statements
below apply to every feasible margin, including ties.

Reflect the configuration and reverse its cyclic indices by
\(i\mapsto5-i\pmod7\). The role list becomes
\((D,T,B,A,G,H,E)\), its word remains 0101011, and every signed
tangent changes sign. E is fixed by this permutation. Therefore the
normalization

\[
                                  u_E\le0
                                                               \tag{7.3}
\]

is available without a contact assumption. This is Section 1 of
[CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md](CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md);
none of that note's older hypothetical budget is used here.

The following six completed hand exclusions are at the fixed squared
radius \(Q_1\). A domain not shown in the prerequisite column is
unrestricted within the full canonical state domain.

| Closed impossible domain | Earlier prerequisites | Fixed rows | Hand appendix |
|---|---|---:|---|
| \(u_G\le-4/5\) | \(u_E\le0\) | 9,087 | G_LOWER_AFFINE_HAND_EXCLUSION.md |
| \(u_G\ge-1/20\) | \(u_E\le0\) | 9,796 | G_UPPER_AFFINE_HAND_EXCLUSION.md |
| \(u_T\ge4/5\) | G in \([-4/5,-1/20]\), E \(\le0\) | 7,078 | T_UPPER_AFFINE_HAND_EXCLUSION.md |
| \(u_T\le1/20\) | G in \([-4/5,-1/20]\), E \(\le0\) | 49,971 | T_LOWER_AFFINE_HAND_EXCLUSION.md |
| \(u_H\le1/2\) | G and T in their resulting closed intervals, E \(\le0\) | 48,050 | H_LOWER_AFFINE_HAND_EXCLUSION.md |
| \(u_D\ge-1/2\) | G and T in their resulting closed intervals, E \(\le0\) | 24,197 | D_UPPER_AFFINE_HAND_EXCLUSION.md |

They prove

\[
-\frac45<u_G<-\frac1{20},\qquad
\frac1{20}<u_T<\frac45,\qquad
u_H>\frac12,\qquad u_D<-\frac12.
                                                               \tag{7.4}
\]

Every table covers both radial kinds on every vertex and all four
original margins in (7.2); no preferred owner or smaller mismatch is
assumed. The cyclic cost sums are \(62839/10000\) for the first,
second, third and fifth tables, \(3927/625\) for the fourth, and
\(125671/20000\) for the sixth. Their respective strict reserves
over \(710/113\) are \(807/1130000\), \(1/70625\), and
\(823/2260000\). The individual manifests bind the exact tables,
full closed covers, and independent reviews.

## 8. What each fixed affine-arc table proves

This section records the common continuous proof behind the candidate
tables. It is needed to distinguish an explicit finite hand input from
a numerical minimum or an unexamined successful computation.

Each of the two curves (3.3) is covered by a supplied finite collection
of closed arcs with rational signed-tangent endpoints. Core side and
corner are separated at the exact tangent \(6/7\). On each arc a
role marker has the fixed affine form \(L=c+pa+qb\), with rational
coefficients. At an overlapping endpoint choose one arc once for the
vertex and use the same marker on its two incident edges. The proof
covers all source/target arc choices, so the labels telescope even if
their formulas differ at a cut.

A row specifies one edge, its two arcs, a signed angle interval, an
actual axis j, and a rational multiplier \(\lambda\ge0\). It proves

\[
\phi-\beta_i h(\phi)+L_s-L_t-\gamma_i-\lambda M_j>0
                                                               \tag{8.1}
\]

on that entire product domain. A feasible axis has \(M_j\ge0\),
so (8.1) gives the desired charged pair inequality. In an uncharged cut,
\(\beta_i=0\).

Subtracting \(\lambda M_j\) separates the source and target
coordinates. On a straight core side the minimum of an affine function
is at an endpoint. On a circular arc, a sign bound for its derivative
gives one endpoint, concavity gives both endpoints, or the full-circle
support gives

\[
 Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2},
                                                               \tag{8.2}
\]

where \((h_0,h_0),R_0\) are the center and radius of the relevant
circle. The derivative and concavity premises are themselves among the
row's displayed polynomial inequalities. Reflection and reversal reduce
axes 2 and 3 to axes 4 and 1, replacing the markers by
\((-L_t,-L_s)\) with the declared signs; the original edge charge is
unchanged. These transformations are identities, not an assumed symmetry
of the role-dependent labels.

For a positive supplied rational \(h_0'\) and \(V\ge0\), the
radical in (8.2) has the global polynomial majorant

\[
T(V)=\frac{5h_0'+15V/h_0'-5V^2/(h_0')^3+V^3/(h_0')^5}{16},
\]

because

\[
T(V)-\sqrt V
=\frac{(\sqrt V-h_0')^4\{V+4h_0'\sqrt V+5(h_0')^2\}}
       {16(h_0')^5}\ge0.
                                                               \tag{8.3}
\]

Thus no state minimization remains after these inequalities. On a row
write \(\phi=k\pi/2\pm x\), with a supplied rational interval
\(0\le x\le.7\). Alternating Taylor bounds for sine and cosine
give exact rational lower polynomials for (8.1) and its support premises.
After \(x=l+(r-l)v\), the expansion

\[
P(x)=\sum_{j=0}^n b_j\binom nj v^j(1-v)^{n-j},\qquad 0\le v\le1,
                                                               \tag{8.4}
\]

shows that nonnegative \(b_j\) prove a weak premise and strictly
positive \(b_j\) prove a strict cost. The input tables supply all
arcs, intervals, multipliers, endpoint brackets, and rational coefficient
bounds. The hand kernel derives the polynomial identity; it does not
infer coverage from random samples or infer a global minimum from a
contact list.

For every original axis and permitted signed source/target arc pair,
the table's closed angle intervals cover the complete necessary angle
range. This range is the intersection of (5.1), (6.1), and any earlier
proved mismatch bound explicitly declared as a hypothesis. Consecutive
intervals meet at exact rational endpoints; isolated equality endpoints
are included. The independent assembly checks reconstruct these unions
separately from the polynomial arithmetic.

The common derivation is
[AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md](AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md),
with its independent continuous audit. The conditional-domain extension
has the separate
[CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md](CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md).
Later restrictions of an axis or frame range always come from a preceding
proved implication; they are never used to prove themselves.

## 9. The mismatch chain, with its remaining obligation exposed

Normalize the real frame of A to zero and write

\[
t=\theta_G,\qquad d_i=\theta_{i+1}-\theta_i,
\qquad I=\{0,2,3,4,5\},\qquad
S=\sum_{i\in I}|d_i|.
                                                               \tag{9.1}
\]

The five charged edges are H→G, A→B, B→T, T→D, D→E. The two mixed
edges G→A and E→H remain uncharged. In particular, their angle ranges
are not made small by a bound on S.

For any fully covered pair theorem

\[
\phi_i-\beta_i h(\phi_i)+L_i-L_{i+1}>\gamma_i,
\qquad \beta_i=\beta\,1_{i\in I},
\]

telescoping gives

\[
            2\pi>\Gamma+\beta\sum_{i\in I}h(|d_i|),
\qquad \Gamma=\sum_i\gamma_i.
                                                               \tag{9.2}
\]

On \([0,.7]\), h is increasing and concave and vanishes at zero.
If \(S\le.7\), concavity gives
\(\sum h(|d_i|)\ge h(S)\). If initially only each
\(|d_i|\le.7\) is known, its endpoint chord still gives
\(h(|d_i|)\ge(29/100)|d_i|\). These are the two forms used below.

### 9.1. Complete first contraction: S < 13/50

The theorem
[CANDIDATE_COARSE_MISMATCH_HAND_PROOF.md](CANDIDATE_COARSE_MISMATCH_HAND_PROOF.md)
uses only the G/T/E domains, all four margins on every edge, and the
original range \(|d_i|<.7\). It sets

\[
\gamma=89727/100000,\qquad \beta=99/5000.
\]

Its 462 closed arcs cover 22 signed role/kind domains. All 121,808
original-axis angle chains are covered by 129,031 fixed rows, with
354,720 premise/cost polynomials and 2,961,120 rational coefficient
bounds. The whole support proof and independent closed-cover review
are complete. Since

\[
7\gamma+\beta\frac{29}{100}\frac25-\frac{710}{113}
=\frac{271}{282500000}>0,
\]

equation (9.2) first gives \(S<2/5\).

The printed cost reserves of the same unchanged table allow the seven
constants to be increased by

\[
(15,13,18,12,15,23,6)\cdot10^{-6},
\qquad \sum c_i=51/500000.
\]

Each retained increase is strictly smaller than the minimum printed
cost reserve over every row of its original edge. This finite minimum
is bound in
[COARSE_MISMATCH_PRINTED_RESERVE_STRENGTHENING.md](COARSE_MISMATCH_PRINTED_RESERVE_STRENGTHENING.md).
No arc, angle range, multiplier, or polynomial changes. With

\[
P(x)=\frac x2-\frac{x^2}4-\frac{x^3}{12}
 +\frac{x^4}{48}+\frac{x^5}{240}-\frac{x^6}{1440}
 -\frac{x^7}{10080}\le h(x),
\]

the exact comparison

\[
7\gamma+\frac{51}{500000}+\beta P(13/50)-\frac{710}{113}
=\frac{9154605884982919}{494375000000000000000}>0
                                                               \tag{9.3}
\]

and concavity in (9.2) prove

\[
                               S<13/50.
                                                               \tag{9.4}
\]

### 9.2. Elementary owner and sign consequences

For any core-avoiding square, not just a boundary state, its unsigned
coordinates satisfy

\[
\frac1{12}\le
\sqrt{(a-1/2)_+^2+(b-1/2)_+^2}
\le\sqrt2(a-1/2)_+.
\]

Containment and \(b\le a\) then give

\[
                       .55875<a<1.415,\qquad b<.9.
                                                               \tag{9.5}
\]

On a zero-quarter edge with \(x=|d|\le.4\), either primary margin
\(M_2,M_4\) is at most

\[
.915-1.05875\cos x+.05875\sin x
\le-711/20000<0.
                                                               \tag{9.6}
\]

Thus H→G, A→B, T→D have only margins 1 and 3 already under (9.4).
This is a conclusion, not a premise of Section 9.1.

When \(S\le.1\), if a zero edge's source signed coordinate is
nonpositive or its target signed coordinate nonnegative, its remaining
margins are bounded by \(-.0085\) or \(-.006\). This proves

\[
            u_H>0>u_G,\qquad u_A>0>u_B,\qquad u_T>0>u_D.
                                                               \tag{9.7}
\]

The complete scalar derivations, including the zero-tangent cases, are
in [HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md](HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md).
We use (9.7) only after a proved bound \(S\le.1\).

### 9.3. Complete contraction M1: from 13/50 to 1/10

**Middle contraction theorem.** Consider a boundary neighbor cycle at
\(Q_1\) with candidate word (7.1), the physical angle and frame
hypotheses (5.1), (5.6), and the following closed tangent ranges:

\[
\begin{array}{c|ccccccc}
\text{role}&H&G&A&B&T&D&E\\\hline
u&[1/2,1]&[-4/5,-1/20]&[-1,1]&[-1,1]&[1/20,4/5]&[-1,-1/2]&[-1,0].
\end{array}
                                                               \tag{9.8}
\]

Every vertex independently permits either radial kind. Assume
\(S\le13/50\). Every edge retains all four original possible
margins (7.2). Then \(S<1/10\).

The fixed table in
[MISMATCH_026_TO_01_AFFINE_HAND_THEOREM.md](MISMATCH_026_TO_01_AFFINE_HAND_THEOREM.md)
has input domains
\([-13/50,13/50]\) on the five aligned differences and
\([-.7,.7]\) on the two mixed differences. The table does not assume
the zero-edge owner restriction (9.6), even though it is already
available; in particular A and B have not yet acquired the signs in
(9.7). Its exact constants are

\[
                    \gamma_i=.897582,\qquad \beta=1/400.
                                                               \tag{9.9}
\]

The complete pair theorem has 401 closed arcs covering 18 nonempty
role/kind/sign domains, 123,168 required original-axis angle chains and
131,255 fixed rows. Its 354,398 polynomials have 2,903,573 rational
Bernstein coefficient bounds; all premise comparisons and strict cost
comparisons pass. The least strict cost bound is \(76173/20000000000000\). The independently
reviewed support kernel, full closed unions and exact cyclic constants
are bound in `MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json`. In particular,
no A/B sign or zero-edge owner conclusion is used to establish this
whole-pair theorem.

The remaining contraction is the single hand comparison

\[
7(.897582)+\frac1{400}
 \left(\frac{.1}{2}-\frac{(.1)^2}{4}-\frac{(.1)^3}{12}\right)
-\frac{710}{113}
=\frac{18173}{2712000000}>0.
                                                               \tag{9.10}
\]

Indeed h is bounded below by the cubic in parentheses, so the complete
pair theorem and (9.2) contradict \(S\ge.1\). This proves M1 on its
entire stated domain.

### 9.4. Complete intermediate contraction: from 1/10 to 3/200

Apply the proved M1 and then (9.7). The hypotheses of
[MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md](MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md)
are now discharged. This completed theorem needs only

\[
H,A\in[0,1],\quad G\in[-.8,-.05],\quad B,D,E\in[-1,0],
\quad T\in[.05,.8],\quad S\le.1.
\]

It retains all four original margins, both radial kinds, and the full
mixed-edge range \([-.7,.7]\). Its 335 arcs cover 14 signed
role/kind domains, and all 101,280 original-axis chains are covered by
107,196 fixed rows. The 292,119 polynomials have 2,468,184 coefficient
bounds. The independent continuous/closed-union review and exact replay
are complete.

Here \(\beta=1/200\), and the seven lower constants are

\[
(.8975928,.8975928,.8975928,.8975928,.8975928,
 .89759275,.8975917),\qquad
\Gamma=\frac{125662969}{20000000}.
                                                               \tag{9.11}
\]

The exact Taylor and Machin comparisons are

\[
h(3/200)>\frac{238191}{32000000},\qquad 2\pi<6.28318531,
\]

\[
\frac{125662969}{20000000}
+\frac1{200}\frac{238191}{32000000}-6.28318531
=\frac{2287}{6400000000}>0.
                                                               \tag{9.12}
\]

By (9.2), \(S<3/200\). The stronger H/D cuts remain available,
but are not needed to establish this intermediate theorem.

At this point the large-mismatch quarter-owner theorem in Section 10.1
also applies. Thus B→T and D→E have only axes 3 and 4 before the final
mismatch stage is attempted.

### 9.5. Complete final contraction M2: from 3/200 to 1/1000

**Completed theorem M2.** Consider a boundary neighbor cycle at
\(Q_1\) with the same physical hypotheses, candidate word, and

\[
\begin{array}{c|ccccccc}
\text{role}&H&G&A&B&T&D&E\\\hline
u&[1/2,1]&[-4/5,-1/20]&[0,1]&[-1,0]&[1/20,4/5]&[-1,-1/2]&[-1,0].
\end{array}
                                                               \tag{9.13}
\]

Assume \(S\le3/200\); each vertex independently permits either
radial kind. The only axis restrictions are already proved ones:
axes 1/3 on H→G, A→B, T→D, and axes 3/4 on B→T, D→E. Both mixed
edges G→A and E→H still retain **all four** original margins and their
full signed frame-difference ranges. Then \(S\le1/1000\).

The completed final charged table uses \(\beta=1/20\) and

\[
 (\gamma_0,\ldots,\gamma_6)
 =(.897595,.897595,.897595,.897595,.897595,.897595,.8975925),
\quad \Gamma=\frac{502653}{80000}.
                                                               \tag{9.14}
\]

Its 456 closed state arcs cover all 14 nonempty signed role/kind domains.
All 129,368 original-axis angle chains are covered by 144,709 fixed rows,
with 399,773 premise/cost polynomials and 3,183,184 rational coefficient
bounds. Every row passes the exact support proof of Section 8. The least
printed strict cost coefficient is
\(3986139/100000000000000>0\). The independent review reconstructs
the complete state, signed-angle and original-axis unions, binds the
unchanged independently reviewed kernel to the completed coefficient
replay, and verifies the cyclic contraction. The closed source is
[MISMATCH_015_TO_001_AFFINE_HAND_THEOREM.md](MISMATCH_015_TO_001_AFFINE_HAND_THEOREM.md),
with `MISMATCH_015_TO_001_AFFINE_HAND_MANIFEST.json`.

Its cyclic implication follows from

\[
h(1/1000)>\frac{5996999}{12000000000},
\]

\[
\frac{502653}{80000}
+\frac1{20}\frac{5996999}{12000000000}-6.28318531
=\frac{522599}{240000000000}>0.
                                                               \tag{9.15}
\]

Equations (9.2), (9.15) give the strict conclusion \(S<1/1000\).
Desired mixed owners and the
tilt interval are not prerequisites of M2; they are consequences of the
completed next section after M2.

## 10. Complete capture and the sharp terminal at one thousandth

The results of this section are complete hand theorems. Their
\(S\le1/1000\) premise is supplied by Section 9. They apply to
arbitrary admissible centers, not merely points on the two boundary
curves.

### 10.1. The correct separator owners

Using (9.5), the G/T tangent bounds, and the stated H/D/sign domains,
one obtains linear lower and upper bounds on each pair \((a,b)\).
At nominal zero aligned error the role frames are either 0 or t.
For any assignment of candidate pair owners, summing their necessary
projection inequalities with fixed nonnegative rational weights, and
adding the coordinate bounds with fixed nonnegative multipliers, gives
an inequality

\[
                     \sum_i C_i\cdot(a_i,b_i)\ge B.
\]

The circle equation then gives the necessary upper bound, for supplied
positive \(\mu_i\),

\[
B+\frac12\sum_i(C_{i,a}+C_{i,b})
\le\sum_i\left(\mu_i Q+\frac{|C_i|^2}{4\mu_i}\right).
                                                               \tag{10.1}
\]

This is just completion of a square for
\((a_i+1/2,b_i+1/2)\), whose squared norm is at most Q. All errors
between actual and nominal projections are bounded using the stated
total mismatch and the actual center norm \(<3/2\). Thus (10.1)
is necessary for the actual configuration on the whole declared domain.
Half-angle substitution \(z=\tan(t/2)\) reduces its negation to
the positive quartic supplied by each row.

The complete owner statements, in order, are:

| Step | Hypotheses already available | Conclusion | Fixed quartics |
|---|---|---|---:|
| Zero quarters | \(S\le2/5\), \(q\le Q_0\) | H→G, A→B, T→D use only axes 1/3 | Elementary bounds (9.6) |
| Other quarters | \(S\le3/200\), \(q\le Q_0\), (9.13) | B→T, D→E use only axes 3/4 | 1,545 |
| Mixed edges | \(S\le1/1000\), \(q\le Q_0\), previous owners and (9.13) | G→A only axis 1, E→H only axis 2 | 729 |

The first quartic table covers all 48 nominal patterns with a wrong
quarter owner, allowing all four choices on both mixed edges. The second
covers the 15 remaining mixed patterns other than the desired pair
\((1,2)\). Their closed half-angle unions include every tie and
boundary. Each result excludes every forbidden feasible axis, even when
another allowed axis separates at the same time. This all-axis scope is
essential for the original-witness transfer in Section 11.

The sources are the large-mismatch quarter part of
[HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md](HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md)
and
[HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md](HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md).
Their continuous geometry, all quartic identities, and complete closed
unions have independent reviews. The least printed rational bounds
are \(2539981/10^{12}\) and \(231527/10^{12}\), respectively.

### 10.2. The common tilt

Once all these owners are known, the five aligned edges have exactly
two owner possibilities each. The hand signed-error calculation fixes
one common nonnegative seven-edge weight vector on each tilt interval
before considering those choices. Maximizing its necessary error bound
over \(\sum_{i\in I}|d_i|\le1/1000\) reduces to zero error or
putting the entire error on one of the five edges with either sign.
Only that edge's derivative depends on its two possible owners. Thus
there are exactly

\[
                         1+5\cdot2\cdot2=21
\]

alternatives. Using a common weight vector before this disjunction is
what makes this finite reduction valid. The width-cusp bound uses a
global semiconvex majorant and includes both one-sided slopes.

The 59 complete closed intervals in
[HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md](HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md)
cover

\[
\left[-\frac38,\frac{1001}{20000}\right]
\ \cup\
\left[\frac2{25},\frac38\right]
\quad\text{in }z=\tan(t/2).
                                                               \tag{10.2}
\]

All \(59\cdot21=1239\) necessary alternatives are excluded by
their fixed positive quartics at \(q\le Q_1\). The least bound
is \(40703/(500000000000)>0\). The prior frame theorem gives
\(|t|<.7\), hence \(|z|<3/8\). Elementary arctangent comparisons
convert the remaining open interval in (10.2) to

\[
                             \frac1{10}<t<\frac4{25}.
                                                               \tag{10.3}
\]

All 1,239 identities and 6,195 coefficient bounds have been independently
reconstructed by rational evaluation and Bernstein interpolation, in
addition to the independent continuous review.

### 10.3. A single complete conditional interface

The current package
[HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md](HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md)
and its manifest bind the three tables just used: 3,513 quartics and
17,565 rational coefficient bounds, together with their geometric
derivations and independent audits. In cyclic order the complete owner
sets are

\[
\boxed{\{1,3\},\{1\},\{1,3\},\{3,4\},\{1,3\},\{3,4\},\{2\}.}
                                                               \tag{10.4}
\]

Relative to A's actual frame, the canonical quarter offsets are
\((-1,-1,0,0,1,1,2)\). Therefore (10.4) is exactly the 32-owner
set of the sharp terminal, with the same t and the same S.

The terminal is
[HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md](HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md),
based on
[HUMAN_BROAD_TERMINAL_ARITHMETIC.md](HUMAN_BROAD_TERMINAL_ARITHMETIC.md)
and the exact identity in
[HAND_EXACT_CENTER_SQUARE_COMPLETION.md](HAND_EXACT_CENTER_SQUARE_COMPLETION.md).
Its comparison is the stationary family at \(q_*\) and the actual
common tilt t. The positive vertex weights \(\mu_i\),
\(i=A,B,D,E,H\), sum to one; its seven contact weights are positive.
Their explicit formulas and force identities are supplied by the
stationary calculation. Exact completion of the five center squares
retains the full dependence on arbitrary actual centers.

No local center approximation is a premise. The two transverse
comparison projections are automatically in

\[
 Z\in[557/1000,1417/1000],\qquad
 \eta\in[-103/200,49/125]
                                                               \tag{10.5}
\]

by (9.5), \(|p|<3/2\), the canonical quarter offsets, and the
stationary bound \(-29/20<h_2<-7/5\). All 32 first-order owner
reserves on this enlarged rectangle exceed
\(56793/5000000=.0113586\). The exact center-square completion,
support-offset cancellations, and slider cosine differences bound the
total nonlinear loss by \(9.3S^2\). The two slider force derivatives
are transverse to their chosen projection differences; this cancellation
is why no closeness of the actual centers is required.

Writing \(o_i\) for the selected actual corner offsets and \(F_i\)
for the corresponding center forces, the resulting hand inequality is

\[
q\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2
+\sum_{i=A,B,D,E,H}\mu_i
 \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
+\frac{10293}{5000000}S
\ge q_*.
                                                               \tag{10.6}
\]

The final coefficient is the exact positive reserve

\[
\frac{56793}{5000000}-\frac{93}{10}\frac1{1000}
=\frac{10293}{5000000}>0.
\]

Thus equality at \(q=q_*\) forces \(S=0\), \(t=t_*\), and
the five stationary anchors. The terminal introduces no further capture
or threshold requirement after M2.

## 11. The unrestricted lower bound and the pullback to original squares

Suppose an actual packing lies in a disk of squared
radius \(q<q_*\). Enlarge only the containing disk, without moving
any square, to

\[
                             \bar q=\max(q,q_-).
                                                               \tag{11.1}
\]

By (1.5), \(5/2<\bar q<q_*<Q_1\). Section 2 supplies the
central core for these original squares. Apply Section 3 at \(\bar q\),
retaining the seven initially selected genuine signed witnesses.
This yields a boundary neighbor cycle at \(\bar q\). Expand its
outer radii to \(Q_1\) by Section 4. Every previous signed witness
survives, and all its center rays, true frames, and relative tangents
are unchanged during that expansion.

For the frame and word steps, expand this cycle temporarily further to
\(Q_0\). Sections 5–6 give the frame range, gap bounds, and candidate
word for the unchanged quantities, hence for the already feasible
\(Q_1\) cycle. Return to that \(Q_1\) cycle. Normalize E by the
reflection in Section 7, and apply its six tangent exclusions. The exact
mismatch chain is now

\[
S<13/50\ \xRightarrow{\mathrm{M1}}\ S<1/10
\ \Longrightarrow\ S<3/200
\ \xRightarrow{\mathrm{M2}}\ S\le1/1000.
                                                               \tag{11.2}
\]

All sign and axis restrictions used along this chain have been supplied
before their first use. Section 10 gives (10.3)–(10.4).

Recover the particular \(\bar q\) boundary cycle that existed
before expansion. It is already known to be feasible. Each of its
previously selected signed witnesses remained feasible at \(Q_1\).
The all-axis conclusion (10.4) therefore puts that very witness in the
allowed owner set. It is unnecessary, and would be unjustified in
general, to assert that every axis remains feasible under arbitrary
inward movement.

The recovered cycle has the same candidate labeling, canonical quarter
offsets, relative tangents, true frames, S and t as its \(Q_1\)
expansion. Its own containment and core avoidance hold by construction.
Consequently all the hypotheses of (10.6) hold at \(\bar q\),
giving \(\bar q\ge q_*\), contrary to (11.1). This proves the
unrestricted lower bound.

For an equality packing, start instead at \(q=q_*\) and repeat the
same construction with its fixed original witnesses. Recover the
\(q_*\) boundary cycle after capture. Equality in (10.6) gives
\(S=0\), \(t=t_*\). These are statements about the original
true frames as well, since no stage changed those frames.

To recover the **original positions**, reapply the fixed stationary
dual directly to the original centers. At these zero frame errors the
two slider forces vanish, and the force identity is

\[
\sum_{i=A,B,D,E,H}\mu_i|p_i+o_i|^2
-\sum_{e}\lambda_e g_e
=q_*+\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2,
                                                               \tag{11.3}
\]

where the seven original selected contact gaps satisfy \(g_e\ge0\),
all \(\lambda_e>0\), and \(\sum\mu_i=1\). Containment bounds
the left side above by \(q_*\). Hence every square displacement on
the right is zero, and every original selected gap is zero. This fixes
the five original anchors A, B, D, E, H; the remaining two equations fix
T's horizontal coordinate and G's e-coordinate. Their transverse
coordinates are the two genuine sliders.

This is
[EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md](EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md).
It needs no estimate for how far a center traveled and no bound on the
original slider projections. The initial fixed witnesses supply its
nonoverlap gaps, and the completed stationary dual supplies its zero
slider forces. Section 12 now describes exactly all the remaining
original-square freedoms.

## 12. Complete equality domain, including the central rotation

This section gives an explicit necessary and sufficient description.
Its only global necessity input is Section 11; its calculations and the
construction converse are independent hand results in
[COMPLETE_EQUALITY_PARAMETER_DOMAIN.md](COMPLETE_EQUALITY_PARAMETER_DOMAIN.md).

### 12.1. Five fixed anchors and two exterior sliders

At the unique solution (1.3), define

\[
\begin{aligned}
x_1&=\sqrt{q_*-y_*^2},&
x_2&=\sqrt{q_*-(y_*+2)^2},&x_3&=x_2-3,\\
y_3&=\sqrt{q_*-x_3^2},&y_4&=y_3-2,&
x_4&=-\sqrt{q_*-y_4^2},\\
c&=\cos t_*,&s&=\sin t_*,&e&=(c,s),\quad f=(-s,c),\\
h_1&=cx_1+sy_*-2-c,&
h_2&=-sx_4+cy_4-1-s,&x_c&=x_2-3/2.
\end{aligned}                                                     \tag{12.1}
\]

The exterior centers and frames are

| Square | Center | Frame |
|---|---|---|
| A | \((x_1-1/2,y_*+1/2)\) | 0 |
| B | \((x_2-1/2,y_*+3/2)\) | 0 |
| D | \((x_3+1/2,y_3-1/2)\) | 0 |
| E | \((x_4+1/2,y_4+1/2)\) | 0 |
| H | \((h_1+1/2)e+(h_2+1/2)f\) | \(t_*\) |
| T | \((x_c,z)\) | 0 |
| G | \(P_H+e+\eta f\) | \(t_*\) |

Define

\[
z_+=\sqrt{q_*-(x_c+1/2)^2}-1/2,\qquad
\eta_-=-h_2-\sqrt{q_*-(h_1+2)^2},\qquad
\eta_+=-h_2-13/12.
                                                               \tag{12.2}
\]

The exact exterior ranges are

\[
                         7/12\le z\le z_+,
\qquad \eta_-\le\eta\le\eta_+.
                                                               \tag{12.3}
\]

The approximate values \(z_+\simeq1.36599564\),
\(\eta_-\simeq-.44504969\), \(\eta_+\simeq.34665361\)
are explanatory only.

For necessity, the preserved cyclic order places T in the upper sector
between B and D, and G in the sector from H to A with negative
f-coordinate. The strict stationary coordinate bounds give
\(0<x_c<1/2\) and \(0<h_1+3/2<1/2\). Thus core avoidance
gives \(z\ge7/12\) and the f-coordinate of G at most \(-7/12\).
The farthest-corner equations give the other endpoints in (12.3).

For sufficiency, the five standard squares A, B, T, D, E form three
separated columns; the two within-column contacts A/B and D/E are
exact. This covers their ten pairs for every z in (12.3). The identities

\[
\begin{aligned}
e\cdot(P_G-P_H)&=1,\\
e\cdot(P_A-P_G)&=(1+c+s)/2,\\
e\cdot(P_A-P_H)&=1+(1+c+s)/2,\\
f\cdot(P_E-P_H)&=(1+c+s)/2
\end{aligned}
                                                               \tag{12.4}
\]

cover four more pairs independently of \(\eta\). E and G are
separated horizontally throughout (12.3). The tops of H and G are
strictly below zero, while the bottoms of B, D, T are positive, giving
the last six pairs. The count is \(10+4+1+6=21\). The farthest
corners of the five anchors have norm \(\sqrt{q_*}\); the two
remaining farthest-corner inequalities are exactly (12.3). Hence these
ranges alone ensure containment and every exterior pair separation.

All signs and strict comparisons here follow from the eight displayed
radical brackets and ordinary convexity estimates in the equality
appendix. No contact-search result is used to complete the 21-pair cover.

### 12.2. Seven explicit conditions for the eighth square

Give the central square center \((x,y)\). Use one fundamental frame
interval by setting

\[
1-\sqrt2\le w<\sqrt2-1,
\qquad C_w=\frac{1-w^2}{1+w^2},\qquad
S_w=\frac{2w}{1+w^2}.
                                                               \tag{12.5}
\]

Its frame is \(\theta=2\arctan w\in[-\pi/4,\pi/4)\).
The symbol \(S_w\) is a sine and is distinct from the mismatch sum S.
For a vector \(d=(d_x,d_y)\), put

\[
\begin{aligned}
M_0(d)&=\max\{|d_x|,|d_y|,
             |C_wd_x+S_wd_y|,|-S_wd_x+C_wd_y|\},\\
M_t(d)&=\max\{|cd_x+sd_y|,|-sd_x+cd_y|,
             |C_wd_x+S_wd_y|,|-S_wd_x+C_wd_y|\},\\
W_0&=(1+C_w+|S_w|)/2,\\
W_t&=(1+cC_w+sS_w+|cS_w-sC_w|)/2.
\end{aligned}                                                     \tag{12.6}
\]

Here \(C_w>0\), and \(cC_w+sS_w>0\), since
\(|\theta-t_*|<\pi/2\). Let
\(d_i=P_i-(x,y)\), with every \(P_i\) taken from the explicit
center table above. The complete five-parameter domain is

\[
\boxed{\begin{gathered}
(x,y,w,z,\eta)\in\mathbb R^5,\qquad
1-\sqrt2\le w<\sqrt2-1,\\
7/12\le z\le z_+,\qquad\eta_-\le\eta\le\eta_+,\\
|C_wx+S_wy|<5/12,\qquad|-S_wx+C_wy|<5/12,\\
M_0(d_A),M_0(d_B),M_0(d_D),M_0(d_E),M_0(d_T)\ge W_0,\\
M_t(d_H),M_t(d_G)\ge W_t.
\end{gathered}}
                                                               \tag{12.7}
\]

Every quantity listed on either of the last two lines must meet its
bound. These are seven explicit maximum inequalities, each equivalent
to a finite disjunction of eight signed linear projection inequalities.
There is no unquantified center, existential pose, selected owner to be
found, or optimization instruction left in (12.7).

The two strict inequalities on \((x,y)\) are exactly the open
central-core condition. They make central containment automatic:
the squared norm of its farthest vertex is less than
\(2(11/12)^2=121/72<q_*\). The seven maximum inequalities are
exactly the separating-axis theorem for the seven central/exterior
pairs. Together with Section 12.1 they cover all 28 pairs.

It follows directly that every parameter choice in (12.7) is a packing
in the radius-\(R_*\) disk. Conversely, Section 11 fixes the
anchors, orientations, and two longitudinal slider coordinates of every
equality packing. The central-core theorem, (12.3), and the same
separating-axis formulas force exactly (12.7). This proves both directions
of the complete classification.

The weak core endpoints in (12.3) are intentional. If an exterior square
actually touches the radius-\(1/12\) disk, the strict central-core
inequalities and the seven actual separation inequalities in (12.7)
automatically rule it out. No extra endpoint convention is required.

### 12.3. The equality family has five genuine freedoms

The following parameters can vary independently throughout a full box:

\[
\boxed{\begin{aligned}
.139&\le x\le.141,&-.001&\le y\le.001,\\
.099&\le w\le.101,&1.349&\le z\le1.351,\\
-.321&\le\eta\le-.319.
\end{aligned}}
                                                               \tag{12.8}
\]

The equality appendix proves (12.8) is contained in (12.7) using fixed
rational endpoint bounds. In the order A, B, D, E, H, G, T, the central
pair projection reserves exceed

\[
                   .020,.020,.036,.450,.031,.192,.257.
\]

The two central own-frame coordinates have absolute values below
\(.139\) and \(.030\); the exterior slider squared-radius
reserves exceed \(.055\) and \(.448\). Thus every parameter
inequality involving these five free coordinates has a strict reserve
throughout the box. This also supplies an explicit hand construction
at \(q_*\), independently of the lower-bound argument.

The central frames near \(2\arctan(.1)\) differ from both exterior
frames 0 and \(t_*\). Central rotation is therefore a real equality
freedom, not an omitted change of coordinates.

These five freedoms survive quotienting by isometries and relabeling.
Within (12.8), exactly five anchors touch the containing circle; four
have frame zero and the unique remaining boundary square is H. Once
the lower bound is applied, their least enclosing circle is the given
one and is unique. An isometry between two such packings fixes its
center. It preserves the frame of the four standard boundary squares
and fixes H. A nontrivial quarter turn cannot fix the nonzero H center;
none of the axial or diagonal reflections can fix it, by the strict
coordinate bounds in the equality appendix. The isometry is therefore
the identity. The unique central square and the distinct two slider
roles recover all five parameters. Distinct parameter choices in this
box are noncongruent.

Accordingly the exact uniqueness conclusion is a unique stationary
root and normalized five-anchor structure, together with the full
necessary and sufficient family (12.7). A claim of one isolated optimal
pose would be false.

## 13. Closed dependency ledger

The following is the complete mathematical dependency graph. Every
listed implication is proved by its continuous hand argument and supplied
fixed arithmetic. The final manifest binds these precise inputs and the
independent assembly reviews.

| Gate | Complete input and output | Current status |
|---|---|---|
| Exact family | Global unique stationary root; hand bracket; an actual packing at \(q_*\) | Complete |
| Central core | Eight actual squares below \(Q_0\) give one open radius-\(1/12\) central core | Complete |
| Boundary and radius transfer | Fixed original axes and frames; all 128 radial words; every initially valid axis survives outward expansion | Complete |
| Frame concentration | Ten whole-pair hand lemmas give \(D<.7\) | Complete |
| Quarter words | Seven-word enumeration; all six noncandidate words excluded by hand | Complete |
| Candidate tangent cuts | Normalize E; exclude both bad G intervals, both bad T intervals, H-low and D-high | Complete |
| Initial mismatch | Full-SAT table and retained printed reserves give \(S<13/50\) | Complete |
| M1 | Declared (9.8) domain, all four axes: \(S\le13/50\Rightarrow S<1/10\) | Complete, including all fixed rows and the independent domain review |
| Signs and next mismatch | (9.7), then full-SAT table gives \(S<3/200\) | Complete |
| Quarter owners | At \(S\le3/200\), B→T and D→E have only axes 3/4 | Complete |
| M2 | Declared (9.13) domain and only earlier owner restrictions: \(S\le3/200\Rightarrow S<1/1000\) | Complete, with full exact arithmetic and independent continuous/domain assembly |
| Mixed owners and tilt | At \(S\le1/1000\), all owners (10.4) and \(.1<t<.16\) | Complete |
| Sharp terminal | Arbitrary centers, automatic sliders, positive mismatch and tilt reserves | Complete |
| Original equality | Fixed-witness pullback, five anchors, and exactly the domain (12.7) | Complete |

The principal bound artifacts for these rows are:

The companion
[verify_unrestricted_eight_hand_interfaces.py](verify_unrestricted_eight_hand_interfaces.py)
checks 44 fixed rational comparisons, all 16,384 four-type seven-walk
weights, and the 70 admissible quarter words before their seven-class
dihedral quotient. Its report is
`unrestricted_eight_hand_interface_arithmetic.json`. These finite
interface checks do not stand in for any continuous pair theorem or
closed domain cover.

| Part | Binding source or manifest |
|---|---|
| Four-type frame theorem | FOUR_TYPE_HAND_COVERAGE_INVENTORY.md; HAND_EXTERIOR_FRAME_CONCENTRATION.md |
| Wrong 0010111 | SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md; short_whole_word_hand_assembly_audit.json |
| Wrong 0011011 | WRONG_0011011_WHOLE_WORD_HAND_PROOF.md; wrong_0011011_hand_word_closure_manifest.json |
| G tangent cuts | G_LOWER_AFFINE_HAND_MANIFEST.json; G_UPPER_AFFINE_HAND_MANIFEST.json |
| T tangent cuts | T_LOWER_AFFINE_HAND_MANIFEST.json; T_UPPER_AFFINE_HAND_MANIFEST.json |
| H/D tangent cuts | H_LOWER_AFFINE_HAND_MANIFEST.json; D_UPPER_AFFINE_HAND_MANIFEST.json |
| Initial mismatch | CANDIDATE_COARSE_MISMATCH_HAND_MANIFEST.json; COARSE_MISMATCH_PRINTED_RESERVE_MANIFEST.json |
| \(.26\) to \(.1\) | MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json, including its independent assembly |
| \(.1\) to \(.015\) | MISMATCH_01_TO_015_AFFINE_HAND_MANIFEST.json, including its independent assembly |
| \(.015\) to \(.001\) | MISMATCH_015_TO_001_AFFINE_HAND_MANIFEST.json, including its independent assembly |
| One-thousandth capture | CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH_HAND_MANIFEST.json |
| Sharp-radius and equality transfer | FIXED_CEILING_TRANSFER_HAND_MANIFEST.json |
| Equality domain | COMPLETE_EQUALITY_PARAMETER_DOMAIN.md; COMPLETE_EQUALITY_PARAMETER_DOMAIN_INDEPENDENT_AUDIT.md |

All declared input domains, original-axis covers and cyclic constants in
this ledger have been checked in the stated order. Equation (11.2) is an
unconditional implication. Section 11 proves the unrestricted lower
bound, and Section 12 gives exactly every equality packing and its
converse. The final manifest binds this manuscript, its fixed interface
comparisons, both independent main-assembly reviews and the completed
component manifests. The earlier subdivision or role-box capture plays
no part in this conclusion.
