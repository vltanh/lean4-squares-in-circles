# The complete Cb882 domain and its finite-table proof rules

**Status: whole-original proof still open.** This chapter fixes the entire
Cb882 caller and gives the continuous justifications for the necessary
rational rows and case covers used in its current whole-domain attempt.
The [sharp local terminal](CB882_LOCAL_SHARP_TERMINAL.md) is complete.
A complete attached cover of the remaining original domain is not yet
claimed. Search-node totals and partial frontiers are not cell closures.

## 1. The unchanged original-nine predicate

Retain nine independently oriented physical unit squares A--I, every
original corner strictly inside the disk of squared radius Q=1105/256,
and all 36 original pairs interior-disjoint. Let AB,BC,EF,FG be actual
positive horizontal projection links, and let AB,BC,CD,EF,FG all be
positive horizontal center-cone links. The CD projection is strictly
weak. Normalize y_D-y_C>2/3, canonical theta_A>=0, theta_D<=0,
and x_H<=x_I, as in the fixed Cb882 original.

Its literal branch-3 escape and predecessor condition are exactly

\[
                  y_H-y_B\le-|x_H-x_B|.                       \tag{1}
\]

The preceding AB escape complements already follow from its selected
AB cone. Thus (1) does not change the original's weak CD bit, its
independent frames, its extras or its physical pair conditions.
The intended theorem is that this entire normalized predicate is empty.

Put rho=91/60 and choose the fixed rational radius ceiling

\[
 r_0=83103850693/40000000000,\qquad
 r_0^2-Q=4436580249/1600000000000000000000>0.                   \tag{2}
\]

This radius ceiling supplies only necessary halfplanes; it does not
replace the strict-radius theorem by a larger-radius packing claim.

## 2. Whole-parent initial bounds

The [inner-frame chapter](00100_INNER_FRAME_AND_DOWNWARD_CONE.md) gives
h_B<259/480, |tan(theta_B)|<1/12, |y_A|<1/3 and
y_B>-67/120. Its C-slant input is supplied by the complete
[nonpositive-D hand/table proof](00100_C_SLANT_LOWER_COMPLEMENT.md).
In particular y_C+(7/8)x_C<-7/32.

The following closed boxes enlarge whole-parent necessary bounds;
no inherited computational bound state is imported.

| Original | Horizontal interval | Vertical interval |
|---|---|---|
| A | [-91/60,-91/64] | [-1/3,1/3] |
| B | [-31/60,-27/64] | [-67/120,47/120] |
| C | [29/60,3/4] | [-91/60,-77/120] |
| D | [4/3,91/60] | [-91/60,91/60] |
| E | [-91/60,-29/60] | [-91/60,91/60] |
| F | [-31/60,31/60] | [-91/60,91/60] |
| G | [29/60,91/60] | [-91/60,91/60] |
| H | [-91/60,91/60] | [-91/60,-37/120] |
| I | [-91/60,91/60] | [-91/60,91/60] |

Here the A/B/C bounds are proved in the inner-frame chapter.
The actual AB link gives x_A<x_B-1<-91/64.
The actual EFG links and the universal center bound give
-31/60<x_F<31/60, then x_E<-29/60 and x_G>29/60.
For the B height, its BC cone and C-slant give
y_B<=y_C+x_C-x_B<-7/32+x_C/8-x_B<47/120.
Equation (1) and the original B/H incircles give
y_B-y_H>=1/sqrt(2)>7/10, proving y_H<-37/120.
The D bound x_D>4/3 follows from x_C>h_C-1/60 and the
original CD insets, as in the secondary-axis chapter's Section 2.

Use the signed half-angle parameter w_P=tan(theta_P/2). The initial
closed intervals are

\[
\begin{gathered}
 w_A\in[0,1/10],\qquad w_B\in[-1/24,1/24],\\
 w_D\in[-5/12,0],\qquad
 w_C,w_E,w_F,w_G,w_H,w_I\in[-5/12,5/12].                       \tag{3}
\end{gathered}
\]

Every physical canonical magnitude is at most sqrt(2)-1<5/12.
For A, h_A<37/64<h(1/10)=119/202 gives the stated enlargement.
For B, |tan(theta_B)|<1/12 and
|tan(theta_B)|=2|w_B|/(1-w_B^2)>=2|w_B| give its bound.
The actual canonical and B-slope restrictions remain in scope even
where these rational intervals are slightly larger.

The [whole-domain localization lemma](CB882_GEOMETRIC_REDUCTION.md)
now supplies the additional necessary bounds

\[
\begin{gathered}
 x_D-g_D<17/16,\quad x_C+g_C<17/16,\quad
 x_B+h_B<1/16,\quad x_A+h_A+2h_B<1/16,\\
 x_A<-23/16,\quad x_B<-7/16,\quad x_C<57/80,\\
 y_B<743/1920,\quad y_B-y_H>203/240,\quad
 y_H<-881/1920,\quad x_H<-1/40.
\end{gathered}
\]

These strengthen the initial enclosure without restricting the parent.
Their closed relaxations may be used in a finite table. A complete
height split also permits the stronger row x_C-x_H>=11/12 on the
child y_H>=y_C; the other child y_H<=y_C must be retained.

All three vertical orders are now proved on the entire parent:

\[
 y_E-y_A\ge g_A+g_E,\qquad
 y_F-y_B\ge g_B+g_F,\qquad
 y_G-y_D\ge g_D+g_G.
\]

The [G-order proof](CB882_G_ABOVE_D.md) excludes the lower-G
alternative by two rational estimates. The
[seven-terminal E-down table](CB882_E_DOWN_TABLE.md) proves E above A;
its complete literal rows, weights and transitions have received an
[independent reconstruction](CB882_E_DOWN_REVIEW.md). Its hand inputs
are the [A/E routing theorem](CB882_E_DOWN_ROUTING.md), the
[endpoint estimate](CB882_E_DOWN_ENDPOINT.md), and the
[E-down middle-height theorem](CB882_E_DOWN_F_ABOVE_B.md).
Finally the [one-terminal E-up table](CB882_E_UP_F_ABOVE_B.md)
proves F above B in the surviving E order. The A/E routing theorem
also gives y_A-g_A<-1/4 before either height order is chosen.
These are whole-parent reductions; the remaining arrangement still
requires exclusion.

The later [seven-original F-order theorem](00100_C_F_ABOVE_B.md)
proves F above B without the B/H downward cone, throughout the
nonnegative-A, nonpositive-D caller. The
[universal left-cap theorem](CD402_H_ABOVE_B.md) also gives
abs(y_A)<1/4 and x_P+g_P>-15/16 for every P distinct from A.
It excludes the leftward B/P inset alternative for every P distinct
from A,B. These are further necessary rows of the unchanged
Cb882 caller; its separate Cd402 H-up corollary is not imported.

## 3. Exact rational frame and support enclosures

The [physical-frame row chapter](CB882_PHYSICAL_FRAME_ROWS.md) proves
the corresponding linear inequalities retaining each original's actual
frame components, including original-corner halfplanes and the distance
from another original's incircle to its physical square. These are
continuous row-validity statements; a finite table must still display
the complete case cover and its exact weighted contradictions.

Write a(w)=(1-w^2)/(1+w^2), b(w)=2w/(1+w^2),
h(w)=(a(w)+|b(w)|)/2. For a current signed interval [l,u], let
m be zero if the interval contains zero, and otherwise the smaller
endpoint magnitude; let M be the larger endpoint magnitude. Valid
whole-interval bounds are

\[
 H=h(m),\quad
 U=\begin{cases}h(M),&M<2/5,\\707107/1000000,&M\ge2/5,
 \end{cases}\quad g^-=1/(4U),\quad a^+=a(m).
\]

The actual signed slope belongs to
[2l/(1-l^2),2u/(1-u^2)] intersected with [-1,1]; for B it
may additionally be intersected with [-1/12,1/12]. If the
physical canonical or slope intersection is empty, that entire
angle case is empty. The upper bound U is justified by
707107^2-500000000000=309449>0.

For any literal rational unit vector n, the minimum support over
the signed angle interval is bounded below by the minimum of its
two endpoint supports and 1/2 if an actual projection corner lies
between them. The endpoint-sign test and concavity proof are exactly
those in the secondary-axis chapter, Section 4. Denote this lower
bound by M_P(n).

For a pair P,T, use its rational lower common side-axis threshold
R^-_{PT} from equation (10) of that chapter, interpreting the
intervals as signed half-angle intervals directly. The relative-angle
endpoint and possible-zero proof is unchanged. All original side-axis
thresholds are at least R^-_{PT}>=1.

One may retain the original signed components b_P,b_T instead of
discarding their relation to the center rows. The
[frame-coupled pair lemma](FRAME_COUPLED_PAIR_ROWS.md) proves

\[
 R_{PT}\ge1+k_{PT}|b_P-b_T|,\qquad
 k_{PT}=\max\left\{0,\min_{w\in\{l_P,u_P\},\ v\in\{l_T,u_T\}}
 \frac{1+wv-|w-v|}{2(1-wv)}\right\}.
\]

The four-endpoint minimum is valid even on the enlarged rational
canonical boxes. In particular, if S is the upper squared-distance
secant from Section 4, the two simultaneous rows
S>=1+2k_PT(b_P-b_T) and S>=1-2k_PT(b_P-b_T) are necessary.
These use the same physical frame components as the original corner
inequalities; they do not introduce independently chosen frames.

There is also a universal width comparison, proved in Section 2 of
the [G-order chapter](CB882_G_ABOVE_D.md):

\[
 R_{PT}\ge1+|h_P-h_T|.
\]

Consequently the same squared-distance secant S satisfies both
S>=1+2(h_P-h_T) and S>=1-2(h_P-h_T). The halfwidths here are
the actual original frame quantities (alpha+|beta|)/2.

## 4. Original physical rows at a current center box

Every row below is a necessary inequality about the same originals.
Let H_P,U_P,g_P^- be the current frame bounds, and let the current
center box be proved before constructing its rows.

Each original gives n dot c_P<=r_0-M_P(n) for every retained
rational unit direction n, and n dot c_P<=rho by its universal
center disk. Any additional literal rational unit direction is
permitted by the same proof. A numerical suggested direction must be
replaced by an exactly unit rational vector before using this rule.

Every actual link P,T gives x_T-x_P>=H_P+H_T. Every cone gives
x_T-x_P>=+(y_T-y_P) and >=-(y_T-y_P). CD gives its inset
gap >=g_C^-+g_D^-, the weak relaxation <=U_C+U_D, and
y_D-y_C>=2/3. B/H gives (1) and the additional inset comparison
y_B-y_H>=g_B^-+g_H^-: otherwise the two inset squares would
overlap in both coordinates because of (1).

Useful combined rows, derived without dropping any positive term,
are

\[
\begin{gathered}
 x_C\ge H_C-1/60,\qquad
 x_C\le\min(U_C+r_0-2,r_0-1-g_C^-),\\
 x_D\ge59/60+g_D^-,\quad
 x_G\ge H_G+101/432,\quad x_B\le r_0-2-H_B,\\
 x_D-x_A\ge H_A+2H_B+1+g_D^-,\\
 x_D-x_B\ge H_B+1+g_D^-,\qquad
 x_C-x_A\ge H_A+2H_B+H_C,\\
 H_A+H_B\le r_0-1,\qquad H_B\le259/480,\\
 46x_C+(27/2)x_G\ge27/4+46H_C+(27/2)H_G,\\
 46x_D+(27/2)x_G\le211/4+46U_D+(27/2)U_G,\\
 x_D-x_C\le1-H_C+U_D,\\
 x_D-x_G\le1459/1728,\qquad x_G-x_D\le11/60.
\end{gathered}                                                   \tag{4}
\]

Their derivations are in the preceding hand chapters: sum the actual
links and CD inset, use h+g>=1, and use the two physical endpoint
caps. The frame-sum row follows by bounding the whole horizontal
span from x_A-h_A to x_D+h_D by 2r: its lower bound is
2h_A+2h_B+(h_C+g_C)+(h_D+g_D)>=2h_A+2h_B+2.
The C-slant row and x_H<=x_I remain present. Since x_G>0, the
proved lower-right pocket exclusion also gives y_G>=y_C.

The complete [endpoint-inset lemma](00100_ENDPOINT_INSETS_ARE_VERTICAL.md)
also gives |y_E-y_A|>=g_A+g_E and |y_G-y_D|>=g_D+g_G.
Thus each endpoint inset pair has only its two vertical cases; both
horizontal cases are excluded on the whole parent by a hand proof.
The [G-order theorem](CB882_G_ABOVE_D.md) further excludes the lower
G case, so the whole-parent row y_G-y_D>=g_D+g_G is now available.
The seven-terminal E-down theorem likewise leaves only the upper A/E
order on the whole parent.
The [B/F inset theorem](CB882_BF_VERTICAL.md) similarly proves
|y_F-y_B|>=g_B+g_F on the whole parent. Its two vertical alternatives
are exhaustive, before either A/E height order is chosen. The proof
uses the physical outsider strip under an endpoint span of h_P+h_T+2.
The two middle-height theorems above then leave only F above B.
Its small-tilt unary estimate additionally gives
-x_A<=rho max(alpha_A) on every current A-angle interval.

Every pair P,T gives the necessary bound |c_T-c_P|>=R^-_{PT}.
For a proved difference interval L<=z<=U, use
z^2<=(L+U)z-LU. Applying this to the two coordinate
differences converts the squared distance bound to an affine
necessary row. Its intervals must be proved before this use.

There is a stronger necessary row from the incircle of T and the
actual contained inset of P. Their distance condition is

\[
 \sum_{z=\Delta_x,\Delta_y}\max(|z|-g_P,0)^2\ge1/4.
\]

The convex function f(z)=max(|z|-g_P^-,0)^2 is pointwise at least
the corresponding function for the actual g_P. On a proved interval
[L,U], its secant
((f(U)-f(L))/(U-L))z+(Uf(L)-Lf(U))/(U-L) bounds f(z)
from above. Sum these two secants and require the sum to be at least
1/4. If L=U, use the exact constant f(L). This supplies a rational
necessary affine row for every ordered original pair, without selecting
a physical separating axis.

Finally the foundation's physical pair cap may be used for any
ordered pair P,T and either signed coordinate direction e:

\[
 46(e\cdot c_P)+(27/2)(e\cdot c_T)
                  \le211/4+46U_P+(27/2)U_T.                  \tag{5}
\]

It requires no selected owner, height order or common frame.

## 5. A complete affine enclosure of a selected physical axis

A side-axis case specifies the actual owner O, its primary or
secondary axis, and its sign s in {-1,+1}. Let the actual signed
slope t_O lie in [p,q]. For a primary axis, its unnormalized
projection toward T from P is
s Delta_x+s t_O Delta_y; for a secondary axis it is
-s t_O Delta_x+s Delta_y. The normalized support requires
this projection to be at least R^-_{PT}/a_O^+.

The only variable product can be bounded by the following rational
identity. If z in [L,U] and t in [p,q], then

\[
 tz\le\begin{cases}
 qz,&L\ge0,\\
 pz,&U\le0,\\
 ((p+q)/2+(q-p)(U+L)/(2(U-L)))z
                  -(q-p)LU/(U-L),&L<0<U.
 \end{cases}                                                   \tag{6}
\]

The last line uses tz<=((p+q)/2)z+((q-p)/2)|z| and
the upper secant of |z|. It therefore holds even when the
actual slope and center difference are correlated. Replace the
product in the chosen side-axis projection by (6), taking
z=s Delta_y for a primary axis and z=-s Delta_x for a secondary
axis. The interval [L,U] must be the proved interval of this signed
coordinate difference; negation changes [L,U] to [-U,-L]. Thus the
product being replaced always has coefficient +1. In particular,
one must not multiply an upper bound for t Delta_y or t Delta_x
by a negative sign. The resulting affine upper projection must
still be at least the support
threshold. This is a necessary row over the entire closed box,
without an approximation tolerance or an independent frame.

## 6. Exact deductions and contradictions

For any current rows A_j c<=B_j, positive integer weights w_j
give a=sum w_j A_j and b=sum w_j B_j. If the proved center
box is P_k=[l_k,u_k], define

\[
 \operatorname{low}_P(a)=\sum_k\min(a_k l_k,a_k u_k).
\]

A complete affine contradiction is b<low_P(a). For a coordinate
deduction choose a positive integer M and sign s. The same row
sum proves

\[
                    s c_k\le
             (b-\operatorname{low}_P(a-Ms e_k))/M.            \tag{7}
\]

A printed upper bound may be rounded only upward; its negation
gives a lower bound. The factor M in both the target coefficient
and the denominator is essential. Every deduction of a batch
uses the old proved box; the new bounds are installed afterwards.
This finite implication induction prevents self-supporting bounds.

Selected physical axes also allow a short geometric terminal.
Two successive genuine separations along the identical original
owner and side axis imply projected endpoint span at least two,
because every unit-square support halfwidth is at least one-half.
If the proved endpoint difference box has maximum squared norm
strictly below four, this is impossible. Identical frame ownership
is required; merely close directions cannot be joined.

The complete sharp terminals are the
[enlarged local theorem](CB882_ENLARGED_SHARP_TERMINAL.md),
the stronger [uniform one-tenth theorem](CB882_UNIFORM_SHARP_TERMINAL.md),
and the [four-row guard catalogue](CB882_SHARP_GUARD_CATALOGUE.md).
They can be invoked only when the current proved angle and center
bounds, or explicit [relative-coordinate row sums](CB882_SHARP_GUARD_ROW_CERTIFICATES.md),
imply the entire selected guard. Each catalogue row has its own
angle and height thresholds, including two endpoint-height targets.
A numerical near-optimal pose is not such an implication.

## 7. Exhaustive case operations and completion boundary

The permitted case operations are complete closed unions:

* Both midpoint halves of an original angle interval.
* Both midpoint halves of a proved center-coordinate interval.
* All four signed horizontal/vertical separations of a pair's actual
  contained aligned insets.
* All eight signed side axes, retaining both original owners, for a
  physical pair.

There is a smaller complete CD-axis union. Sections 2--4 of the
[primary-axis chapter](00100_C_SLANT_PRIMARY_AXES.md) exclude every
alternative except +u_C with theta_C>=0, +v_C with theta_C<=0,
and +v_D. Those exclusions use cap transfer and the original CD
cone, height and strict weak bit; they do not use the contrary C-slant
hypothesis. The first case may also retain the necessary height and
span bounds (10)--(11) in that chapter. With w_C>=0 and
z_D=|w_D|, these include

\[
 y_D-y_C\ge J(w_C)+k(z_D),\quad
 J(w)=\frac{1-w^2+2w^3}{2(1+w^2)},\quad
 k(z)=\frac{1-2z-z^2}{2(1+z^2)}.
\]

J decreases on [0,5/12] and k decreases on the physical interval.
Their endpoint minima therefore give necessary rational rows. A
negative k value caused by enlarging the canonical parameter box may
be replaced by zero, since the actual canonical k is nonnegative.

Adding a necessary circle row or a proved bound deduction requires
no case split. Each operator preserves the entire unchanged physical
caller. The sharp terminal and each weighted or geometric
contradiction have their mathematical proofs above.

To conclude the whole Cb882 theorem, an attached finite table must
list every split, every deduction with its literal nonnegative
weights, every extra rational circle direction, and every terminal,
and must cover every child of the single original parent. Until
that entire cover is present and checked, the original remains open.
The present chapter supplies sound proof rules and a fixed domain,
not a substitute for the missing complete cover.
