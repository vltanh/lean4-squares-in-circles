# Exact finite-cover rules for the original Cb882 domain

This chapter gives the common root and proof rules for literal finite covers
of [the original Cb882 predicate](CB882_WHOLE_DOMAIN.md). Every attached
cover states any additional hypothesis explicitly. The
[C-primary cover](CB882_C_PRIMARY_COMPLETE.md) assumes a positive C-owned
primary separator; a whole-original cover must cover all three remaining
C/D axes. This chapter alone asserts neither exclusion.

Each proof retains all nine physical originals and all 36 physical pair
conditions. Its appendices contain a root table, a literal rational row pool,
exact context tables, positive row sums, and a complete indexed case tree.
These are the proof data; no numerical feasibility verdict is a premise.

## 1. Original caller and the root enclosure

Retain the strict-radius Cb882 caller: every original corner lies strictly
inside the centered disk of squared radius Q=1105/256; all original open
interiors are pairwise disjoint. The links AB,BC,EF,FG have actual disjoint
horizontal projections. The links AB,BC,CD,EF,FG satisfy the positive horizontal
center-cone comparison. The CD projection is strictly weak. Retain

\[
 y_D-y_C>2/3,\qquad \theta_A\ge0,\qquad \theta_D\le0,
 \qquad x_H\le x_I,\qquad y_H-y_B\le-|x_H-x_B|.
\]

All these predicates remain in scope even when a necessary row uses their
closed relaxation. In particular, the strict weak CD bit is retained for the
sharp terminals. Set

\[
 \rho=91/60,\qquad r_0=83103850693/40000000000,
 \qquad r_0^2-Q=4436580249/1600000000000000000000>0.
\]

The whole-parent deductions in Sections 1--2 of the whole-domain chapter,
[the geometric reduction](CB882_GEOMETRIC_REDUCTION.md), and
[the A/E routing theorem](CB882_E_DOWN_ROUTING.md) give the following root.
Its intervals are closed enlargements, not additional hypotheses.

| Original | w=tan(theta/2) | x | y |
|---|---|---|---|
| A | [0,1/10] | [-91/60,-23/16] | [-1/3,1/4] |
| B | [-1/24,1/24] | [-31/60,-7/16] | [-67/120,743/1920] |
| C | [-5/12,5/12] | [29/60,57/80] | [-91/60,-77/120] |
| D | [-5/12,0] | [4/3,91/60] | [-91/60,91/60] |
| E | [-5/12,5/12] | [-91/60,-29/60] | [-91/60,91/60] |
| F | [-5/12,5/12] | [-31/60,31/60] | [-91/60,91/60] |
| G | [-5/12,5/12] | [29/60,91/60] | [-91/60,91/60] |
| H | [-5/12,5/12] | [-91/60,-1/40] | [-91/60,-881/1920] |
| I | [-5/12,5/12] | [-91/60,91/60] | [-91/60,91/60] |

The root also retains the necessary rows

\[
 x_H\le-1/40,\quad y_H-y_B\le-203/240,\quad
 y_E-y_A\ge g_A+g_E,\quad y_G-y_D\ge g_D+g_G.
\]

The first two come from the geometric reduction. The endpoint orders come
from [the complete E-down exclusion](CB882_E_DOWN_TABLE.md) and
[the G-order theorem](CB882_G_ABOVE_D.md). The later broader
[seven-original E-order proof](00100_C_E_ABOVE_A.md) is an alternative
acyclic source for the first endpoint order.

In the literal root's choice notation these are, respectively,
`lin([(14,1)],-1/40)`, `lin([(15,1),(3,-1)],-203/240)`,
`proxy(0,4,1,+1)`, and `proxy(3,6,1,+1)`. The root does not silently
add an I location or a selected physical CD separator. Its B/F height split
retains both children; the downward child invokes
[the complete E-up F-order table](CB882_E_UP_F_ABOVE_B.md).
The [B/F vertical theorem](CB882_BF_VERTICAL.md) justifies that two-case split.

A cover may additionally declare a global physical hypothesis in its root.
For the C-primary conditional theorem, this is exactly

\[
 u_C\mathbin\cdot(c_D-c_C)\ge
 \frac12+\frac{|u_C\mathbin\cdot u_D|+|u_C\mathbin\cdot v_D|}{2}.
\]

It is recorded as `root_assumptions=[['sat',2,3,2,0,1]]`. This is a theorem
hypothesis, not an inferred row and not an assumption of a whole-original
cover. The ordinary choice list remains the one displayed above until the
named single-child action in Section 4 records that separator. Thus all
pre-separator contexts keep their exact original boxes and choices.

## 2. Variables, context boxes, and row interpretation

Index A,...,I by i=0,...,8. The 54 physical quantities are

\[
 z_{2i}=x_i,\quad z_{2i+1}=y_i,\quad
 z_{18+3i}=a_i,\quad z_{19+3i}=b_i,\quad z_{20+3i}=d_i,
 \qquad z_{45+i}=g_i,
\]

where u_i=(a_i,b_i), v_i=(-b_i,a_i), d_i=|b_i|,
h_i=(a_i+d_i)/2, and g_i=1/(4h_i). The symbol d_i here is an
absolute frame component. Write

\[
 a(w)=\frac{1-w^2}{1+w^2},\qquad b(w)=\frac{2w}{1+w^2}.
\]

For a proved w interval [l,u], put m=0 if l<=0<=u and otherwise
m=min(|l|,|u|); put M=max(|l|,|u|). The context gives

\[
 a_i\in[a(M),a(m)],\quad b_i\in[b(l),b(u)],\quad
 d_i\in[b(m),b(M)],\quad g_i\in[1/(4U),1/(4H)],
\]

where H=(a(m)+b(m))/2 and
U=(a(M)+b(M))/2 for M<2/5, while U=707107/1000000 otherwise.
These are the continuous frame enclosures of the whole-domain chapter.
The exact canonical restriction a_i>=d_i remains in scope in the rational
tails beyond |w|=sqrt(2)-1. A context contains all nine original frames.

A literal pool row `k:q` contributes q z_k; absent coefficients are zero.
Every row means c dot z<=B. Its label identifies the generating family and
its exact parameters. Before printing, a row may be divided by
max(1,max_k |c_k|), a positive rational; the printed row and its printed
weights are the quantities used in every sum.

An identical labelled equation may occur in several contexts and have one
pool ID. Its validity is still checked at each use against that context's
box, retained choices, and row-family hypotheses. The context's permitted-row
list specifies precisely which pool rows its certificates use.

The row-family sources are as follows.

| Labels | Necessary inequality and source |
|---|---|
| bound upper/lower | The displayed interval of the indicated z coordinate. |
| frame chord/tangent; absolute frame chord/tangent; canonical frame; abs positive/negative/exact/secant | The signed and absolute unit-arc inequalities in Section 1 of [physical frame rows](CB882_PHYSICAL_FRAME_ROWS.md). Absolute arcs retain the same original a_i,d_i even across zero signed tilt. |
| width lower/upper; inset tangent/secant | H<=h_i<=U and the reciprocal tangents/secant in equation (5) of that chapter. |
| corner; center; exact Q tangent; extra | Original-corner or center halfplanes in equations (6)--(7). Unit rational normals use r_0 or rho. Integer normals of squared norm 1105 use exact corner right side 1105/16. |
| actual; cone; proxy | The original actual links, center cones, and the selected contained-inset inequalities defined in Section 4 below. |
| sat; frame sat | All applicable signed-product upper planes for the selected physical owner-axis separation, using R^- or 1 plus either signed beta difference times k; physical frame rows, Sections 3--4, and [frame-coupled pair rows](FRAME_COUPLED_PAIR_ROWS.md). |
| common owner path | Add the two retained separations along the identical original owner and side axis, and apply the same signed-product upper planes to the endpoint difference; physical frame rows, Section 4. |
| distance; frame distance; width mismatch distance | Upper secants of the squared coordinate gaps against (R^-)^2, 1 plus/minus 2k(b_i-b_j), or 1 plus/minus 2(h_i-h_j). See whole-domain Sections 3--4, frame-coupled pair rows, and physical frame rows, equation (14). |
| incircle inset | Upper secants of max(|Delta_ax|-g_0,0)^2 summed over both coordinates, where g_0=1/(4U_i), with sum at least 1/4; whole-domain Section 4. |
| actual square incircle | Equations (11)--(13) of physical frame rows, retaining the actual frame of i and all indicated upper-product choices in its original-square distance to j's radius 1/2 incircle. |
| pair cap | 46(s c_i,ax-h_i)+(27/2)(s c_j,ax-h_j)<=211/4, for either coordinate and sign; [foundation](FOUNDATION.md) and whole-domain equation (5). |

For completeness, the non-generic geometric labels are matched below to their
actual-variable forms. All are closed necessary inequalities; their sources
are the cited whole-parent hand proofs, not earlier numerical contexts.

| Labels | Actual-variable inequalities and source |
|---|---|
| B positive/negative slope; B narrow frame | ±b_B<=a_B/12 and h_B<=259/480; [inner frame](00100_INNER_FRAME_AND_DOWNWARD_CONE.md). |
| CD inset; CD weak closure; CD v | x_D-x_C>=g_C+g_D; x_D-x_C<=h_C+h_D; y_D-y_C>=2/3. Original CD cone, contained insets, weak bit and normalization. |
| BH down cone; BH down inset; HI x order | y_H-y_B<=±(x_H-x_B), y_B-y_H>=g_B+g_H, x_H<=x_I. Original escape and physical insets. |
| C slant; G above C | y_C+7x_C/8<=-7/32 and y_G>=y_C; [C-slant complement](00100_C_SLANT_LOWER_COMPLEMENT.md) and its lower-right pocket exclusion. |
| C x lower; C x upper width/inset | x_C>=h_C-1/60; x_C-h_C<=r_0-2; x_C+g_C<=r_0-1. Whole-domain equation (4), retaining the actual h_C,g_C before any interval weakening. |
| D x lower; G inner x lower; B x upper | x_D-g_D>=59/60; x_G-h_G>=101/432; x_B+h_B<=r_0-2. Whole-domain equation (4) and the endpoint-inset derivations cited there. |
| long span; A B width sum | x_D-x_A>=h_A+2h_B+1+g_D; h_A+h_B<=r_0-1. Sum the original actual links, CD inset, and h+g>=1; whole-domain equation (4). |
| left cap load | 46x_C+(27/2)x_G>=27/4+46h_C+(27/2)h_G; the physical endpoint cap in whole-domain equation (4). |
| CD cap transfer; DG forward/reverse gap | x_D-x_C<=1-h_C+h_D; x_D-x_G<=1459/1728; x_G-x_D<=11/60. [Endpoint-inset theorem](00100_ENDPOINT_INSETS_ARE_VERTICAL.md), with whole-domain equation (4). |
| A unary | -x_A<=rho a_A; endpoint-inset theorem, Section 1, equation (6). |
| D unary inset; C/B/A unary inset transfer | x_D-g_D<=17/16; x_C+g_C<=17/16; x_B+h_B<=1/16; x_A+h_A+2h_B<=1/16. [Geometric reduction](CB882_GEOMETRIC_REDUCTION.md). |
| H negative margin; BH physical clearance | x_H<=-1/40; y_H-y_B<=-203/240. The same geometric reduction. |
| A signed height inset reserve; A signed height | y_A-g_A<=-1/4 and y_A<=1/4; [A/E routing](CB882_E_DOWN_ROUTING.md). |
| universal left cap; A absolute quarter height; no left B inset | x_i+g_i>=-15/16 for i!=A; ±y_A<=1/4; x_B-x_i<=g_B+g_i for i!=A,B. The whole-parent portions of [the left-cap theorem](CD402_H_ABOVE_B.md); its separate Cd402 H-order consequence is not imported. |

Two conditional rows use the positive C-primary choice only. Write
k_C^- = max(0,(a(w_C^+)-b(w_C^+))/2), where w_C^+ is the upper
parameter endpoint, and U_C is the proved upper halfwidth. The labels
`CD C primary height frame` and `CD C primary span frame` assert

\[
 y_C-y_D+(a_D-d_D)/2\le-J(w_C^+),\qquad
 x_C-x_D+g_C+a_D/2+\frac{k_C^-}{2U_C}d_D\le0,
\]

where J(w)=(1-w^2+2w^3)/(2(1+w^2)). These are the continuous
bounds (10)--(11) in [the primary-axis chapter](00100_C_SLANT_PRIMARY_AXES.md).
They require the retained choice +u_C and w_C>=0. The original strict weak
CD bit excludes w_C=0 in that choice; no division by zero is assumed.

All product and secant bounds use the context's already-proved intervals.
A signed multiplier is absorbed into the product variable before an upper
plane is chosen. A coincident secant interval uses its exact constant value.
These are the conventions proved in the physical-frame chapter; no new
row family from an unfinished exploration is part of this cover.

## 3. Literal sums, simultaneous deductions, and frame inversion

Let the printed positive integer weights give A dot z<=B. For a rational
vector t and the old context box z_k in [L_k,U_k], define

\[
 \mathcal L(t)=\sum_{t_k\ge0}t_kL_k+\sum_{t_k<0}t_kU_k.
\]

A contradiction context supplies a printed strictly positive lower bound
for mathcal L(A)-B. A bound line (k,s,b), s in {-1,+1}, asserts
s z_k<=s b and supplies a nonnegative lower bound for

\[
 10^6 s b-B+\mathcal L(A-10^6s e_k).
\]

A guard target v dot z<=r is certified by the corresponding nonnegative
reserve 10^6 r-B+mathcal L(A-10^6v). A box-only target has reserve
r-sum_k max(v_k L_k,v_k U_k). The chapter on
[guard certificates](CB882_SHARP_GUARD_ROW_CERTIFICATES.md) proves these
implications. The rational reserve printed in an appendix is a lower bound;
its positivity or nonnegativity is verified against the literal sum.

Every deduction in one bound context uses the same old rows and old box.
Only after the entire batch is proved are its bounds intersected with the
old intervals. No line uses another line's conclusion to pay its own
residual. An empty intersection is a contradiction.

For a beta interval [p,q] after intersection, convert outward to w using the
rational grid G={j/65536:-32768<=j<=32768}. Its new lower endpoint is the
larger of the inherited endpoint and max{g in G:b(g)<=p}; its new upper
endpoint is the smaller of the inherited endpoint and min{g in G:b(g)>=q}.
The strictly increasing rational function b(w) on this range proves both
inclusions. The old beta enclosure guarantees the required grid endpoints
unless an intersection was already empty. Recompute the frame and inset
boxes from Section 2 afterwards. All comparisons are rational, including
ones at grid endpoints.

## 4. Complete case conventions

The indexed case table starts at N00000. Each node first applies its displayed
bound context, if any, using Section 3. Its action then uses the resulting
state. All choices and extra support normals are inherited by every child.
The exact child orders are:

| Action | Exhaustive children, in printed order |
|---|---|
| angle(i,m) or center(k,m) | Closed lower half [l,m], then closed upper half [m,u]. Their common endpoint is included in both. |
| proxy(i,j) | (axis,sign)=(0,-1),(0,+1),(1,-1),(1,+1), where axis 0 is horizontal and axis 1 vertical. |
| vertical(i,j) | Vertical sign +1, then sign -1; used only for the proved vertical pairs A/E,D/G,B/F. |
| sat(i,j) | Owner i, then j; for each owner primary axis 0, then secondary axis 1; for each axis sign -1, then sign +1. |
| CD axes | +u_C, then +v_C, then +v_D. |
| assumed CD primary | One child retaining +u_C; permitted only when that exact physical separation is a declared global root hypothesis. |
| CD angle sign | One necessary intersection: w_C>=0 for +u_C, w_C<=0 for +v_C; +v_D needs no new sign. |
| support(i,n) | One child retaining the printed exactly unit rational normal and all its original-corner halfplanes. This adds a necessary inequality, not a disjunction. |

The choice `proxy(i,j,axis,s)` means
s(c_j-c_i)_axis>=g_i+g_j. The four choices exhaust the separations of the
original contained aligned insets. The choice `sat(i,j,o,axis,s)` means that
the actual unit normal s u_o or s v_o separates the two physical originals
toward c_j-c_i, with the sum of their actual support halfwidths. The eight
choices exhaust the physical square separating-axis alternatives; owner
identity is retained. The smaller three-case CD cover and its sign conditions
are proved in Sections 2--4 of the primary-axis chapter, using the original
cone, height and strict weak bit. No unproved selection removes a child.
The single-child conditional action instead uses its explicitly stated
global hypothesis; it makes no assertion about either other C/D axis.

An angle interval entirely outside the canonical range is empty: for l>0,
l^2+2l>=1 suffices; for u<0, u^2-2u>=1 suffices. The rational endpoints
cannot equal the irrational canonical boundary. A selected C-primary case
with upper endpoint below zero, or C-secondary case with lower endpoint
above zero, is empty by the proved CD routing. The root endpoint orders and
the F-above-B theorem justify their explicitly named hand terminals.

## 5. The retained sharp and common-axis terminals

For a uniform sharp leaf, the full guard of
[the uniform terminal](CB882_UNIFORM_SHARP_TERMINAL.md) is checked: all seven
loaded absolute beta values are at most 1/10, A and D have their original
signs, and all ten displayed relative-coordinate targets hold. The BI lower
and upper allowances are at most 1/16 and 3/4. An older literal certificate with
a smaller right side is a valid stronger target. The inherited original
actual AB/EF/FG links and the positive A/E,D/G inset orders supply the
remaining physical and strict-height hypotheses.

A catalogue leaf identifies one row of
[the four-guard catalogue](CB882_SHARP_GUARD_CATALOGUE.md). It checks that
row's angle bound and all twelve relative-coordinate targets, including both
endpoint-height ceilings. Each target has its explicit vector and right side;
none can be inferred from a numerical pose. The current row 1 lower allowance
is 11/200, so older 1/20 certificates are stronger. A box-only sharp leaf checks
the same complete guard directly in its inherited or contracted box. Earlier
local and enlarged box guards are stronger subsets of this uniform guard;
every retained such leaf is checked against the full uniform targets.

Both sharp theorems force the aligned anchors. Retained actual BC then gives
x_C>=h_C; the CD cone and insets give x_C<=1-g_C. Hence h_C=g_C=1/2 and
x_D-x_C=h_C+h_D, contrary to the original strict weak CD bit.

A common-axis leaf identifies two directed selected physical edges i->j and
j->k along the identical owned side normal, with the same direction. A
negative separator sign first reverses that edge, so both resulting directed
edges use the owner's positive primary or positive secondary normal. Each support threshold is at
least 1, so the endpoint projection is at least 2 and |c_k-c_i|^2>=4. The leaf
checks from its proved box that

\[
 \sum_{ax=0}^1
 \max\{|L_{k,ax}-U_{i,ax}|,|U_{k,ax}-L_{i,ax}|\}^2<4.
\]

This contradiction requires the same original owner, side axis, and signed
normal after directing the edges; approximate agreement of two angles is
insufficient. The current proof data use no
rotated-four-chain terminal or other optional terminal family.

## 6. Completion criterion for the attached table

The root table must equal Section 1 and explicitly state any global physical
hypothesis needed by a conditional action. Every permitted pool row must be
justified by its generating family in the displayed context. Every printed
sum must pass Section 3, and every child in Section 4 must occur exactly in
the indexed tree. Every leaf must have one of the contradictions in Sections
3--5 or the explicitly cited F-order theorem. No `OPEN` entry is permitted.

Once those conditions hold, induction down the finite case tree proves that
no point satisfying the original Cb882 predicate together with the declared
global hypotheses belongs to the root. This excludes the entire conditional
domain of that cover. If there are no extra global hypotheses, it excludes
the whole original Cb882. The attached index supplies the exact node, context
and row counts; the proof consists of its printed fractions and this finite
implication argument.
