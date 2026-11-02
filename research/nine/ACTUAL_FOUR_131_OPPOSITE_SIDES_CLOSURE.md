# The opposite-side (1,3,1) occupancy: a low selected middle is impossible

November 2, 2026. Complete physical reduction and five-variable finite
scalar proof, with all 9,035 strict leaves independently replayed in exact
directed arithmetic. No Lean or CI is used.

## 1. Original physical setting and the eventual caller

Retain an actual horizontal four-chain \(M_0,M_1,M_2,M_3\) whose
consecutive center comparisons are also horizontal cone comparisons,
inside the closed disk of squared radius \(Q=1105/256\). All square
frames are independent and all original physical nonoverlap constraints
are retained. Put

\[
 l=29/60,\quad g_0=15/31,\quad \delta=331/20000.
\]

In normalized occupancy \((1,3,1)\), suppose the sole left-side
outsider is above its inner main, the sole right-side outsider B is
below its inner main, two central outsiders are above both mains and
one central outsider H is below both. Use common routing of the selected
horizontal cone triple \(L<_cP<_cR\).

The selected right endpoint cannot be B. Hence L is the sole left-side
outsider, P is negative central, and R is positive central. In particular

\[
 x_L<-11/12,\quad y_L>27/40,\quad
 -23/60<x_P<-13/60,
 \quad 19/60<x_R<l.                              \tag{1}
\]

The two cone gaps and the outsider strip imply the useful two budgets
on the one original P frame:

\[
              g_P-11/15<x_P<2/15-g_P.            \tag{2}
\]

The left budget follows from
\(x_P\ge x_L+g_L+g_P>-13/12+7/20+g_P\).
The right follows from
\(x_P\le x_R-g_P-g_R<l-g_P-7/20\).

The scalar theorem below retains only the original mains, P, H and B.
It proves

\[
                              y_P>3/5.           \tag{3}
\]

Once (3) is available, the accepted far-left/high-middle argument in
Section 3 of `ACTUAL_FOUR_140_THREE_UPPER_ONE_LOWER_CLOSED_HAND_PROOF.md`
applied to the same original L,P gives \(y_P-h_P>1/10\).

For completeness, R is a high right shoulder independently. Since B is
below M2, the one-sided main-height theorem gives \(y_2>-7/20\).
Adding both selected cone gaps gives

\[
 x_R-g_R\ge x_L+g_L+2g_P>-13/12+21/20=-1/30.
\]

Thus the horizontally reflected coupled cone-loss theorem applies to R:
its reflected coordinate satisfies \(-x_R+g_R<1/30<J=23/150\).
It gives \(y_R-h_R>1/10+13/4960\), and hence \(y_R>3/5\).
The original L,P,R therefore meet the widened five-square cap. In the
normalized strict-counterexample setting its conclusion \(D\le2\)
contradicts the retained actual-four endpoint span \(D>2\).

The rest of this document proves (3) using the original seven-unit
necessary predicate, rather than imposing any new condition on P.

## 2. Complete inset clearances, and elimination of x_P

For a folded physical slope \(t\in[0,1]\), write

\[
 d=\sqrt{1+t^2},\quad a=1/d,\quad b=t/d,
 \quad h=(a+b)/2,\quad k=(a-b)/2,\quad g=1/(4h).
\]

The main inset bounds are

\[
 g_1,g_2>g_0,\quad x_1+g_1>-\delta,
 \quad x_2-g_2<\delta,\quad x_2+g_2>59/60.
\]

Use the full physical clearance formula established in Sections 2--3 of
`CENTRAL_SINGLETON_FLOOR_HAND_TABLE_PROOF.md`:

\[
 \Lambda(s,t)=\max\{0,t(k+s),(s-k)/t\}\quad(t>0),
 \qquad \Lambda(s,0)=0\quad(s<1/2).             \tag{4}
\]

The original center-chord order excludes reversed vertical facets;
horizontal separation is impossible in the stated inset ranges.
Both chiralities and both unit-owned axis slopes are included. A unit
above an inset of halfwidth \(g_i\), at horizontal center gap D,
has vertical clearance at least
\(g_i+h-\Lambda(s,t)\) whenever \(s\ge D-g_i\).
The same formula applies after vertical reflection below that main.

For an upper negative central P, the left loss is
\(\max\{0,t_P(k_P+\delta+x_P)\}\), and the right loss is
\(\Lambda(\delta-x_P,t_P)\). Use the two upper bounds from (2):

\[
 \begin{aligned}
 r(t_P)&=\max\{0,t_P(k_P+\delta+2/15-g_P)\},\\
 p(t_P)&=\Lambda(\delta+11/15-g_P,t_P).
 \end{aligned}                                  \tag{5}
\]

These bound the two losses simultaneously for the same actual P frame.
They deliberately allow their separate worst x_P values; this weakens the
necessary system and does not add a geometric premise. No x_P variable
remains.

The two inequalities (2) require \(g_P\le13/30\), so
\(h_P\ge15/26\). Since h increases on \([0,1]\), and

\[
 (15/26)^2-h(1/6)^2=225/676-49/148=11/6253>0,
\]

every physical caller has \(t_P>1/6\). The closed cover therefore
only needs \(1/6\le t_P\le1\).

## 3. Both original lower units acquire explicit center lower bounds

Suppose, toward a contradiction, that \(y_P\le3/5\). Reflect H
and B vertically, writing their positive center heights as
\(Y_H=-y_H\), \(Y_B=-y_B\), their horizontal coordinates as
\(x\in[-l,l]\), \(z\in[l,13/12]\), and their folded slopes as
\(t_H,t_B\in[0,1]\).

For H put

\[
 H_L=\Lambda(x+\delta,t_H),\qquad
 H_R=\Lambda(-x+\delta,t_H).
\]

For B the horizontal distance from the right main inset is bounded by

\[
 s_B=\max\{z-59/60,\delta-z\}\le1/10.
\]

Because \(s_B<g_B\), the steep term of (4) is no larger than the
shallow term. Thus its right-main loss is bounded by

\[
                         b_B=\max\{0,t_B(k_B+s_B)\}.       \tag{6}
\]

Adding the original P/H clearances through each of the two independent
main insets, and P/B through the right main, gives

\[
 \begin{aligned}
 Y_H&\ge2g_0+h_P+h_H-3/5-\min\{r+H_L,p+H_R\},\\
 Y_B&\ge2g_0+h_P+h_B-3/5-p-b_B.
 \end{aligned}                                           \tag{7}
\]

There are useful additional positive lower bounds. P's own-half central
disk clearance exceeds \(59/60\), so \(y_1<-23/60\).
Every central H below M1 has vertical gap greater than \(g_1\).
Hence \(Y_H>g_0+23/60\). P's horizontal distance to the right
main inset is below \(1/2\), so \(y_2<3/5-g_2\). The lower
right-side B has vertical main clearance greater than \(29/30\),
giving \(Y_B>g_0+11/30\).

Define the necessary lower bounds

\[
 \begin{aligned}
 A_H&=\max\{2g_0+h_P+h_H-3/5-\min(r+H_L,p+H_R),
                         g_0+23/60\},\\
 A_B&=\max\{2g_0+h_P+h_B-3/5-p-b_B,
                         g_0+11/30\}.
 \end{aligned}                                           \tag{8}
\]

Finally, the original B below M2 forces \(y_2>-7/20\).
The P/right-main clearance and \(y_P\le3/5\) therefore require

\[
                         19/20-g_0-h_P+p\ge0.              \tag{9}
\]

All three original P,H,B frames remain independent. Only the main center
heights and P's horizontal coordinate have been eliminated.

## 4. Original circle constraints and both lower-unit separator owners

For \(X\ge0\), define

\[
 \begin{aligned}
 U_+(X,t)&=\min\{\sqrt{Q-(X+k)^2}-h,
                         \sqrt{Q-(X+h)^2}+k\},\\
 U_-(X,t)&=\min\{\sqrt{Q-(X-k)^2}-h,
                         \sqrt{Q-(X+h)^2}-k\},\\
 M(X,t)&=\min\{\sqrt{Q-1/4}-1/2,\max(U_+,U_-)\}.
 \end{aligned}                                           \tag{10}
\]

Every original contained unit at positive center height Y satisfies
\(Y\le M(|x|,t)\). The two U branches are the two physical
chiralities, obtained from two actual corners in each case; the maximum
retains both. This is the same full corner bound used in the accepted
central singleton-floor certificate.

Set

\[
 M_H=M(|x|,t_H),\quad M_B=M(z,t_B),\quad
 D=z-x,\quad V=\max\{0,M_B-A_H,M_H-A_B\}.
\]

If (8) is compatible with the original circle constraints, then
\(D\ge0\) is the actual horizontal center gap and V bounds the
absolute vertical center gap. In any unit-owned separating normal of
H or B the actual support sum is at least

\[
 \sigma=\frac12\left(1+
 \frac{1+t_Ht_B+|t_H-t_B|}{\sqrt{1+t_H^2}\sqrt{1+t_B^2}}\right).
                                                        \tag{11}
\]

The folded relative angle is at least the difference of the folded
absolute angles, and cosine plus sine increases on \([0,\pi/4]\),
which proves this lower bound for either actual chirality. All four
actual owned-axis center projections are bounded by

\[
 W=\max\{a_HD+b_HV,b_HD+a_HV,a_BD+b_BV,b_BD+a_BV\}.
\]

Physical nonoverlap of the original H,B therefore requires
\(W-\sigma\ge0\). No physical pair owner has been fixed or omitted.

## 5. The original right endpoint further constrains B

The actual right endpoint contains the fixed aligned rectangle centered
at \((3/2,0)\), of horizontal halfwidth \(217/480\) and vertical
halfheight \(221/600\). These are the inherited uniform endpoint
inset bounds; the same rectangle remains after reflecting the lower B.

Put

\[
 d_E=3/2-z-217/480,\qquad v_E=M_B-221/600.
\]

The separating-axis theorem for this rectangle and the actual B square
requires at least one nonnegative quantity among

\[
 d_E-h_B,\quad v_E-h_B,\quad
 a_Bd_E+b_Bv_E-1/2,\quad b_Bd_E+a_Bv_E-1/2.
\]

Using positive absolute components in the latter two expressions allows
both original chiralities and every sign. Define their maximum as E.
Then original endpoint/B disjointness necessarily gives \(E\ge0\).

## 6. A complete five-variable compact domain

All remaining variables lie in the closed box

\[
 \boxed{(x,z,t_P,t_H,t_B)\in
 [-29/60,29/60]\times[29/60,13/12]\times[1/6,1]
                  \times[0,1]\times[0,1].}                \tag{12}
\]

Every physical counterexample to (3) makes all six quantities

\[
 13/30-g_P,\quad M_H-A_H,\quad M_B-A_B,\quad
 W-\sigma,\quad E,\quad19/20-g_0-h_P+p                  \tag{13}
\]

nonnegative. The finite cover proves that the minimum of (13) is
strictly negative throughout (12).

The only removable singularity in the formulas is (4) at t=0. For exact
evaluation set \(\epsilon=1/10000\) and replace its denominator t
by \(\max(t,\epsilon)\). This does not change \(\Lambda\)
anywhere used in the proof. Indeed every s is at most
\(l+\delta=1/2-7/60000\). For \(0\le t\le\epsilon\),

\[
 k\ge1/2-t/2-t^2/4
 \ge1/2-\epsilon/2-\epsilon^2/4>s,
\]

because

\[
 7/60000-\epsilon/2-\epsilon^2/4
                      =79997/1200000000>0.
\]

Thus the protected steep term is nonpositive and contributes nothing to
the maximum, including t=0. Above epsilon the denominator is unchanged.
Aligned original H or B frames are therefore fully covered.

The direct evaluator uses the monotonicity of each frame quantity:
a and k decrease with t, whereas b, h and d increase. Their exact
interval values therefore come from independently enclosed values at
the two slope endpoints. In particular \(h\in[1/2,17/24]\) and
\(k\in[0,1/2]\). All square-root arguments are positive even on the
full box; the smallest crude bound is
\(Q-(13/12+17/24)^2>0\). The support lower bound in (11) is also
intersected with its universal lower bound one; pointwise this does not
change (11), and it only sharpens interval evaluation.

## 7. Meaning of each finite-table leaf

The discovery producer uses untrusted floating interval calculations to
choose coordinate bisections and candidate terminal rules. Its numerical
values are not proof premises. The saved tree has one integer per node:
a nonnegative coordinate index requests exact midpoint bisection; a
negative integer selects one of the six necessary inequalities (13).

The separate exact checker imports no producer code. It rebuilds
(4)--(13), uses an independent directed integer arithmetic kernel with
64 fractional bits, and encloses every radical outward. Starting from
the rational box (12), it reconstructs every exact midpoint box,
checks that the tree exhausts the root with no extra or missing node,
and recomputes the selected inequality at every terminal. Every
terminal must have a strictly negative direct interval upper bound.
No mean-value or hand-only terminal remains in the accepted table.

The protected denominator argument covers every original angle endpoint.
The produced floating boxes and their floating arithmetic reserves are
never accepted as evidence by the exact checker.

## 8. Exact replay record

The certificate is `131_opposite_low_middle_direct_cover.json.gz`,
discovered by `discover_131_opposite_low_middle.cpp` and replayed by the
separate `verify_131_opposite_low_middle_direct.py`. The complete replay
report is `131_opposite_low_middle_direct_replay.json`:

* 18,069 exact midpoint-tree nodes;
* 9,035 strict direct interval leaves;
* maximum depth 24;
* terminal counts in the order (13): \((0,3226,3520,2289,0,0)\);
* largest replayed upper bound
  \(-5250650345271/9223372036854775808<0\).

The compressed certificate SHA-256 is
`2bf75ca014ec2e9d3718f9014e22ce138387385aee7e28c14819b126306daf90`.
The exact checker SHA-256 is
`1293a95e46ec7d49056fdd6712fc2150a6231545c1be3fb33402beb347e0f3f8`.

Thus (13) cannot hold simultaneously anywhere in (12), proving (3).
Section 1 then supplies every widened-cap hypothesis from original units
and closes the entire opposite-side (1,3,1) split with two central upper
and one central lower outsider. The arithmetic replay is an independently
implemented computation, not a human or proof-kernel certification.
