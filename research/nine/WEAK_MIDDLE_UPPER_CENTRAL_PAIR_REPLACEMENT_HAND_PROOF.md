# Two upper central originals supply a whole floor with a weak middle link

November 2, 2026. Computer discovery, complete exact replay, and physical
hand/table proof. No Lean, Lake, or CI.

## 1. The physical theorem

Put \(Q=1105/256\), \(\rho=91/60\), and \(l=29/60\).
Retain four original physical unit squares A,B,C,D in horizontal
center-cone order in the closed Q-disk. Their outer links A--B and
C--D are actual horizontal projection comparisons; their middle link
may be actual or weak. Retain two distinct original squares F,G with

\[
 |x_F|,|x_G|\le l,\qquad
 y_G\ge y_F>\max(y_B,y_C),\qquad |x_G-x_F|\le1/2.
\]

**Theorem.** The higher original square has whole floor

\[
                         y_G-h_G>1/10.                 \tag{1}
\]

Every original independent orientation, physical separating-axis owner,
and touching boundary is retained. Neither an outsider cone triple nor
an outsider occupancy count is a premise.

## 2. The main and endpoint resources

Write \(g_M=1/(4h_M)\), \(\eta_M=h_M+g_M-1\), and
\(V=\eta_B+\eta_C\). The accepted outer-actual endpoint theorem gives

\[
 1/2\le h_B,h_C<13/20,\qquad 0\le V<1/30,
\]

\[
 b_-=h_B-61/60<x_B<1/60-g_B-\eta_C=b_+,
\]

\[
 c_-=g_C+\eta_B-1/60<x_C<61/60-h_C=c_+.
                                                        \tag{2}
\]

Both intervals have length \(1/30-V\). The two outer endpoints obey
\(X+Y<129/80\), where \(X=|x_E|\), \(Y=|y_E|\).
This is exactly the corner argument in Section 1 of
`UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md`: its only
chain inputs are \(X>89/60+(h_E-1/2)\) and \(h_E<8/15\), both
supplied by the outer-actual theorem. Thus the actual outer cones give

\[
 y_B>-129/80-x_B,\qquad y_C>-129/80+x_C.           \tag{3}
\]

For \(U=h_A+h_D-1\), the same theorem gives

\[
 |y_A|+|y_D|+(37/50)U+(32/9)V\le1/8.
\]

Since \(|x_A|+|x_D|<2\rho\), the averaged outer resource is

\[
 \frac{|x_A|+|x_D|-y_A-y_D}{2}
       <379/240-(16/9)V.                              \tag{4}
\]

The wide-main own-half-plane clearance, combined with
\(y_B,y_C>-6/5\), gives \(y_F>-3/10\). These two deductions are
proved without either short-link premise in Sections 1--2 of
`WEAK_MIDDLE_BOTH_WEAK_COMMON_REDUCTIONS.md`.

## 3. A complete original-pair clearance function

Fold a square's original side components to \(a\ge b\ge0\), with
\(a^2+b^2=1\). For two such frames \(s=(a,b)\), \(t=(c,d)\), put

\[
 \sigma(s,t)=\frac{1+ac+bd+|ad-bc|}{2}\ge1.
\]

This is a lower bound for the actual support sum on every original
owned separating axis. For folded angles \(\alpha\ge\beta\), the
opposite-chirality sum exceeds the same-chirality sum by
\(2\sin\beta(\cos\alpha-\sin\alpha)\ge0\). Quarter turns and
normal signs therefore cause no missing frame case.

For a nonnegative horizontal gap bound D, take the minimum over

\[
                    (p,q)=(a,b),(b,a),(c,d),(d,c)
\]

of \(\max(0,(\sigma-pD)/q)\) when \(q>0\). If \(q=0\) and
\(\sigma-pD>0\), omit that impossible owner; if \(q=0\) and the
numerator is nonpositive, include zero. Call the resulting minimum
\(K(s,t,D)\). The original separating-axis theorem implies

\[
                         |\Delta y|\ge K(s,t,D).      \tag{5}
\]

The function K is nonnegative and nonincreasing in D. Every original
owner and both chiralities have been relaxed in a necessary direction.

For the central/main gaps in (2), D is at most one. Since
\(\sigma\ge1\) and \(p\le1\), each finite numerator is nonnegative.
For fixed frames and central x, each finite expression
\(K(s,t,|x-z|)\) is the minimum of concave functions of z. Adding z
or -z preserves concavity. Its minimum over a main-position interval
therefore occurs at an endpoint. An owner with zero vertical component
can become possible only at D=1, already an interval endpoint; its zero
value is explicitly included there. No concavity outside D<=1 is used.

## 4. Eliminate all but five parameters

Let x=xF and define

\[
 L=\min_{z\in\{b_-,b_+\}}[-z+K(B,F,|x-z|)],
\quad
 R=\min_{z\in\{c_-,c_+\}}[z+K(C,F,|x-z|)].
\]

Here a square name in K means its retained original folded frame.
Equations (3)--(5), the endpoint minimum rule, and the average (4) give

\[
 y_F\ge-129/80+L,\qquad y_F\ge-129/80+R,
\]

\[
 y_F\ge-379/240+(16/9)V+(L+R)/2.                    \tag{6}
\]

Retaining physical separation of B and C is essential. Put

\[
 K_B=K\left(B,F,\max_{z\in\{b_-,b_+\}}|x-z|\right),
\quad
 K_C=K\left(C,F,\max_{z\in\{c_-,c_+\}}|x-z|\right),
\]

\[
                         M=K(B,C,c_+-b_-).
\]

If C is higher than B, first use their original separation and then
C/F separation. This gives \(y_F\ge-129/80-b_++M+K_C\).
If B is higher, it gives \(y_F\ge-129/80+c_-+M+K_B\).
The union of both original height orders therefore gives

\[
 Y_{\rm mid}=M-129/80+\min(-b_++K_C,c_-+K_B)\le y_F.
                                                        \tag{7}
\]

Set

\[
 Y=\max\{-3/10,-129/80+L,-129/80+R,
       -379/240+(16/9)V+(L+R)/2,Y_{\rm mid}\}.
\]

Equations (5)--(7) and the original F/G pair imply

\[
              y_G-h_G\ge Y+K(F,G,1/2)-h_G.            \tag{8}
\]

For a main, its folded components are
\(a=h+\sqrt{1/2-h^2}\), \(b=h-\sqrt{1/2-h^2}\).
For F and G use \(t=b/a\in[0,1]\), so
\(a=1/\sqrt{1+t^2}\), \(b=ta\).
Horizontal reflection exchanges B,C and changes x to -x. The complete
remaining closed parameter rectangle is consequently

\[
 (h_B,h_C,t_F,t_G,x)\in
 [1/2,13/20]^2\times[0,1]^2\times[0,29/60].           \tag{9}
\]

## 5. Complete exact scalar table

The entire rectangle (9) is covered by the binary midpoint tree in
`wide_central_pair_candidate.json`. The two possible leaf conclusions
are the following strict rational inequalities:

| Leaf conclusion | Number of leaves |
|---|---:|
| V>1/30, excluding that orientation box | 69 |
| The right side of (8) exceeds 1/10 | 43,262 |
| Total | 43,331 |

Every root endpoint, shared bisection face, and zero-slope frame is
included. There are 86,661 nodes, maximum depth 26, and no unprocessed
frontier. The tree contains all split-axis and terminal records needed
to reconstruct every rational box; none is selected by floating output
during replay.

`verify_wide_central_pair.py` independently reconstructs the formulas
above. It uses 64 fractional bits with directed integer rounding, exact
rational tree endpoints, and integer square roots. It imports no
numerical producer. Monotone frame functions are bounded at their exact
endpoints; all distance arguments are rounded upward, clearance values
downward, and hG upward. For zero vertical owners it uses precisely the
exact cases in Section 3, with no tolerance.

The complete exact replay passed, with least positive reserve

\[
             112318305826923/92233720368547758080>0.
\]

Certificate SHA256:
`ed365f824ba9027ee4472e3d1b34412a3dce5711279a234e9ef61eabd880d6e0`.
The complete binary-tree skeleton is checked before arithmetic replay.
Four changed-root, illegal-axis, missing-child, and false-terminal
controls were all rejected. The separate independent physical and code
review is `WIDE_MIDDLE_PAIR_RELAXATION_INDEPENDENT_REVIEW.md`.

Every physical point belongs to (9) and has V<1/30. Its leaf therefore
proves the second alternative. Equation (8) proves (1).

## 6. Useful count consequences

Call an upper central original good when its whole floor exceeds 1/10.
A good square has center height greater than 3/5, since h>=1/2.
The accepted upper-column separation theorem states that two original
squares with center heights at least 3/5 have horizontal center gap
strictly greater than l.

**There are at most two upper central originals in each closed horizontal
half-plane.** Otherwise order three in one half by center height. Apply
(1) to the lowest and each of the other two: both higher originals are
good. Their horizontal gap is at most l, contradicting upper-column
separation. Equality of their heights is already impossible for distinct
original units whose horizontal gap is below one.

Thus three upper central originals include one of each strict horizontal
sign, and at least one is good: among their x-ordered coordinates an
adjacent gap is at most l<1/2. Four upper central originals consist of
exactly two negative and two positive originals, with none at x=0.
The higher original in each same-sign pair is good.

These count conclusions need no lower bound inherited from a narrow
inner-main frame. They apply to the full outer-actual weak-middle domain.

## 7. A complete occupancy consequence for 010/11

Suppose the outsider count is (1,4,0) and all four central originals are
above both mains. Common routing of the selected cone triple gives a
left-side original L with yL>27/40, and two selected central originals
of opposite horizontal signs. From Section 6 select the good higher
negative original U and the good higher positive original R.
The three originals L,U,R are distinct and obey

\[
 x_L<0<x_R,\quad |x_U|<l,\quad
 y_L,y_R>3/5,\quad y_U-h_U>1/10.
\]

These are the widened five-square cap's hypotheses, with the original
main endpoints. All endpoint resources required by that cap follow from
the outer-actual theorem. The cap gives
\(\mathcal D=x_D-x_A-h_A-h_D\le2\).
But the main span gives \(\mathcal D\ge2+V\), and a genuinely weak
middle link forces V>0. Indeed V=0 would align both inner mains, whose
weak horizontal gap and cone vertical gap would then both be below one,
contradicting their original physical disjointness. This is impossible.

Consequently this complete four-upper occupancy family, and its
horizontal reflection, is excluded even in the closed Q-disk. The other
height splits and other occupancy counts of 010/11 remain separate
gates. No whole-mask ledger entry is changed by this lemma alone.
