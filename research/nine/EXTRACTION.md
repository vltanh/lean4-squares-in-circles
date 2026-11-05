# Exhaustive center-cone extraction

This chapter proves the extraction required by G2 of the
[roadmap](PROOF_PLAN.md). Its only imported combinatorial theorem is the
precisely stated finite-poset theorem of Greene in Section 4. The geometric
estimates and the rotating-frame and event arguments are written below.
They apply to the same nine independently oriented original squares,
including configurations with boundary contact. They do not supply the
unrestricted geometric closure required by G4.

## 1. Statement and elementary physical inputs

Put

\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q,\qquad \rho=\frac{91}{60}.
\]

Let nine unit squares with pairwise disjoint open interiors be contained
in the closed disk of radius \(r\), centered at zero. The same conclusions
apply to a packing in any smaller concentric disk.

**Extraction theorem.** There is an orthonormal coordinate frame and a
labeling of all nine originals as

\[
 A,B,C,D;E,F,G;H,I
\]

such that the five directed differences on

\[
 AB,\quad BC,\quad CD;\quad EF,\quad FG
\]

satisfy \(\Delta x\ge |\Delta y|\). Every nonconsecutive pair in either
chain has disjoint physical projection interiors in the \(x\)-direction.
One of the five displayed differences satisfies
\(\Delta x=|\Delta y|>0\). After explicit common isometries and relabeling,
the marked difference may be taken to be one of \(AB,BC,EF\), with
\(\Delta y=\Delta x>0\).

All nine original frames, all 36 pairwise nonoverlap conditions and all
36 corner-containment conditions are retained. The conclusion does not
assert physical projection separation on a consecutive cone edge.

For one square, write its orthonormal side axes as \(u,v\), its center
as \(c=(x,y)\), and its projection halfwidth on either coordinate axis as
\(h\). The two coordinate halfwidths are equal because the square's axes
are perpendicular. Define

\[
 \frac12\le h\le\frac1{\sqrt2},\quad
 k=\sqrt{\frac12-h^2},\quad
 a=h+k,\quad b=h-k,\quad g=\frac1{4h}.
\tag{1}
\]

Here \(a\ge b\ge0\), \(a^2+b^2=1\), and \(a,b\) are the absolute
components of an appropriate physical side axis, in decreasing order.

The concentric coordinate-aligned square of halfwidth \(g\) is contained
in the original. Indeed each of its points \(z\) satisfies

\[
 |u\cdot z|,|v\cdot z|\le (a+b)g=2hg=\frac12.
\tag{2}
\]

Its open interior lies in the original's open interior. Consequently two
such insets cannot overlap in both coordinate interiors. Their center
coordinates therefore obey at least one of

\[
 |\Delta x|\ge g_S+g_T,
 \qquad |\Delta y|\ge g_S+g_T.
\tag{3}
\]

These insets are used only to obtain inequalities for the originals.

For the center norm \(t=|c|\), the largest squared corner norm is

\[
 t^2+\frac12+|c\cdot u|+|c\cdot v|
 \ge t^2+t+\frac12.
\]

Since

\[
 \rho^2+\rho+\frac12-Q=\frac{31}{57600}>0,
\]

containment implies \(|c|<\rho\). Distinct originals have distinct
centers: their open incircles have radius \(1/2\), and disjointness even
implies that their center distance is at least one.

We also use the elementary separating-axis criterion for two convex
squares: if their open interiors are disjoint, one of their four physical
side-normal directions separates their projection interiors, with equality
allowed. It follows directly by separating the interiors and using a face
of the polygonal difference body. If the relative angle of the two square
frames, reduced modulo their quarter-turn and reflection symmetries, is
\(\Delta\in[0,\pi/4]\), then on each candidate axis the sum of their
support halfwidths is
\((1+\cos\Delta+\sin\Delta)/2\). Thus

\[
 |c_S-c_T|\ge\frac{1+\cos\Delta+\sin\Delta}{2}.
\tag{4}
\]

## 2. A unary inset bound

**Lemma 2.1.** Every original satisfies

\[
 |x|-g<\frac{17}{16},\qquad |y|-g<\frac{17}{16}.
\tag{5}
\]

*Proof.* It suffices to consider \(X=|x|\). In physical side
coordinates \((U,V)\), containment gives

\[
 (|U|+1/2)^2+(|V|+1/2)^2\le Q,
 \qquad X\le a|U|+b|V|.
\]

Maximizing the latter expression over this quarter-disk gives

\[
 X\le
 \begin{cases}
 r-h,&rb\ge1/2,\\
 a(\sqrt{Q-1/4}-1/2),&rb<1/2.
 \end{cases}
\tag{6}
\]

To verify the maximization, set \(P=|U|+1/2\), \(Z=|V|+1/2\).
The unconstrained circle maximum is at \((P,Z)=r(a,b)\). It is feasible
exactly when \(rb\ge1/2\). Otherwise \(Z=1/2\) is active and
\(P=\sqrt{Q-1/4}\). The constraint \(P\ge1/2\) does not bind,
since \(a\ge1/\sqrt2\) and \(r>2\).

In the first branch, \(h>3/5\). Otherwise

\[
 b\le\frac35-\sqrt{\frac7{50}}<\frac{23}{100}
 <\frac6{25}<\frac1{2r},
\]

contradicting that branch. The rational comparisons used here are
\(1400>1369\), to bound \(\sqrt{7/50}>37/100\), and
\(159120<160000\), to bound \(r<25/12\). Since
\(h+1/(4h)\) is nondecreasing for \(h\ge1/2\),

\[
 X-g\le r-h-g\le r-\frac{61}{60}
 <\frac{499}{240}-\frac{61}{60}=\frac{17}{16}.
\]

Here \(r<499/240\) is the exact squared comparison
\(248625<249001\).

In the second branch,

\[
 \sqrt{Q-1/4}-\frac12
 =\frac{\sqrt{1041}-8}{16}<\rho,
\]

because \(234225<234256\). Consequently

\[
 X-g<F(h):=\rho\bigl(h+\sqrt{1/2-h^2}\bigr)-\frac1{4h}.
\]

For \(1/2<h<1/\sqrt2\),

\[
 F''(h)=-\frac{\rho}{2k^3}-\frac1{2h^3}<-7.
\tag{7}
\]

Indeed \(k\le1/2\) and \(h\le1/\sqrt2\), so the magnitudes of the
two negative terms sum to at least \(4\rho+\sqrt2>7\). Take
\(h_0=119/202\), \(k_0=79/202\); these satisfy
\(h_0^2+k_0^2=1/2\). The needed arithmetic is

| Quantity | Exact value or comparison |
|---|---|
| \(F(h_0)\) | \(255347/240380\) |
| \(F'(h_0)\) | \(10201/14161-182/237=-159665/3356157\) |
| \(\lvert F'(h_0)\rvert<1/20\) | \(3193300<3356157\) |
| \(17/16-F(h_0)\) | \(227/961520\) |
| \(227/961520>1/5600\) | \(1271200>961520\) |

Integrating (7) between \(h_0\) and \(h\), and completing the square,
gives

\[
\begin{aligned}
 F(h)&\le F(h_0)+F'(h_0)(h-h_0)-\frac72(h-h_0)^2\\
 &\le F(h_0)+\frac{F'(h_0)^2}{14}
 <F(h_0)+\frac1{5600}<\frac{17}{16}.
\end{aligned}
\]

Continuity handles both endpoints of the \(h\)-interval. This proves
(5). \(\square\)

## 3. Cone orders and the exclusion of five-chains

In any frame define, for distinct originals,

\[
 S\prec_x T\iff x_T-x_S\ge|y_T-y_S|,
 \qquad
 S\prec_y T\iff y_T-y_S\ge|x_T-x_S|.
\tag{8}
\]

Each displayed positive-coordinate gap is strictly positive because
centers are distinct. The triangle inequality proves transitivity.
Thus these are strict partial orders. Every pair is compared by at least
one of them, by choosing a coordinate of largest absolute center gap.
At a diagonal tie, both applicable comparisons are retained.

By (3), every \(x\)-cone comparison satisfies
\(x_T-x_S\ge g_S+g_T\). Any two-step \(x\)-cone chain therefore gives

\[
 x_U-x_S\ge g_S+2g_T+g_U
 \ge\sqrt2\ge h_S+h_U.
\tag{9}
\]

This is an actual physical projection comparison of its two endpoint
originals. The same conclusion holds in \(y\). The proof does not
promote a single consecutive cone comparison to actual separation.

**Lemma 3.1.** Each cone order has height at most four in every frame.

*Proof.* Suppose \(A\prec_x B\prec_x C\prec_x D\prec_x E\).
Summing their four inset gaps and applying (5) to the endpoints yields

\[
 2(g_B+g_C+g_D)
 \le (x_E-g_E)-(x_A+g_A)<\frac{17}{8}.
\tag{10}
\]

All inset halfwidths are at least \(1/(2\sqrt2)\). If one of
\(h_B,h_C,h_D\) were at most \(45/64\), the corresponding inset
halfwidth would be at least \(16/45\), giving

\[
 g_B+g_C+g_D\ge\frac{16}{45}+\frac1{\sqrt2}
 >\frac{16}{45}+\frac{509}{720}=\frac{17}{16}.
\]

The strict comparison is \(259200>259081\). Hence, for these three
internal squares,

\[
 h_j>\frac{45}{64}>\frac7{10},\qquad
 k_j^2<\frac{23}{4096}<\frac9{1600},\qquad k_j<\frac3{40}.
\tag{11}
\]

The second rational comparison is \(36800<36864\).

Put \(p_0=3/\sqrt2-17/16\). The four inset gaps show that

\[
 (-x_A-g_A)+(x_E-g_E)\ge\frac3{\sqrt2}.
\]

Each parenthesized quantity is less than \(17/16\), by (5). Therefore

\[
 -x_A-g_A>p_0>\frac{127}{120}>0,
 \qquad x_E-g_E>p_0.
\tag{12}
\]

For the middle strict comparison, square
\(3/\sqrt2>509/240\), obtaining \(259200>259081\). In particular
\(x_A<0<x_E\).

We next show that \(h_A<49/80\). Let \(X=-x_A\). If the first
branch of (6) applies and \(h_A\ge49/80\), then

\[
\begin{aligned}
 X-g_A&\le r-h_A-g_A\\
 &\le r-\frac{49}{80}-\frac{20}{49}
 <\frac{133}{64}-\frac{4001}{3920}
 =\frac{16581}{15680}<\frac{127}{120},
\end{aligned}
\]

contradicting (12). The comparisons are \(17680<17689\) for
\(r<133/64\), and \(1989720<1991360\) for the final fractions.

If the second branch applies, use \(X-g_A<F(h_A)\). At \(h=49/80\),
\(k=\sqrt{799}/80<17/48\), because \(1840896<1849600\). Thus

\[
 F(49/80)<\frac{91}{60}\frac{29}{30}-\frac{20}{49}
 =\frac{93311}{88200}<\frac{93345}{88200}=\frac{127}{120}.
\]

Moreover

\[
 F'(49/80)<-\frac{2821}{2550}+\frac{1600}{2401}<0,
\]

where the last comparison is \(4080000<6773221\). Strict concavity
from (7) makes \(F\) decreasing thereafter. This again contradicts
(12) if \(h_A\ge49/80\).

On \([1/2,1/\sqrt2]\), \(h+\sqrt{1/2-h^2}\) is nonincreasing and
\(h-\sqrt{1/2-h^2}\) is increasing. Since
\(\sqrt{799}/80>7/20\), equivalent to \(799>784\), the preceding
bound implies

\[
 a_A>\frac{77}{80}>\frac{24}{25},
 \qquad b_A<\frac{21}{80}<\frac4{15}.
\tag{13}
\]

The last two comparisons are \(1925>1920\) and \(315<320\).

There are three inset gaps from \(B\) to \(E\). Therefore

\[
 x_B\le x_E-g_E-g_B-2g_C-2g_D
 <\frac{17}{16}-\frac5{2\sqrt2}< -\frac{169}{240}.
\tag{14}
\]

The final comparison follows from \(5/(2\sqrt2)>53/30\), whose
square is \(5625>5618\). As \(x_A>-\rho\),

\[
 0<x_B-x_A<\frac{91}{60}-\frac{169}{240}=\frac{13}{16}.
\]

The cone comparison also gives \(|y_B-y_A|\le x_B-x_A\). Hence

\[
 |c_B-c_A|<\frac{13\sqrt2}{16}<\frac{23}{20},
\tag{15}
\]

where the final squared comparison is \(67600<67712\).

For the reverse bound choose folded side angles
\(\alpha,\beta\in[0,\pi/4]\) for \(A,B\), so that
\(a_A=\cos\alpha\), \(b_A=\sin\alpha\), and similarly for \(B\).
Since \(h_B>45/64>49/80>h_A\), monotonicity of
\((\cos t+\sin t)/2\) implies \(\beta>\alpha\).

For equal chiralities, the cosine-plus-sine of the relative frame angle
is \(2h_Ba_A-2k_Bb_A\). For opposite chiralities it is
\(2h_Ba_A+2k_Bb_A\). Reducing the latter angle modulo square symmetries
does not change its cosine-plus-sine. Applying (4) and the weaker of
these two expressions gives

\[
\begin{aligned}
 |c_B-c_A|
 &\ge\frac12+h_Ba_A-k_Bb_A\\
 &>\frac12+\frac7{10}\frac{24}{25}
       -\frac3{40}\frac4{15}
 =\frac{144}{125}>\frac{23}{20}.
\end{aligned}
\tag{16}
\]

The last comparison is \(2880>2875\). This contradicts (15).
Interchanging the coordinate axes proves the same height bound for
\(\prec_y\). \(\square\)

An \(x\)-antichain is a \(y\)-chain: every pair in it must be compared
by the \(y\)-order, and that order is transitive. The converse holds as
well. Thus both cone orders also have width at most four.

## 4. The exact finite-poset input and its nine-element consequence

The following is the sole imported combinatorial theorem.

**Greene's finite-poset partition theorem.** For a finite poset \(P\),
let \(c_k\) be the largest cardinality of a union of at most \(k\)
chains, and let \(a_k\) be the analogous maximum for antichains. Set
\(c_0=a_0=0\), and extend both sequences by \(|P|\) after they
stabilize. Then

\[
 \lambda=(c_1-c_0,c_2-c_1,\ldots),
 \qquad \mu=(a_1-a_0,a_2-a_1,\ldots)
\]

are decreasing partitions after zero terms are removed, and they are
conjugate:

\[
 \mu_j=\#\{i:\lambda_i\ge j\}.
\tag{17}
\]

The source is Curtis Greene, *Some partitions associated with a partially
ordered set*, Journal of Combinatorial Theory, Series A **20** (1976),
69–79, [DOI 10.1016/0097-3165(76)90078-9](https://doi.org/10.1016/0097-3165(76)90078-9).
The [publisher's abstract](https://www.sciencedirect.com/science/article/pii/0097316576900789)
states the conjugate-partition result for arbitrary posets; the
[author's publication record](https://scholarship.haverford.edu/mathematics_facpubs/150/)
confirms the bibliographic reference. No restriction to graded,
permutation, or dimension-two posets is imposed. We import this theorem,
not a claim that a single chain partition realizes all the maxima.

**Lemma 4.1.** A nine-element poset of height four and width at most four
has disjoint chains of lengths four and three, or disjoint antichains of
lengths four and three.

*Proof.* If \(c_2\ge7\), take two chains realizing a union of at least
seven elements, and delete their intersection from one of them. Each
remaining chain has at most four elements, so their two disjoint sizes are
\((4,3),(3,4)\), or \((4,4)\). In the last case discard one element.

Suppose instead \(c_2\le6\). By (17), \(\lambda_1=c_1=4\),
\(\lambda_2\le2\), and every later part is at most two. The number
of parts is \(\mu_1=a_1\le4\). Since the parts sum to nine, three
or fewer parts would give at most \(4+2+2=8\), while four parts must
have the final three equal to \(2,2,1\). Thus

\[
 \lambda=(4,2,2,1),\qquad \mu=(4,3,1,1),\qquad a_2=7.
\]

Take two antichains with union seven and make them disjoint as above.
Their sizes are four and three because each size is at most four.
\(\square\)

This proves the needed nine-element specialization from exactly (17).
A later formalization must either establish that imported theorem or
replace Lemma 4.1 with a direct finite proof; no theorem-proving execution
is asserted here.

## 5. Some rotating frame has height four

Rotate the coordinate frame through \(\theta\in[0,\pi]\), retaining
both cone comparisons at every diagonal tie. Suppose for a contradiction
that both heights were at most three at every angle. For each original
square \(S\), let \(i_S(\theta)\), \(j_S(\theta)\) be the lengths
of longest \(x\)- and \(y\)-cone chains ending at \(S\).

A comparison strictly increases the ending rank in its order. Since
every pair is covered, all nine rank pairs are distinct. They belong to
\(\{1,2,3\}^2\), so every pair in that grid occurs, and

\[
 \sum_S i_S(\theta)=18,\qquad
 \sum_S j_S(\theta)=18.
\tag{18}
\]

For each fixed ordered pair, the set of angles satisfying its cone
comparison is closed, by continuity of its coordinate differences.
Consequently every comparison absent at a fixed angle \(\theta_0\)
remains absent throughout a neighborhood of that angle. Intersecting the
finitely many such neighborhoods gives, for nearby \(\theta\),

\[
 \prec_x(\theta)\ \subseteq\ \prec_x(\theta_0),
 \qquad
 \prec_y(\theta)\ \subseteq\ \prec_y(\theta_0).
\]

Every nearby ending rank is therefore at most its value at \(\theta_0\).
The unchanged sums (18) force equality for every square separately.
Each square's rank pair is locally constant, hence constant on the
connected interval \([0,\pi]\).

Take the original with initial label \((1,1)\). It has no predecessor
in either initial order. At angle \(\pi\), both orders are reversed,
because both coordinate differences are negated. Its unchanged label
\((1,1)\) then means that it also has no successor in either initial
order. This contradicts pair coverage with any other original.

Thus some frame has height at least four in one order. Lemma 3.1 makes
its height exactly four and both widths at most four. Lemma 4.1 gives
parallel disjoint cone chains of lengths four and three in that order,
or antichains of those sizes, which are chains in the other order.
Choose the coordinate names and directions so these are
\(A\prec_x B\prec_x C\prec_x D\) and
\(E\prec_x F\prec_x G\). Label the remaining two originals \(H,I\).
Equation (9) gives actual projection separation for every nonconsecutive
pair in the two chains.

## 6. Diagonal-event reduction, including persistent height four

Fix the five directed nonzero center differences of these chosen chains.
Let \(\theta_0\) be the current angle of the positive \(x\)-axis,
and choose arguments \(\phi_1,\ldots,\phi_5\) of those differences
in \([\theta_0-\pi/4,\theta_0+\pi/4]\). Such representatives exist
by the cone inequalities. On this common real-angle branch, all five
comparisons persist on the closed interval

\[
 J=\bigcap_{j=1}^5[\phi_j-\pi/4,\phi_j+\pi/4]
  =[\max_j\phi_j-\pi/4,\min_j\phi_j+\pi/4].
\tag{19}
\]

This interval contains \(\theta_0\), including when its endpoints
coincide. At its left endpoint an edge with maximal \(\phi_j\) has
\(\Delta y=\Delta x>0\); at its right endpoint an edge with minimal
\(\phi_j\) has \(\Delta y=-\Delta x<0\). The positive \(x\)-gap
is nonzero at either endpoint, since the underlying difference is nonzero
and its angle to the positive \(x\)-axis is at most \(\pi/4\).

All five selected comparisons hold there. Equation (9) is valid in every
frame, so all nonconsecutive physical projection comparisons hold there
too. This construction makes no first-birth assumption: it still works
when a cone order has height four throughout the entire rotation, and
when several selected edges become diagonal simultaneously.

For one unordered center pair, a diagonal frame has positive-axis angle
\(\arg(c_j-c_i)\pm\pi/4\), with the appropriate orientation chosen.
These choices give a single frame class modulo quarter-turns. There are
therefore at most \(\binom92=36\) candidate frame classes, depending on
the actual centers. This is a finite reduction of witness directions;
it does not discretize positions or physical orientations.

## 7. Explicit symmetry maps and the three event types

The following operations act on all nine originals and their entire
physical frames. They preserve containment, interior disjointness and
all cone inequalities of the selected chains.

**Simultaneous reversal.** Apply \(T=-I_2\) to all points, reverse
both chain labelings, and retain the extra labels:

\[
 (A',B',C',D';E',F',G';H',I')
 =(-D,-C,-B,-A;-G,-F,-E;-H,-I).
\tag{20}
\]

The notation \(-S\) means the entire square is transformed, not only
its center. In original-frame terms, with the label permutation
\(\sigma=(A\ D)(B\ C)(E\ G)\),

\[
 c'_J=-c_{\sigma(J)},\qquad
 u'_J=-u_{\sigma(J)},\qquad v'_J=-v_{\sigma(J)}.
\]

For example, the new \(AB\) difference equals the old \(CD\)
difference, and the new \(EF\) difference equals the old \(FG\)
difference. Thus (20) exchanges \(AB\leftrightarrow CD\) and
\(EF\leftrightarrow FG\), and fixes the middle-edge position \(BC\).
It preserves the sign of the directed tie's \(\Delta y\).

**Common reflection.** Apply \(T(x,y)=(x,-y)\) to every center and
both side vectors of every square, without changing labels. This leaves
all positive \(x\)-gaps unchanged and negates every \(y\)-gap. If a
right-handed side-frame convention is desired, negate one transformed
side vector as well; that changes no square. This reflection turns a
negative diagonal tie into a positive one.

For either common orthogonal transformation, support transforms by
\(h'_J(e)=h_{\sigma(J)}(T^{\mathsf T}e)\). Hence the weak/actual
projection status is preserved under the corresponding label and
coordinate changes. The two extra originals are transformed along with
the selected seven; neither is discarded.

Choose any one of the tied edges supplied by Section 6. Apply reversal
if necessary to put an outer or short edge in the first position, then
reflection if necessary to make its tie positive. This gives the cover

| Marked edge before normalization | Operation on its position | Representative | Marked equation |
|---|---|---|---|
| \(AB\) or \(CD\) | Identity or (20) | \(AB\) | \(x_B-x_A=y_B-y_A>0\) |
| \(BC\) | Identity | \(BC\) | \(x_C-x_B=y_C-y_B>0\) |
| \(EF\) or \(FG\) | Identity or (20) | \(EF\) | \(x_F-x_E=y_F-y_E>0\) |

Common reflection is available in each row. The rows need not be disjoint:
a configuration with simultaneous ties can occur in more than one. This
is harmless because the theorem requires an exhaustive cover, not a
unique representative.

At a tied edge \(ST\), exactly one of

\[
 \Delta x=|\Delta y|<h_S+h_T,
 \qquad
 \Delta x=|\Delta y|\ge h_S+h_T
\tag{21}
\]

holds. The first is weak in both coordinate projections; the second is
actual in both. Projection equality belongs to the second alternative.
Both are retained. No arbitrary separator-owner choice is introduced.

## 8. Dependency and boundary ledger

| Input or boundary | Treatment in this chapter |
|---|---|
| Independently oriented physical squares | Each original retains its own orthonormal side frame throughout |
| Four-corner containment and support | Used directly in Sections 1–3 |
| Square separating-axis criterion | Stated in Section 1; supplies only the physical inequality (4) |
| Inset and center-radius estimates | Proved in Sections 1–2 |
| Height bound | Complete hand argument in Section 3, with its rational comparisons displayed |
| Finite-poset theorem | Exactly Greene's conjugate-partition theorem (17), explicitly imported |
| Nine-element specialization | Proved in Lemma 4.1; no simultaneous optimal chain partition assumed |
| Cone ties | Both comparisons retained, giving closed angle sets |
| Corner or physical pair contact | Allowed throughout; no positive clearance is assumed |
| Simultaneous diagonal ties | Kept by the closed interval (19); overlapping event rows allowed |
| Persistent height four | Covered directly by Section 6, without first-birth rank-grid hypotheses |
| Consecutive projection equality | Counted as actual in (21) |
| All omitted originals | \(H,I\) and their physical constraints persist under every transformation |

The remaining geometric task is precisely to route these full-nine event
domains to a sharp terminal, possibly after changing endpoints or direction.
The extraction proves neither the signed-surplus inequality in
[the proof draft](PROOF.md) nor its proposed all-nine routing statement.
