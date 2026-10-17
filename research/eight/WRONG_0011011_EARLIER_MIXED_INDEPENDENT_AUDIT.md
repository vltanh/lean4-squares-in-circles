# Independent review of the earlier mixed transitions for 0011011

## Verdict and exact scope

**PASS.** The six whole-angle manuscripts listed below prove their stated
mixed core/outer transitions at \(Q=9789/2500\), for all four retained
separating axes and the whole interval
\[
 \pi/2-7/10\leq\phi\leq\pi/2+7/10.
\]
Both pieces of each core boundary are included wherever the theorem claims
the whole core. Their strict corrected-cost threshold is
\(\gamma=17953/20000\). The two additional aligned/strip prerequisites
also pass this review with exactly their stated, smaller angle domains.
No correction was necessary.

The reviewed files are in **m5_agent/hand_conversion**. In the table,
each shortened name has prefix **WRONG_0011011_** and suffix
**_HAND_PROOF.md**.

| Manuscript | Stated family | Fresh author comparisons |
|---|---|---:|
| EDGE2_NEGATIVE_CORE_SIDE | \(O^-\to C^-\), core side | 67 |
| EDGE2_NEGATIVE_CORE_CORNER | \(O^-\to C^-\), core corner | 82 |
| EDGE2_OUTER_TO_POSITIVE_CORE | \(O^-\to C^+\), whole core | 55 |
| EDGE2_CORE_TO_POSITIVE_OUTER | \(C^-\to O^+\), whole core | 63 |
| EDGE3_FOUR_WHOLE_MIXED_FAMILIES | \(C^-O^-,O^+C^+,C^+O^-,O^+C^-\) | 68 |
| EDGE3_OUTER_TO_POSITIVE_CORE | \(O^-\to C^+\), whole core | 127 |
| ALIGNED_MIXED_QUARTER | All twelve permitted mixed edge-2/3 families, \(\phi=\pi/2\) | 85 |
| EDGE2_MIXED_QUARTER_STRIP | All mixed edge-2 families, \(|\phi-\pi/2|\leq1/50\) | 146 |

The last report includes the 85 aligned comparisons. The fresh replays
therefore have 693 reported comparisons, with that intentional overlap.

The independent checker **audit_wrong_0011011_earlier_mixed_hand.py**
passes **237 strict rational comparisons**. It rebuilds **ten polynomial
rows and all 84 displayed Bernstein lower bounds**, and independently
reconstructs the decisive contact, curvature, tangent and endpoint
comparisons. It does not import the author arithmetic implementation.
The report **wrong_0011011_earlier_mixed_independent_audit.json** binds
every reviewed manuscript, author checker and author arithmetic report,
the exact role-label input, and the independent checker's own bytes.

## Common geometric and label interface

I rederived the four signed SAT projections from the own-frame convention
\((a,-\sigma b)\), rather than relying on a sign-pattern analogy.
At alignment they reduce, in the stated order, to the two repeated
alternatives
\[
 \sigma b+A\geq1,\qquad a-\tau B\geq1.
\]
For the negative/negative and negative/positive nonaligned cases the
displayed signs of \(b\sin\phi\), \(B\cos\phi\), and \(A\cos\phi\)
agree with direct rotation of the two centers.

The common four-axis reduction is the previously established boundary
geometry premise. These notes do not assert that four arbitrary axes
replace SAT outside that premise. Each of the six whole-angle theorems
then treats every retained axis on both angle halves, or excludes it
by a necessary projection bound. The core-side/corner join and the
outer axial/diagonal endpoints are closed domains throughout.

All used label coefficients match the exact five-feature role table
with denominator \(100000\). Edge 2 uses its proved negative source sign.
The reflection/reversal used to obtain edge 5 or 6 preserves the
angle and corrected cost while exchanging the two endpoint labels.
The second row of the four-family note explicitly changes to the
reversed pair's labels; it does not assume that one role's positive and
negative labels coincide.

For completeness, the frequently used outer norm bound follows directly
from
\[
 a^2+b^2=Q-\tfrac12-a-b,\qquad (a+b)'=1-r\geq0.
\]
Thus the norm is at most the axial coordinate \(a_0<1.415\).
The whole core norm is less than \(0.8\). These facts justify the
impossible-axis and forced-side arguments without assuming a contact
configuration.

## Edge 2: negative outer to negative core

### Core side

The side note has a complete independent cover.

The ratio \((L'/r)'\) is negative: multiplying by \(r^2\) leaves the
stated three-term expression, and the bounds \(r\leq1\),
\(r'>.557\), \(a<1.415\) have the correct directions. The continued
height function \(M\) is exactly the negative outer label, and its
third derivative is positive on the enlarged height interval.
The tangent-quadratic integral formula proves a whole-interval lower
minorant from its one left-endpoint comparison. The downward rounding
in its constant exceeds the possible slope-rounding error.

For lower axis 4, the height bound \(y_*\) follows from the actual
separator, with \(1\leq y_*\leq a_0+1/2\) for every feasible state.
Using \(M(y_*)\) is a valid lower relaxation even if the continued
contact is outside the physical outer arc. I independently expanded
the discriminant \(4\mathcal A\mathcal C-\mathcal B^2\), checked the
sign of \(\mathcal A\), and reconstructed all ten positive
degree-nine Bernstein bounds. The trigonometric substitution and
negative-tail allowance both lower the discriminant; neither a
squared-sign choice nor a discarded positive tail is implicit.

For lower axis 3, the early norm envelope is concave by
\(N''+N/4>0\). In the remaining range, positive target-coordinate
contacts move toward alignment with decreasing cost. A zero-coordinate
exit continues on the unique outer contact. The contact derivative
does not vanish, its source coordinate stays above \(0.7\), and the
outer diagonal has negative margin, so an omitted outer endpoint
cannot stop the path.

On the upper strip, the same endpoint checks establish existence and
the required derivative signs for both axes. Positive target
coordinates remain below the side/corner join; zero-coordinate paths
remain strictly inside the outer arc. The direct late-angle bound
starts before the strip ends. The resulting angle cover has no gap.

### Core corner

The contact height decreases in both corner coordinate and angle and
lies in \((1.33,1.7)\). The continuation is used only to lower the
cost, so a continued contact below the outer diagonal is harmless.

I rederived
\[
 f_{BB}=M''u_B^2+(M'\cos\phi-.34492)A''-.10668,
 \quad A''=-12(1+w^2)^{3/2},
 \quad u_B^2\leq1+w^2.
\]
The five early rows bound \(M''\) at the join/left angle and the
normal coefficient at the diagonal/right angle. Every coefficient
has the sign required for the ensuing concavity bound.
The two later ranges use upper bounds on \(f''\), followed by the
valid lower interpolation loss \(K\ell^2/8\); this direction does not
assume convexity.

I independently expanded all three endpoint-curvature polynomials
\(E,A_0,P\), solved their Bernstein representation by triangular
elimination, and checked all twenty printed strict lower bounds.
The positive signs of \(E\), \(A_0\), and \(P\) justify the radical
comparison and give \(H''>.4\) on the entire enlarged height interval.
The two fixed reference points, the increasing diagonal curve after
\(1.1\), and both interpolation reserves independently check.
The late direct bound includes every remaining angle and axis.

The side and corner notes therefore join to prove the complete
\(O^-\to C^-\) edge-2 family.

## Edge 2: the other two reviewed families

### Negative outer to positive core

Axis 1 is impossible by the core norm. The upper axis-2 relaxation
has the correct sign because \(\cos\phi\leq0\); its scalar is concave.
Axis 3 forces \(B<.415\) on either angle half. On the lower half,
the small-source chord gives a concave norm envelope; the large-source
contact has \(a\geq1\) and \(B_\phi\geq1\), so the cost decreases to
the aligned state.

For lower axis 4, a corner target would require \(a\geq1.5>a_0\).
On the side, the comparison with \(1+B\) bounds the contact by
\(B\leq a-1<.415\). The large-source continuation and its completed
square have the right derivative sign. The other lower states and
all upper states outside the imported strip use the two stated
squared support polynomials. I independently reconstructed all
eighteen Bernstein coefficients, the positive numerator conditions,
and the exact negative-tail allowances.

### Negative core to positive outer

The outer label is increasing and strictly concave. Its rounded
tangent has both slope and intercept rounded upward, which preserves
the upper bound for \(B\geq0\).
Axis 1 forces the core side. In its early range, the contact derivative
increases with the outer coordinate but remains negative at its
largest feasible value. Thus the deformation ends at zero source
coordinate, rather than at an unexamined core corner.
On that zero curve, the identity
\[
 S^2=Q-2A-\tfrac14,\qquad
 \phi'(B)=\frac{1+\cos\phi/S}{A+1/2}
\]
has the stated signs and endpoint bounds. Its decreasing cost reaches
the fixed angle \(1.2\).

Both later axis-1 supports are concave. Both axis-2 halves are covered
by necessary coordinate relaxations and two full-interval positive
polynomials, whose eighteen printed coefficients and tail allowances
were independently reconstructed. Axis 3 is universally impossible;
the remaining upper axis 4 has either the direct late bound or the
stated strict coordinate cutoff. No imported strip is needed by this
theorem.

## Edge 3: the four-family calculation

The two outer chords are lower bounds because their labels are concave.
The negative-core affine estimate is an upper bound on both the side
and corner; on the corner its lost primary-coordinate term is more
than offset by the negative quadratic term.

For the two normalized negative/negative rows, I checked all six
angle/axis subcases. The substitutions with \(a>1/2\), \(a\leq7/12\),
\(A\geq d\), and \(A\leq a_0\) change direction correctly when
\(\cos\phi\) changes sign. The lower primary estimate uses
\(\cot\phi\geq\pi/2-\phi\) with coefficient strictly between zero and
one. The scalar derivatives or concavity arguments cover their whole
intervals. The independent calculation reconstructs all lower scalar
endpoints and all upper concave-scalar endpoints for both rows.

The positive-core/negative-outer family uses a direct late bound and
four valid early projection consequences. The positive-outer/negative-
core family has a direct bound independent of its separator.
These arguments include every core boundary point.

## Edge 3: negative outer to positive core

The small and global upper lines for \(T\) are whole-interval bounds.
Their proof uses increasing \(T''\), a strongly concave reference
quadratic, and endpoint maxima on the remaining intervals. In
particular, convexity of \(H'\) with \(H'(.6)<0\) allows no additional
interior maximum of \(H\). The two bounds on \(T'/r\) have strict
rational reserves.

I independently reconstructed the slopes, intercepts, and both scalar
endpoints of all eight early axis-3 supports. Each tangent applies on
the same concave source arc, and each norm envelope is concave on its
declared closed angle interval. The eight intervals meet exactly.
The later source-coordinate motion increases the target coordinate
but keeps it below \(0.415\), so it reaches the stated small-source
support without a missing core endpoint.

For the early lower primary contact, the margin and its derivative
force a single zero-target curve. Its contact derivative is negative
throughout the feasible interval. I rederived the important
curvature cancellation:
\[
 N(m)=Qm(2m+1)-m(m+1)^3-\frac{205Q}{144},
 \qquad N'(m)=(4m+1)\{Q-(m+1)^2\}.
\]
Feasibility gives \(m\leq a_0-1/2\), and the derivative is positive.
Thus the upper negative bound for \(N\), together with the upper
positive denominator bound, gives the claimed negative acceleration.
Since \(T''<0\) and \(T'>.610\) there, the cost has curvature \(>.94\).
The independent rational reference value, derivative, and completed
quadratic at \(\phi=1.383036\) all pass.

Both upper-strip contacts have the stated positive angle-cost
derivatives. At an axis-3 zero exit one may write, explicitly,
\[
 a\geq\tfrac12+\tfrac12\sec x-.4\tan x
 =1-.4\sin x+(\sec x-1)(\tfrac12-.4\sin x)
 \geq1-.4\sin(.02)>.992.
\]
This supplies the short algebra behind the manuscript's zero-exit
bound. The resulting source bound \(b<.81\) gives its direct reserve.
The two remaining primary support polynomials were independently
expanded, with all eighteen coefficients and both tail allowances
checked. Their interval endpoints overlap the contact/strip ranges.

## Aligned and strip prerequisites

I also rechecked the complete aligned axis reduction and all twelve
permitted mixed kind/sign families. The three nontrivial aligned
convexity calculations, the concave positive-core contact, and the
negative-core contact with decreasing second derivative cover all
endpoints. The independent checker reconstructs the tight \(G,H_2,H_3\)
reference comparisons and their completed-square consequences.
The direct aligned cases have their required label monotonicity and
strict reserves.

For the edge-2 strip I checked the signs separately on \(e<0\) and
\(e>0\). Positive and negative target labels require opposite initial
coordinate motions. Each selected projection moves toward contact
with the cost decreasing. The derived coordinate bounds place all
contacts on the core side. The zero-target contact exists uniquely
for every angle in the strip, has a nonzero outer derivative, and
stays away from both outer endpoints. Its cost derivative has the
correct sign on each half. The small-source and small-target
exceptions have direct integrated reserves, and the zero-source
exit in the core-to-outer case has a bound independent of the
particular contact. No corner or endpoint is omitted.

## Arithmetic method and limitations

The independent program uses Python fractions, integer square-root
brackets checked by squaring, and alternating trigonometric series.
It proves its rational \(\pi\) enclosure using separate Machin sums.
For each polynomial it solves the Bernstein change of basis by
triangular elimination, re-expands the resulting basis to the original
power coefficients, and compares every displayed numerical floor.
Only whitespace and mathematical delimiters are removed in checking
the Markdown transcription; signs and digits remain part of the test.

All eight author reports were freshly regenerated by genuine Node
execution and compared byte-for-byte with the stored reports.
This is an arithmetic and continuous-proof audit of the stated
components. Whole-word exclusion additionally requires the other
pair components and the finite case-cover/telescoping argument.
It does not, by itself, claim unrestricted eight-square sharpness or
its equality classification.
