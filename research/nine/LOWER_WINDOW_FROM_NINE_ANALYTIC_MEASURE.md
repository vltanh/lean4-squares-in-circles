# The original nine-square lower window follows from the analytic radius-two measure

Date: October 28, 2026. Author: six_body.

**Status: complete standalone lower-window join, submitted for root and
separate independent review.** This supplies the exact existing obligation
`G0.W.3`: an independent hand proof of `R>=79/40` for every actual
nine-square packing. It uses the stronger analytic same-nine theorem
`R>2`. No lower bound on R, positive stress, minimizer, contact graph,
eight-square theorem or generated arithmetic table is a premise.

The six mathematical sources below retain their complete original
geometric domains and open-interior measure conventions. Their fixed
values now use the printed analytic replacement. The old five-charge
and 208-charge checkers remain historical alternatives; their execution
and stored margins are not operative dependencies of this join.

## 1. Exact physical theorem, without an assumed radius window

Let `S_1,...,S_9` be any nine actual closed unit squares, each with its
own orthonormal frame, contained in the closed disk of nonnegative radius
R about the same point O. Assume only that their open interiors are
pairwise disjoint. The squares may touch, share boundary segments, have
coincident vertices or have O on their boundaries.

**Theorem.**

\[
                         R>2>\frac{79}{40}.
\tag{1}
\]

In particular every such packing satisfies the original coarse window
prerequisite `R>=79/40`. All nine original units are retained. This
theorem is not asserted for a smaller isolated positive component.

Suppose otherwise that `R<=2`. The original containment gives

\[
                         S_i\subseteq D_R(O)\subseteq D_2(O)
                         \qquad(1\le i\le9).
\tag{2}
\]

This is ordinary inclusion of disks, with the same O, same physical
squares and same orientation of every square. No dilation, change of
unit length, deletion of one square or displacement is used. It remains
to apply the unconditional measure theorem on `D_2(O)`, whose complete
active proof is recorded in Sections 2--4.

## 2. Frozen active mathematical sources

The following exact versions were read for this join. Each SHA256 refers
to its entire recovered manuscript, including its explicit dependency
update. Mutual bibliographic references between files do not constitute
mathematical dependencies; Section 4 gives the operative order.

| Source | SHA256 | Operative mathematical part |
| --- | --- | --- |
| `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` | `4c9e708945938c3f9df575e76f7573903d6b5a0ce4eccb5bcea760353a47458a` | The measure, complete own-frame normalization, and Sections 3.1--3.4 geometric reductions and direct strip bound |
| `NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md` | `714e2a092af516fad1450d2aeb38a6529418ef72070b5184d462a3f4b8a8f18d` | Sections 1--3: complete actual circle formulas, derivative signs and exact locations of the two line minima |
| `NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md` | `8b749abf2792e022b2a3bb79ea275ebc02000707c864a4ae41f5b6410edeb780` | Sections 1--3: four entire corner cases, two entire middle cases, and all fourteen printed Taylor and six mass comparisons |
| `NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md` | `9258e4d00c0935a4deee1942159b88a7474e95169443d1ed966da3156a336eba` | Sections 1--4: complete circle-face branches, continuous monotonicity, convexity and the fixed-tangent implication |
| `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md` | `9a4656cc90ab81200847c8b6958fc6e089fc4b807b401705663304be4f782c4b` | Sections 2--5: signed Taylor and pi bounds, both actual line minima, all three outer values and the complete derivative estimate |
| `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` | `c316fbce9320918ba88e46c4cd53b5c70c8ccdb2cc585171204f28385905929f` | Sections 1--3 with their current dependency update: exhaustive normalized-domain assembly and same-nine measure contradiction |

The full source-specific independent and root reviews are
`REVIEW_NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES_INDEPENDENT_CURRENT_50C0_2026_10_27.md`
and `REVIEW_NINE_RADIUS_TWO_ANALYTIC_VALUES_ROOT_2026_10_27.md`.
Their adoption and current-source reconciliation are preserved in
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`,
`REVIEW_ANALYTIC_CERTIFICATE_CHECKPOINT_CURRENT_D579_2026_10_27.md`
and `REVIEW_ANALYTIC_CERTIFICATE_PACKAGE_ROOT_CURRENT_D579_2026_10_27.md`.
Their complete accepted mathematical scope is retained. The present
join independently checks the absence of a lower-window premise and
the exact original W.3 implication.

## 3. The full measure theorem covers every unit in the radius-two disk

Let `lambda_r` be normalized angular measure on the circle of radius r
about O, and `delta_O` the point mass at O. Use the single nonnegative
measure

\[
\mu=\frac1{1000}\left(
292\delta_O+714\lambda_{1/10}+3858\lambda_1
             +2424\lambda_{11/10}+1709\lambda_{27/20}\right).
\tag{3}
\]

Its total mass is

\[
                \mu(\mathbb R^2)=\frac{8997}{1000}<9.
\tag{4}
\]

For any one actual unit in `D_2(O)`, choose that unit's own coordinates,
with O as the coordinate origin, and reflect and interchange the axes
so its center coordinates satisfy `x>=y>=0`. Put `a=x+1/2` and
`b=y+1/2`. Its complete domain is exactly

\[
 S(a,b)=[a-1,a]\times[b-1,b],\qquad
                   \frac12\le b\le a,\qquad a^2+b^2\le4.
\tag{5}
\]

The last inequality is the farthest-vertex containment condition. The
radial measure (3) is invariant under these coordinate choices, so this
individual analysis applies to every independently oriented original
square with the same measure. It does not put all squares in one frame.

Here is the complete normalized-domain cover, with the new printed
fixed-value proof used wherever the historical sources name a checker.

| Entire normalized domain | Complete current lower bound |
| --- | --- |
| `a<=9/10` | The actual origin atom and small circle give `1006/1000>1`. |
| `9/10<=a<=11/10`, `b<=9/10` | The even-density translation reduces to the entire line `b=1/2`. Its left minimum has mass greater than `1+785291/314159000`; its right, atom-free minimum has mass greater than `1+575589/110000000`. |
| `9/10<=b<=a<=11/10` | The four complete corner cases in the rectangle source give positive reserves `11613/2200000`, `5761/90000`, `14681/4400000`, and `2423/550000`. |
| `11/10<=a<=27/20`, `b<=1` | The two-circle strip calculation gives the strict reserve `189/34375`. |
| `11/10<=a<=27/20`, `1<=b<=a` | The two complete middle cases give the positive reserves `19681/550000` and `2897/75000`. |
| `a>=27/20` | The outward measure comparison reduces to the entire curve `a=sqrt(4-b^2)`, `1/2<=b<=sqrt(2)`. Its complete branch and convexity proof gives mass greater than `3013/3000`. |

These are exhaustive continuous regions. First take the first or last
row when applicable. In the remaining a interval, split at `a=11/10`,
then at `b=9/10` or `b=1` respectively. The actual order `b<=a`
and full containment inequality stay in force. No finite pose sample
supplies this cover.

For the outer row, the three actual values at `b=1/2`, `b=13/12`
and `b=sqrt(2)` exceed `201/200`. On the entire middle branch the
printed derivative estimate at `b_*=13/12` and the continuous
second-derivative bound are

\[
                |M'(b_*)|<\frac1{150},\qquad M''>\frac1{30}.
\]

Consequently, writing `y=b-b_*`,

\[
 M(b)>\frac{201}{200}-\frac{|y|}{150}+\frac{y^2}{60}
      =\frac{3013}{3000}+
                 \frac{(|y|-1/5)^2}{60}>1.
\tag{6}
\]

The initial and final branches are bounded by the other two fixed
values. All actual face transitions and both geometric endpoints are
included. Neither the derivative zero nor a pose minimum is numerically
assumed.

The origin atom is counted only for an actual open interior containing
O. In particular the entire line `a=1` is assigned to its atom-free
formula, and the rectangle proof separately covers every `a=1` or
`b=1` boundary. Angular circle measures disregard only finitely many
edge intersection points, each of zero angular measure. There is no
continuity argument that supplies an origin atom to a boundary square.

The six rows therefore prove, uniformly on (5),

\[
                         \mu(\operatorname{int}S)\ge1.
\tag{7}
\]

## 4. Exact dependency order and absence of a lower-radius assumption

The active logical order is the following.

1. Define (3), normalize an arbitrary unit in `D_2` by (5), and prove
   the elementary geometric comparisons and strip estimate.
2. Derive the complete line formulas and locate their two scalar minima
   by exact derivative signs. Independently prove the entire rectangle
   cases and the outer curve's branch, monotonicity and convexity facts.
3. Prove the elementary Taylor and pi estimates. Use the already derived
   line and outer formulas to evaluate their five fixed mass targets
   and one derivative target by the displayed rational comparisons.
4. Assemble the six continuous regions to obtain (7), then sum the
   same measure over the original nine open square interiors.

No step calls a window-dependent contact, force, tree, cyclic, eight-square
or nine-square packing theorem. The numbers `9/10`, `11/10`, `27/20`
and the line-minimum enclosures in these sources are own-frame parameter
or measure-circle constants. They are not assumed bounds on the
containing radius R. The whole argument is a proof about arbitrary
units in the fixed disk `D_2`, before any claimed packing contradiction.

For completeness, the printed pi bounds also require no geometric
packing theorem. Put `alpha=arctan(1/5)`, `beta=arctan(1/239)`.
The tangent double-angle formula gives `tan(4 alpha)=120/119`,
and the subtraction formula gives `tan(4 alpha-beta)=1`.
Since `0<4 alpha-beta<4/5<pi/2`, this proves
`pi=16 alpha-4 beta`. The lower signed atan remainder gives the
printed rational lower pi bound; the positive integral

\[
                  \int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx
                  =\frac{22}{7}-\pi>0
\]

gives the upper one. The elementary estimate `pi>2` needed to
locate the preceding angle follows directly from
`pi/4=integral_0^1 1/(1+x^2) dx>1/2`.

There remain thirteen printed Taylor comparisons in the fixed-value
source, fourteen in the rectangle source, and explicit radical and
rational arithmetic. Those are ordinary hand inequalities with stated
remainder signs and positive reserves. They do not require an external
inverse-angle evaluator, generated pose table, adaptive subdivision,
stored whole-box margin or execution of a proof-checking program.

## 5. The same-nine contradiction and the original W.3 conclusion

Under (2), apply (7) to every one of the nine actual squares. Their
open interiors are pairwise disjoint measurable sets. Additivity of
the one fixed nonnegative measure gives

\[
 9\le\sum_{i=1}^9\mu(\operatorname{int}S_i)
    =\mu\!\left(\bigcup_{i=1}^9\operatorname{int}S_i\right)
    \le\mu(\mathbb R^2)=\frac{8997}{1000}<9,
\]

a contradiction. Thus `R>2`. Finally,

\[
                         2-\frac{79}{40}=\frac1{40}>0
\]

proves (1), including the requested weak inequality `R>=79/40`.
No low-radius range has been assumed away: every original `0<=R<=2`
was covered by its actual disk inclusion in (2).

The exact existing checklist obligation

> **W.3** Supply an independent hand R>=79/40 argument if standalone
> table-freedom is required.

is therefore discharged after acceptance of this complete join and its
frozen analytic dependencies. The original W.2 eight-square import
remains a valid historical alternative, but it is unnecessary for the
lower-window premise on this route. No older hand source needs a new
force or contact assumption to use the stronger same-nine conclusion.

If a hypothetical subcritical packing has `R^2<1105/256`, the same
argument applies directly to it and to any independently established
attained minimizer, giving

\[
                 \frac{79}{40}<2<R_*<\frac{\sqrt{1105}}{16}.
\]

Thus every existing original lower-window caller can use this new
entry point while retaining its own upper-radius, physical and
certificate-selection hypotheses. This does not provide a compactness
or stress theorem; those remain their separate established inputs.

## 6. Precise bookkeeping and limits

This is one new closure of the already existing fine obligation W.3.
It changes no original fine ID or count denominator and closes no
coarse graph cell. It proves neither the sharp target
`R^2>=1105/256` nor its complete equality classification. It does not
retire other arithmetic or canonicalization dependencies of the full
project merely because the lower-window n=8 import is now optional.

The conclusion keeps all nine original physical units and does not
apply to a six-body component after its completion units are removed.
No original force, normal, application mean, circle mask, load or degree
is changed. No Lean compilation, CI, workflow, original ledger edit,
remote write or numerical inverse-angle evaluation is part of this join.
