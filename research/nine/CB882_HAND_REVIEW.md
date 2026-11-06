# Review of the Cb882 hand lemmas and table rules

This is a second-agent mathematical review of the current hand argument,
dated 6 November 2026. It is not a human referee report or a Lean
verification. The review found no invalid geometric implication in the
scope below. It clarified one sign convention in the affine-axis rule.
The whole Cb882 original remains open until an exhaustive complement
table has been supplied and checked.

## 1. Reviewed continuous arguments

The following chapters were read as mathematical arguments, retaining
their stated physical originals, owner alternatives and boundary cases.

| Chapter | Reviewed implication and outcome |
|---|---|
| [Local sharp terminal](CB882_LOCAL_SHARP_TERMINAL.md) | The full stated guard implies the seven aligned frames and the four anchor centers. Actual BC and cone CD then contradict strict weakness of CD. This is a local theorem, not a proof that the whole caller enters the guard. |
| [Endpoint insets](00100_ENDPOINT_INSETS_ARE_VERTICAL.md) | Both horizontal alternatives for A/E insets are excluded. The D/G argument uses only the earlier cap and localization bounds, before any G-height hypothesis or contrary C-slant assumption. Both inset pairs therefore separate vertically on the stated parent. |
| [Inner frame and downward cone](00100_INNER_FRAME_AND_DOWNWARD_CONE.md) | The narrow B-frame bound and the nonpositive-horizontal H case are independent of C-slant. The remaining H case correctly uses nonpositive-D C-slant. Together they give the necessary bound y_B>-67/120 in the complete stated Cb882 caller. |
| [Whole-domain rules](CB882_WHOLE_DOMAIN.md) | The initial boxes, rational frame enclosures, physical rows, secant rows, weighted deductions, selected-axis alternatives and terminals are necessary conditions or complete covers of the stated original caller. They do not constitute a completed finite cover. |

For the local terminal, the review checked the relative-angle lower
support bound, both physical owners of BI and ID, their four owner
combinations in the path-loss estimate, and both owners and signs in
each endpoint vertical link. The four-corner weighted identity and all
six positive coefficients agree with direct expansion. Equality in the
four positive-weight support inequalities forces the four actual
corners; the proof does not assume a height for B.

For the endpoint lemma, direct rational substitution reproduces the
printed quartic numerator N(w). Its two interval estimates cover
0<=w<=1/10 with positive denominators. The inverse horizontal
alternative is separately excluded. Thus the argument does not infer
vertical separation from only one horizontal inequality.

For the downward-cone lemma, the distance used is between H's center
and B's actual contained inset. This is a valid necessary condition
from H's incircle. The secant-free estimate, the two horizontal cases
for H, and both cases in the lower-right pocket exclusion were checked.
The two pocket endpoint reserves are exactly 11/14400 and 23/9216.

The A-height bound cited by the whole-domain initial boxes is proved
in [the earlier sharp-height chapter](00100_SHARP_A_HEIGHT_AND_CB882_DEEP_B.md),
Section 1; it is not a new conclusion of the inner-frame chapter.
The review also checked that height argument and the localization and
cap-transfer deductions needed by the four reviewed chapters.

## 2. The selected-axis sign clarification

The upper bound for a product tz in whole-domain Section 5 is valid
for the actual correlated variables throughout the entire proved box.
For a signed primary axis it must be applied with z=s Delta_y;
for a signed secondary axis it must be applied with z=-s Delta_x.
Negating a coordinate difference replaces its interval [L,U] by
[-U,-L]. Multiplying an upper product bound by a negative sign would
reverse its inequality and would not give a necessary axis row.

The chapter now states this convention explicitly. This clarifies the
rule; it does not change the geometry or claim a missing table leaf.
The rest of the whole-domain arithmetic rules were checked with their
stated directions: distance secants bound squared distance from above,
the inset-incircle secants first enlarge the convex distance terms,
and weighted deductions use only the previously proved center box.

## 3. Independent reconstruction of the C-slant arithmetic

The three C-slant chapters were reviewed for their axis reduction,
sign coverage, row derivations and acyclic assembly. In particular,
the lower-G table does not inherit the upper-G height row or its
G-left-of-D conclusion. Its changed row 122, physical row 124,
octagon row 125 and optional horizontal-sign row 126 were reconstructed
from their own printed definitions.

A separate short exact-fraction calculation reconstructed every
weighted table row from the manuscripts, without importing an earlier
row generator or validator. It checked the following finite arithmetic:

| Printed component | Roots | Terminal cells | Binary splits | Positive-weight occurrences |
|---|---:|---:|---:|---:|
| [Upper-G secondary-axis table](tables/c-slant-secondary.tsv) | 21 | 4,204 | 4,183 | 29,278 |
| [Lower-G complement table](tables/c-slant-lower.tsv) | 288 | 1,039 | 751 | 6,568 |
| Total | 309 | 5,243 | 4,934 | 35,846 |

For every line the reconstructed rational coefficients satisfy its
printed inequality

\[
 -\sum_j w_j B_j-\frac{91}{60}
       \sum_k\left|\sum_jw_j(A_j)_k\right|
       \ge\frac{m\sum_jw_j}{100000}>0.
\]

Every weight and m is a positive integer. Each root's paths form a
complete binary tree: every nonterminal prefix has both halves of
the same original angle interval, and no terminal has descendants.
The listed roots equal the full sign, owner, axis, horizontal-sign
and octagon alternatives stated in the chapters. All leaf counts
and minimum printed reserves agree with the root tables.

The primary-axis chapter's 67 rectangles were checked separately by
substituting their endpoints into its rational formulas. Every
printed lower bound for X and Y holds. The smallest printed squared
numerator is 4,357,440 over denominator 1,000,000, strictly greater
than Q=1105/256. The 63 original rectangles and four replacements
cover the entire stated enlarged canonical rectangle.

These calculations audit the displayed finite arithmetic. The proof
remains the printed formulas, covers and inequalities; a numerical
feasibility result or executable success report is not a premise.

## 4. Review boundary

The physical weighted two-square cap in [FOUNDATION.md](FOUNDATION.md),
Part B, was taken as the earlier hand theorem. Its application and
the cap-transfer algebra were checked here; this review does not
claim a fresh line-by-line audit of that cap's full scalar proof.
The physical separating-axis theorem, inset containment and center
radius estimate used here were checked in the foundation.

This review does not re-establish extraction of every nine-square
configuration, the archived original-cell register, or the literal
Cb882 ancestry outside the stated caller. It does not classify the
unrestricted equality cases, close another original, or supply the
missing whole-Cb882 complement table. Any later table must still
justify every bound before use, preserve both children of every
split, and imply the complete local guard before invoking its sharp
terminal.
