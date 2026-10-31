# Independent review of the constant-corner all-means Fermat bound

Date: October 26, 2026.
Reviewer: block_attachments, separately from the author.

**Verdict: PASS.** The scalar pair inequality, its full half-line
positivity proof, the one-common-point mean comparison, every
Fermat alternative, and the unchanged physical support-functional
join are correct. The source validly replaces the twelve rational
three-by-three matrix checks formerly used for the constant-corner
one-share and two-share rows.

Primary source:

- TRIANGLE_CONSTANT_CORNER_ALL_MEANS_RADIUS_TWO.md.

Dependencies inspected for the exact physical and algebraic joins:

- TRIANGLE_SQUARE_CORNER_FERMAT_BOUND.md;
- SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md, especially Section 3;
- SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md;
- SIX_CYCLE_CONSTANT_CHI_ONE_SHARE_EXCLUSION.md;
- SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md;
- SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md.

The separate global radius-two measure theorem has already passed
this reviewer's complete independent audit in
REVIEW_NINE_RADIUS_TWO_MEASURE_BLOCK_2026_10_26.md.

## 1. The strict two-variable inequality is valid on the full quadrant

For nonnegative a,b, the collapsed-endpoint branch follows from
the exact identity

    (124/3)(a^2+ab+b^2)-(5a+6b)^2=(7a-4b)^2/3.

The fixed strict comparison with (2-sqrt(2))D has positive
quantities on both sides. Its final squared reserve is exactly

    1027^2-2*726^2=577>0.

Thus it is strict whenever D>0. The zero pair is correctly
retained only as a weak equality case.

For the original-corner branch, a=0,b>0 is immediate. For
a>0 the source's normalization t=b/a retains the whole
half-line, with no upper ratio restriction.
I reconstructed

    H=121(4D_0^2-E_0^2)-(5+6t)^2

directly and obtained exactly

    217+(303-121sqrt(3))t+327t^2.

Every coefficient is positive using sqrt(3)<7/4. The
second squared comparison expands exactly to the displayed
quartic. Every occurrence of sqrt(3) in a nonconstant
coefficient has negative sign, so replacing sqrt(3) by
7/4 really is a lower bound for all t>=0.

The resulting rational polynomial is exactly

    Q(t)=179010t^4-34557t^3+45043t^2-103505t+45778.

Its translation t=y+1/2 gives the displayed identity,
including the linear coefficient 20501/4 and constant
48619/4. The bracket derivative on y>=-1/2 is at least
144453>0, and its endpoint value is 289487/2>140000.
Multiplying the bracket bound by y^2 preserves the
inequality for negative as well as positive y.
The remaining quadratic has strictly negative
discriminant and positive leading coefficient.

This proves positivity on the entire half-line in
one argument. The source then reverses its two
squarings legitimately: H>0, E_0>0, L>0, and all
quantities compared by the final square root are
nonnegative. Both branches therefore give

    2D-max(E,sqrt(2)D)>(5a+6b)/11

for every a+b>0, including t=0 and a=0.
No sign grid or coefficient packet is required.

## 2. A single original Fermat point handles all three means simultaneously

For either constant bit, the collapsed vector is
(I+J)F_i or (-I+J)F_i. Its norm is exactly
sqrt(2)|F_i|. The affine vector inside the actual
mean functional can be written

    (1-delta_i)(g_i-x)+delta_i(g_i-k_i).

Norm convexity therefore gives the pointwise
maximum bound in the source for each delta_i in
[0,1]. The same comparison point x is retained
in every term. In particular the proof never
combines separately minimized endpoint functions.

Translation to the Fermat point is also exact:
translating every force point by -o translates
g_i and k_i by -o while leaving F_i unchanged.
Consequently

    g_i-delta_i*k_i-(1-delta_i)o

is precisely the translated vector used in the
common-point calculation. No actual force or
physical normal is altered by this evaluation.

## 3. Interior and nonvertex Fermat alternatives

A nonvertex minimizer of the three-distance
functional has three unit radial directions
summing to zero, hence pairwise 120-degree
angles. For a nondegenerate counterclockwise
triangle they occur in the source's cyclic
counterclockwise order. With distances a_i>0,
the side lengths are exactly D(a_(i-1),a_i).

I independently expanded both corner norms
using consecutive radial vectors

    (a,0), (-b/2,sqrt(3)b/2).

For chi=1 the squared corner norm is

    2a^2+(1+sqrt(3))ab+b^2;

for chi=0 it is the same expression with a,b
interchanged. This confirms the orientation
and the sign of the sqrt(3) cross term.

The linear right sides of the strict pair
inequality sum cyclically to sum_i a_i:
each distance receives coefficients 5/11 and
6/11, in either constant-bit direction.
Thus the three pair inequalities yield

    sum_i |f_i-o|
      +sum_i max(|g_i-o|,sqrt(2)|F_i|)<2P.

Combining the pointwise mean bounds at this
one o proves the entire independent mean cube.

## 4. Vertex, collinear and coincident cases

At a vertex Fermat point f_0=0, put
p=|f_1|, q=|f_2| and d=|f_1-f_2|.
For two nonzero rays the subgradient condition
gives angle at least 120 degrees. Therefore
d^2>=p^2+pq+q^2>=3(p+q)^2/4.
The same inequality holds when one ray is
zero. Three distinct collinear points have
their median at a force vertex, and their
two nonzero rays have angle 180 degrees.
This exhausts every nonconstant degenerate
triple without taking an unsupported limit.

For chi=1, direct expansion gives the first
two maxima exactly sqrt(2)q and sqrt(2)p.
The last is bounded by
max(sqrt(2)p+q,sqrt(2)d), using the
triangle inequality for (I+J)f_1-Jf_2.
For chi=0 its counterpart is obtained by
exchanging p and q; both comparisons below
are valid in either order.

The collapsed last maximum gives the strict
positive gap

    (2-sqrt(2))(d-(p+q)/sqrt(2)),

since sqrt(3)/2>1/sqrt(2) and p+q>0.
For the other maximum, I reconstructed the
full two-variable complete square:

    4(p^2+pq+q^2)-[(2sqrt(2)-1)p+sqrt(2)q]^2
      =2[q-(1-sqrt(2)/2)p]^2+(6sqrt(2)-8)p^2.

It is strictly positive for every p,q>=0
with p+q>0, including p=0 and q=0.
All sides before taking square roots are
nonnegative. This proves the second strict
comparison and hence the common-point
theorem in every remaining Fermat case.

The all-coincident triple has P=0 and a
zero minimum. It is explicitly separated;
it cannot occur in the physical application.

## 5. Fresh exact arithmetic reconstruction

I wrote and ran

    /tmp/review_constant_all_means_block.py.

It constructs sparse rational polynomials
over Q(sqrt(3)) and Q(sqrt(2)) directly from
the unsquared expressions, rather than
copying the author's stored coefficient
list. It independently checks:

- the collapsed-endpoint quadratic identity;
- H from 121(4D_0^2-E_0^2)-(5+6t)^2;
- all five quartic coefficients after the
  second squared comparison;
- the sqrt(3)<7/4 lower replacement;
- Q(y+1/2), its bracket endpoint and
  derivative bound, and the final quadratic
  discriminant;
- both oriented 120-degree corner expansions;
- the full vertex-case complete square;
- the fixed radical reserve 577.

All checks pass exactly. These are
reconstructions of displayed algebraic
identities and whole-domain arguments,
not a new finite positivity packet.

## 6. The unchanged physical mean and closure join

The accepted strict-turn normal form puts
the two distinct actual applications on
one inner side with chord length
0<ell_i<=1. A nonshared unit has endpoints
(0,1). At a genuine share, constant chi=1
has the actual outgoing mean (0,ell_i);
constant chi=0 has the actual incoming
mean (1-ell_i,1). The original genuine
contact remains genuine when its mean
is a side endpoint.

Set delta_i=1-ell_i. Substitution into
the exact K_i formula in Section 3 of
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md gives

    chi=1: K_i=f_(i-1)-delta_i*f_i,
    chi=0: K_i=f_i-delta_i*f_(i-1).

Adding JF_i is exactly g_i-delta_i*k_i.
Thus the new functional uses the original
support vectors and original means.

Every original f_i is nonzero and every
original support vector is nonzero by the
accepted support identity. Differentiating
the new functional at the original point
x=0 gives exactly

    -sum_i[n_i+ell_i*u_i]=0,

the negative of the actual full channel
closure equation. Convexity makes that
original point a global minimum.
The exact original virial equality is

    RP=sum_i mu_i+sum_i |g_i-delta_i*k_i|.

There is no replacement of ell_i by one,
no selection of a preferred mean, and no
discarded transverse transmitter parameter.
The force triangle is the original
counterclockwise nonconstant triangle, so
P>0. The strict common-point bound gives
R<2 for that same physical containing
radius.

All three additional squares remain
present. The separately accepted global
R>2 theorem applies to those same nine
squares, producing the required
completion contradiction.

## 7. Exact replacement scope

The proof covers every constant actual
corner bit and every independent original
mean, including zero, one, two or three
genuine shares in the accepted normal
form. Its use in the already complete
all-unique/all-side C6 assembly therefore
legitimately replaces these two rows:

| Existing row | Retired current positivity work |
| --- | --- |
| Constant-corner exactly one share | Six displayed rational 3-by-3 matrices |
| Constant-corner exactly two shares | Six displayed rational 3-by-3 matrices |

The twelve old matrix checks and their
stronger R<79/40 conclusions remain
historical alternatives. This new proof
claims only the needed R<2, together
with the separate uniform R>2
nine-square obstruction.

The 208-charge global certificate is
one shared dependency and is neither
removed nor counted again by this
replacement. No original gate closes
an additional time. No physical radial
two-corner load is identified with a
unique-corner load, and no unresolved
radial parent, stronger global radius
target, equality classification, or
Lean verification is inferred.
