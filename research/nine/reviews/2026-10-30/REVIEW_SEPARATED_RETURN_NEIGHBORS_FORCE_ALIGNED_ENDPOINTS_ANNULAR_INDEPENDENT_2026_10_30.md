# Independent review of the complete tilted-long-endpoint exclusion

**Date:** October 30, 2026 UTC. **Reviewer:** annular-capacity agent.

**Verdict: PASS at the complete stated local and seven-cycle scopes.
No source repair is required.**

## 1. Frozen assembly and review boundary

I read the complete source
`SEPARATED_BOUNDARY_RETURN_NEIGHBORS_FORCE_ALIGNED_LONG_ENDPOINTS_2026_10_30.md`
and independently reconstructed every new inequality and every import-to-caller
join. The reviewed frozen object is 16,456 bytes with SHA256

`9c7f47ce87b5a7d548ec76c33f5912adae870211770ea578f15621a78104ca06`.

The source was not edited. I had previously suggested coupling the two
occupied normal-chord points and independently checked the author's proposed
both-tilted and mixed estimates before this assembly was frozen. This review
discloses that mathematical discussion and checks the full resulting argument,
including its precise hypotheses and all circle-mask cases.

The main input is the complete endpoint-locus and tilted-vertex reduction,
SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`.
I independently reviewed that entire source, including its two-circle quotient
and aligned-other-endpoint exclusion. Its full hypotheses are met here: both
long endpoints have true positive degree two; their sole other neighbors are
physical-boundary units wholly above zero; their original force, angular,
normal and mean data are retained. The common long channel consists of two
genuine unloaded true-degree-two internal units.

The additional exact chord source
`3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3`
has also received my full independent review. It applies to precisely the
original means and normals used in the new distance contradiction.

## 2. Original return normal at a tilted endpoint

Under the tilted hypothesis, the imported result supplies the actual lower-
inner long vertex `q=(x,t)`, upper-inner return vertex `p=q+(b,a)`, and
the possible circle corners `z_-=q+(a,-b)` and `z_+=z_-+(b,a)`.
The original return normal has positive global y component. Full y-force
balance gives a negative total circle y resultant; positive total circle
load and positive corner x coordinates give a positive x resultant.

The return force line meets the horizontal long line at `(x0,t)`. Substituting
the full force equation into the full origin-moment equation gives exactly
`x0=t*m_x/m_y`, where m is the original circle vector. This derivation does
not impose concurrence as an extra premise or move the actual application.

For two physical circle corners, `m_y/m_x` is their slope average with
nonnegative weights proportional to their original weight times corner x.
The upper corner's slope is strictly larger: the numerator of the slope
difference is `a(x+a)-b(t-b)>0`. Thus the lower circle corner minimizes
the negative resultant slope over the whole allowed mask. Since t is
negative, the reciprocal-slope inequality has the direction used in the
source. It follows that the actual inward-horizontal to upward-normal ratio
is bounded below by

    [tau*(a-b)-b*(x+b)]/[a*(tau+b)], tau=-t>1/2.

The numerator is positive under the displayed uniform bounds. Removing the
denominator factor `a<=1` therefore preserves a lower bound. The remaining
quotient increases in tau, increases in `a-b`, decreases in x, and decreases
in b over the positive domain. Substitution gives exactly

    7401/10960 > 2/3,
    7401/10960-2/3 = 283/32880.

The auxiliary estimates are also valid: the square reserve for `a-b>37/40`
is `19/2880`, and subtraction from `a+b<16/15` gives `b<17/240`.
Consequently the original global inward component exceeds `2/sqrt(13)`
and then `11/20`, with square reserve `27/5200`. Its global sign is
proved by this calculation, not inferred incorrectly from the tilted own
normal cone. Reflection supplies the left-endpoint statement.

## 3. Whole angular interval, including all endpoints

For fixed `A>0,B<=0`, the derivative of

    (A-cos(theta))^2+(B+sin(theta))^2

has the sign of `A*tan(theta)+B` on the stated acute interval. This
quantity is increasing, so its only possible interior critical point is a
minimum. The maximum is at an endpoint, including the case B=0.

Applying this first with one normal angle fixed, and then to the other,
reduces the two-normal distance to the four corners of the entire angle
rectangle. For `2<=L<21/10`, the mixed angular corner is largest. Direct
expansion gives the differences from the two same-angle corners as
`2(1-c0)(L-1)` and `2(1-c0)(1+2c0-L)`, both positive.
Thus the exact largest value is `1+k^2-(11/10)k`, with `k=L-1`.
This is a continuous maximum proof, not a finite sampling argument.

## 4. Both long endpoints tilted

The two actual return vertices have horizontal difference
`L=2+b_A+b_B` and vertical difference `a_B-a_A`. The original support
equalities, together with the strict endpoint center bound, yield
`(a_A+b_A)+(a_B+b_B)<31/15`. With `a_i>199/200`, this gives

    L<623/300, |a_B-a_A|<1/200.

Removing just that vertical difference temporarily leaves exactly the
two-angle function from Section 3. Its upper bound is

    87739/90000 < (199/200)^2,
    (199/200)^2-87739/90000=5453/360000.

The polynomial increases for `k>=1`, so substituting the upper endpoint
is legitimate. Restoring the actual vertical displacement by the triangle
inequality gives a strict distance below one. The compared points are
`p_A+n_A` in D and `p_B+n_B` in C by the actual normal-chord lemma.
This contradicts the assumed set distance at least one. Neither a common
return-square frame nor an identification of a mean with a center is used.

## 5. Mixed branch: the aligned endpoint's coupled height and normal

For the aligned left endpoint, the actual long side interval and
`tau=-t>1/2` imply `Y=-y_A>0`. Thus its lower outer corner is its
unique physical circle corner; this uniqueness is derived rather than
imposed as a mask. Defining

    e=Y+1/2-tau, H=1-e

gives exactly `0<=e<1/8`, `tau+e<=5/8`, and the actual return
vertex `p_A=(-x,t+H)`. Eliminating its complete two-edge force and
moment equations gives the slope

    h_A=[tau-x*e]/[(tau+e)(1-e)].

Every denominator is positive. The ratio increases with tau and decreases
with x. After replacing tau by one half, its derivative in e is negative
throughout `[0,1/8]`. Enlarging to the closed parameter box therefore gives
the lower bound `358/525>2/3`, whose excess is `8/525`.

The exact rewrite used for the upper bound, with `x+1>119/60` and
`tau+e<=5/8`, gives `h_A<=1-2e`. The comparison after clearing
`1-e` has the nonnegative difference `(13/75)e+2e^2`, including
the case e=0. This upper bound controls the upward unit-normal component:

    beta_A>=1/sqrt(1+(1-2e)^2)>2/3+e.

For the strict second inequality, the source's positive polynomial is
increasing on the whole interval and has final value `9025/9216<1`.
Its derivative indeed contains the positive factor `1-5e+12e^2`.
The crucial consequence `H+beta_A>5/3` therefore retains the actual
height-normal correlation. The separate bounds `alpha_A>11/20` and
`beta_A<21/25` also hold with the correct strict signs.

## 6. Mixed branch: the complete normal arc is below distance one

With the aligned endpoint held fixed, the other original unit normal ranges
inside the same enlarged acute interval. The difference of the two actual
occupied chord points has squared norm

    (L-alpha_A-cos(theta))^2
      +(a-H-beta_A+sin(theta))^2.

Here `L-alpha_A>0` and `a-H-beta_A<0`; hence the already proved
single-variable endpoint maximum theorem applies. There is no omitted
interior angle or alternative sign branch.

At angle zero, the horizontal difference is positive and below `25/48`.
The vertical difference is negative and has magnitude below `169/200`.
The exact squared bound is

    1418821/1440000 < 1.

At the other angular endpoint, the horizontal difference is positive and
below `233/240`. The vertical difference lies strictly between `-9/200`
and `13/75`; since the latter is the larger absolute bound, its squared
norm is below

    1400489/1440000 < 1.

These estimates cover the entire normal interval and hence the original
normal. The actual two chord points again contradict the set gap of one.
Both tilted and mixed possibilities are exhausted, proving the local
theorem that both long endpoints possess a side axis along the long normal.

## 7. Local scope and complete seven-cycle caller

The local argument uses physical-boundary status and the actual above-side
location of C,D, but no degree restriction at either C or D. Their set
distance condition may come from any valid geometric source. There is no
planarity or lower-radius premise in the local theorem itself.

For the stated opposite seven-cycle, the inherited compatible embedding
and radius window activate the frozen whole-return-side theorem
`c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e`.
Its conclusion gives the full squares C,D in `y>1/120`. The genuine
unloaded true-degree-two short transmitter propagates a common normal;
its actual support equalities give a gap at least its unit-square width,
hence `dist(C,D)>=1`. All hypotheses of the local theorem then hold.
Extra endpoint forces at C,D are allowed, while extra forces at A or B
would violate the explicitly retained true-degree-two premise.

This proves the advertised entire tilted-long-endpoint branch exclusion.
It does not align the other three cycle squares, make the joins vertical,
force internal heights equal, discard the two other packing squares, or
close the remaining sharp aligned-endpoint inequality. These limits are
stated correctly in the source. The record and staggered equality examples
remain compatible with the conclusion.

All source pins and the exact rational constants were checked alongside
the complete hand reconstruction. No source mutation, numerical packing
search, pose grid, stress replacement, Lean compilation, CI execution,
original ledger modification, or remote publication was performed.
