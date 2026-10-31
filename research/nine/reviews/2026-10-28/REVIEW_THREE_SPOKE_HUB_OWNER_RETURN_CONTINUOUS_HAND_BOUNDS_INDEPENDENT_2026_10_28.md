# Independent full review of the continuous hub-owner return scalar

Date: October 28, 2026 UTC.

Reviewer: return_scalar_independent, independent of the authors of the
reviewed construction. The reviewer did not supply a discovery argument,
estimate, identity, or source edit before freeze. The complete frozen
manuscript was read, including every intermediate domain and the final
restoration of the original parameter.

**Verdict: PASS, without a source repair.** The continuous proof proves
the exact four outputs of the old scalar theorem throughout its entire
unchanged coupled domain. The stronger unconditional estimates and the
guarded bound `F>467/40000` also hold as stated. This is a full proof
review, not a review of only the last polynomial or of a difference from
the old interval certificate.

## 1. Exact reviewed bytes and adoption scope

The complete new mathematical source read and checked is

    THREE_SPOKE_HUB_OWNER_RETURN_CONTINUOUS_HAND_BOUNDS.md
    SHA256 7ce73e2445b0047ed40b12b103e5999be8e3afabdcdf5033f0f727c10bf2498c.

For literal comparison of the old theorem, domain, endpoint conventions,
and claimed arithmetic replacement, I read the entire old theorem and
its original checker as text. The following current hashes were checked:

| Historical record | SHA-256 |
| --- | --- |
| `THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_BOUNDS.md` | `dd6ee983deaeac1cf0c02758b2ddb2501a33175fb0281702a18027f869fdbf64` |
| `certificates/three_spoke_hub_owner_return_scalar_bounds.py` | `d073ebfa7d1c27f8c4272a9d3b5c56e20f8de1a1ae310a8d7d790ff5c91acf99` |
| `certificates/review_three_spoke_hub_owner_return_fraction.py` | `fa997a188f483e06800e8c6a036749fa440fcf1ca0f3bf67d8a5ba3ba9991369` |

The new proof is self-contained real algebra and calculus. Those
historical files, their arithmetic results, and their 475 terminal boxes
are not proof premises. No old checker was executed in this review.

This verdict accepts the scalar theorem only. A separate same-export
caller join and its full review must identify the actual physical
applications before the historical certificate can be retired from the
current geometric dependency route. No original graph/load gate, family
flag, coarse/fine count, or complete global theorem is closed by this
scalar review alone. In particular, the separate equal-roof-separation
certificate is not being counted or reviewed again here.

## 2. Literal domain equality and elimination of lambda

The new source uses exactly the old domain

    a>b>0, a^2+b^2=1,
    p0=(a-b)/(a+b)<p<min(b/a,(1-b)/a),
    H=b+ap, t=1-H,
    x=1-(b/a)(1+p)>0, y=a-t,
    D=1-pH, v=t/D,
    E=sqrt(1+x^2), L=sqrt(1+v^2),
    g=(x+v)/(EL), h=(1-xv)/(EL),
    A0=(1+b+xy)/E, B0=(x(1+b)-y)/E.

The name `y` replaces the old `y0` without changing its expression.
The original parameter remains `0<lambda<=1`, with

    xi=B0+lambda h, d=1-xi, k=1-A0+lambda g,

and the only further guard is `k>0`. No restriction on `xi`, no upper
bound on `k`, and no separately selected value of any coupled scalar is
introduced. The original `lambda=1` is included. An original `k=1`
is excluded by the proved bound, rather than removed from the domain.

The elementary signs imply `g,h>0` and `g^2+h^2=1`. I expanded the
exact identity

    g(g-d)=F+hk,
    F=g^2-g+B0g+h(A0-1).

The inequalities `d>=d1=1-B0-h` and `k<=k1=1-A0+g` follow solely
from `lambda<=1`. Thus actual `k>0` necessarily implies `k1>0`.
The new proof validly proves `d1`, `k1`, and `h` bounds without that
guard, then proves the `F` bound with this necessary guard. There is no
division by `k`, `lambda`, `xi`, or a possibly zero proper length.

## 3. Elementary range bounds and the closed lower endpoint

Writing `r=b/a`, the nonempty strict interval `p0<p<r` gives
`r>sqrt(2)-1` and `0<p0<sqrt(2)-1`. The split at `b=1/2` proves
`p<1/sqrt(3)` with both upper bounds retained; the meeting case is
covered by both arguments. The increasing function `r/(1+r^2)` on
`0<r<1` gives `ab>1/(2sqrt(2))` and hence `b>1/3`.

For `T=a-bp`, the identities `H^2+T^2=1+p^2` and `H>T>0`
are correct. They imply `H>1/sqrt(2)>7/10` and `0<t<3/10`.
The relations

    q=1-p>21/50,
    D=q+pt>q>0,
    D-t=H(1-p)>0

give `0<v<1`. The original lower bound on `p` gives
`0<x<p0<sqrt(2)-1`; consequently `xv<1`, so the angle
`chi=atan(x)+atan(v)` is on the branch `(0,pi/2)`. There is no
ambiguous sign in identifying `g=sin(chi)` and `h=cos(chi)`.

For fixed original `a,b`, decreasing `p` to `p0` keeps every strict
upper bound valid, increases the positive `x`, and keeps `t,D,E,L`
positive. The endpoint only replaces `H>T` by `H=T` and `x<p0`
by `x=p0`; these equalities do not break any subsequent estimate.
The separate endpoint family extended to `z=0` and
`z=sqrt(2)-1` also has positive denominators.

The bound `E<11/10` follows from `x^2<1/5`. Since `y=a-t>0`,
the stated `A0>40/33>1>g` is valid throughout the original domain
and its fixed-`a,b` lower-endpoint continuation.

## 4. Unconditional angle and k1 bounds

The estimate

    v^2<t^2/q^2<(250/147)t<2t

has the correct strict signs. The convex tangent bound for
`(1+z)^(-1/2)` therefore proves `1/L>H`. Substitution into the
exact numerator of `B0+h` gives

    B0+h=[x(1+b-v/L)+t-a+1/L]/E>(1-a)/E>0.

This combination is proved without using the later guarded bound on
`B0`, so the fixed-`a,b` monotonicity is not circular.

I independently differentiated all the coupled expressions:

    x'=-r, y'=a,
    v'=-M/D^2, delta'=-M/K^2,
    A0'=rB0/E^2+ax/E,
    B0'=-rA0/E^2-a/E,

where `M=a+b-1+t^2>0` and `K^2=D^2+t^2`. The identity
`M=aD-t(H+ap)` is exact. These give

    g'=h(-r/E^2+delta')<0,
    k1'=-r(B0+h)/E^2-ax/E+h delta'<0.

At `p=p0=z`, I checked the complete formulas for `a,b,H,x,A0`
and `w=tan(chi)` in source (19). On the entire closed interval
`0<=z<=sqrt(2)-1`, the printed derivatives prove that `A0`
decreases and `w` increases. In particular, `u^3<2` is sufficient
for the first sign, and
`sqrt(u)(1+3z-2z^2)<11/4<2sqrt(2)` proves the second.
The tangent remains positive and on the correct branch. Thus both
endpoint `g` and endpoint `k1=1-A0+g` increase with `z`.

The endpoint values `A_star` and `w_star` are algebraically correct.
I checked the rational reserves proving

    A_star>77/50,
    w_star<8/9,
    g_star<8/sqrt(145)<133/200.

These are respectively supported by the positive reserves
`11/8750`, `485^2-2*342^2=1297`, and
`133^2*145-64*200^2=4905`, with all quantities squared positive.
The two monotonic reductions therefore prove on the entire original
domain

    0<g<133/200,
    k1<1-77/50+133/200=1/8.

Finally `g^2+h^2=1` and `h>0` give
`h^2>22311/40000>(149/200)^2`, hence `h>149/200>3/5`.
No positive-`k1` restriction was used.

## 5. Entire derivative-control polynomial for d1

I expanded `Q=K^2-N`, where `N=xD+t`, directly. All coefficients
in source (26) are correct, including

    C=a(2b-1)+(b/a)(1-b)-b.

The proof deliberately extends the polynomial to `[0,P]` without
requiring `x>0` there; it does not infer any physical or trigonometric
statement on that extension. Since `a>1/sqrt(2)`, the displayed
second derivative of `Q'` is positive, so `Q'` is convex. Negative
values at both endpoints are therefore sufficient for negativity
throughout the whole interval.

The two elementary arguments proving `C<0` cover `b<=1/2` and
`b>=1/2`, including equality. At `P=b/a`, I independently obtained

    a^2 Q'(P)=a(8b^3-2b^2+5b-1)-(3b+2b^3).

The multiplying polynomial is positive on `1/3<b<=1/2`, so
substituting the strict concave-square-root bound
`a<1-b^2/2` has the correct direction. The factorization in (28)
is exact, its remaining bracket is positive, and its strictness
persists when `2b-1=0`.

At the other endpoint `P=(1-b)/a`, I independently checked the
substitution giving

    Q'(P)=(2P^4+7P^3-4P^2+3P-2)/(1+P^2).

Using `P^2<=1/3` gives precisely the stated increasing quadratic
upper bound. Its value at `1/sqrt(3)` is
`(16sqrt(3)-28)/9<0`. Thus `Q'<0` on the complete interval in
both branches.

For the final endpoint values, the `H=1` branch gives exactly
`Q(P)=q(q-x)>=qP^2>0`. The `p=b/a` branch gives

    Q(P)=p[1+5p-2(1+p)sqrt(1+p^2)].

The squared comparison polynomial is the printed
`G=-3+2p+17p^2-8p^3-4p^4`. Its derivative is positive on the
whole relevant interval, and its value at the lower endpoint is
`34-24sqrt(2)>0`. Both sides being squared are positive. These
are proofs on the full endpoint curves, not evaluations at sample
points. Since `Q` decreases, the complete conclusion `K^2>N`
holds at every original point and every needed lower-endpoint value.

## 6. Whole-domain d1 monotonicity and endpoint estimate

The derivative

    d1'=a/E+r(A0-g)/E^2-gM/K^2

follows from the previously checked derivatives and
`h=cos(gamma+delta)`. On the actual domain and its lower-endpoint
continuation, `N>0`, `M>0`, `M<aD<aK`, and `K^2>N`.
Consequently `NM<aK^3`, making the first and last terms combined
strictly positive. The middle term is positive because `A0>g`.
Thus `d1` increases with `p` throughout the required interval.

At the lower endpoint I independently checked

    B0=(1+z)/sqrt(1+z^2)-sqrt(2),
    d1=1+sqrt(2)-S,
    S=cos(psi+delta)+cos(psi)+sin(psi).

For `0<=z<=1/8`, the angle monotonicity already proved implies
`h<=h(0)`. The exact bound
`h(0)^2=2/(5-2sqrt(2))<35/38<(24/25)^2` is valid, with reserve
`13/23750` in the last comparison. The increasing second summand
is at most `9/sqrt(65)<28/25`. Thus this entire interval gives
`S<52/25`.

For `1/8<=z<=sqrt(2)-1`, the comparison `v>5/16` is equivalent
to (35) after multiplication by positive denominators. The
derivative numerator `16z-10z^2-5` is negative on the full interval,
and the squared reserve at `z=1/8` is `7847/4096`. This proves
the strict comparison also at both endpoints of this second interval.
The decreasing function `(1-v)/sqrt(1+v^2)` and Cauchy--Schwarz then
give the printed bound (36). I checked both radical comparisons
`sqrt(281)>50/3` and `sqrt(3)<26/15` and their reserves.

The two intervals meet without a missing endpoint and prove

    d1>sqrt(2)-27/25>1/3,

the last strict inequality following from
`2-(106/75)^2=14/5625>0`. Monotonicity transfers it to every
original `p`. The proof of this conclusion is independent of `k1>0`.

## 7. Necessary ratio restriction under the positive-k1 guard

For the remaining argument only, `k1>0` is a necessary consequence
of the actual `k>0`. The two already proved monotonicities imply
that the lower-endpoint value of `k1` is positive and that this
endpoint value increases with `z=p0`. I checked the estimates at
`z=3/10`:

    A0>157/99>19/12,
    u^(3/2)/sqrt(2)>4/5,
    w<5/7,
    g<5/sqrt(74)<7/12.

All roots and denominators are positive. The displayed strict
rational reserve `19/12375` and the squared reserve `26` are
correct. Therefore that endpoint `k1` is negative, proving
`p0>3/10`, `r<7/13`, and `b<7/sqrt(218)<19/40` under the guard.
The derived lower bound `a>7/8` follows from the printed positive
reserve `7/800`. These restrictions are proved consequences of
the guard, not extra hypotheses added to the theorem.

## 8. Entire guarded lower bound for A0

The two original bounds on `p` correctly give

    x>1-r-r^2>29/169,
    r<(1-x)/(1+x),
    x<sqrt(2)-1.

I independently eliminated `p` to obtain source (43). The derivative
of its rational-radical summand `f(r)` and its numerator at
`r_max=(1-x)/(1+x)` are correct. For `x>=1/3` the derivative is
nonpositive throughout the allowed ratio interval. Its endpoint
is exactly the already treated `p=p0` family with `z=x`; hence
that entire branch gives `A0>77/50`.

For `x<=1/3`, the printed square identity for
`f(r)^2-4B(A-B)` is exact. Positivity permits taking its square
root, giving `A0>=J(x)`. The full second derivative of `J` is
correct, and the bounds `2/9` and `4` prove strict concavity
throughout `[29/169,1/3]`. The four endpoint radical comparisons
and their integer reserves `19568`, `2791`, `6`, and `23` are
correct. A concave function is at least the lesser endpoint value;
therefore `J>31/20>77/50` throughout this interval, including its
endpoints. The two branches cover the entire guarded range and
agree at `x=1/3` without needing a strict branch choice.

## 9. The complete guarded first-crossing reduction for B0

The proof of `B0>-1/4` uses the original fixed `a,b`, with only
`p` varied continuously down to `p0`. The derivative `B0'<0`
was proved independently of this claim. At `p0`, the exact value
is `sqrt(2)(a-1)>-1/4` by `a>7/8`. Therefore an actual value
`B0<=-1/4` gives one unique crossing in `(p0,p]`.

Every strict upper bound on `p`, the positive `x`, and all coupled
formulas remain valid at that crossing. Since `k1` decreases with
`p`, its value at the crossing is at least the actual positive
value. This also covers an original value exactly equal to
`B0=-1/4`. The reduction therefore loses no equality case.

I derived all formulas in (47) from `B0=-1/4`, including

    c=1+x+E/4,
    b=(1-x)/c,
    p=ac-1,
    t=a-x(1+b)-E/4,
    (1+p)^2=c^2-(1-x)^2.

The auxiliary `c` is separate from the original `d=1-xi`.
The formula for `b'` is exact and strictly negative. For
`x<=1/4`, the rational comparisons indeed force
`b>96/193>19/40`, contradicting the guard consequence. At
`x=7/20`, the stated bounds give `p>9/20>r`; meanwhile `p(x)`
increases and `r(x)` decreases. Thus original `p<r` proves

    1/4<x<7/20

at every possible crossing. The reserves `1655` and `273/6400`
and all denominator signs are correct.

## 10. Crossing A0 bound and the two affine comparisons

The crossing identity gives `A0=(1+b)E+x/4`. On the whole
closed crossing interval, the bounds `c<13/8`, `b<1/2`, and
`x/E<1/3` prove exactly

    A0'<-128/169+3/4=-5/676<0.

The right-endpoint estimates
`E>1059/1000` and `b>2/5` therefore yield
`A0>15701/10000>157/100`. The square-root reserve `1019/1000000`
is correct. This bound is obtained directly on the crossing;
it does not presume the desired lower bound on `B0`.

For `p_bar=7x/4-1/8`, I expanded the square comparison against
`R_x`. The remainder in (54) is correct, and replacing
`-x^3/4` by `-(7/80)x^2` is a valid lower bound on the whole
interval. The resulting quadratic has discriminant `-31/320`
and positive leading coefficient. Since both square roots are
positive, this proves `p<p_bar`.

For `t_bar=17/40-3x/4`, multiplying the exact expression for
`t` by `c>0` gives precisely `sqrt(R_x)<A+BE`, with the printed
polynomials `A,B`. Both are positive throughout the interval.
The bounds in (56) are valid: `A` increases on this interval,
`B` increases, and their left endpoint values are `221/256`
and `139/320`. Therefore the coefficient of `E` in the squared
difference is strictly positive, with reserve `117/1960`.

The inequality `E>=1+(12/25)x^2` follows by squaring two
positive quantities, using `x^2<25/144`. Substituting this
lower bound into its positive coefficient has the correct
direction. I independently expanded the complete resulting
polynomial and obtained exactly

    640000 * lower_bound
      =95625-733500x+1779929x^2-1299876x^3
             +536120x^4-132000x^5.

I also checked every coefficient in the full substitution
`x=3/10+s` in (59). With `|s|<=1/20`, subtracting the absolute
value bound for every nonconstant term is valid regardless of
the sign of `s`. The exact remaining lower bound is
`1265287/2000>0`. This is a single estimate covering the complete
closed interval, with no subdivision, sampled sign, or hidden
coefficient packet. It proves `t<t_bar` throughout the crossing
interval.

## 11. Complete crossing contradiction and guarded F bound

The quantities `p_bar,t_bar` both lie in `(0,1)` on the complete
crossing interval. The two printed partial derivatives of
`v=t/(1-p+pt)` are positive on this rectangle, and its denominator
is positive. Thus simultaneous substitution of the two strict
upper bounds is justified by monotonicity, not by treating an
uncoupled extremum as the original value.

I expanded the complete identity (61) after `s=7/20-x` and
checked all four coefficients. On `0<=s<=1/10`, its constant
is positive, its linear term is nonnegative, and its last two
terms combine to a nonnegative expression. Hence

    x+v<5/8,
    xv<25/256,
    tan(chi)<160/231,
    g<160/sqrt(78961)<57/100.

The product bound follows from `4xv< (5/8)^2` via
`4xv<=(x+v)^2`, and all denominators and angles keep their
previous positive signs. The final squared reserve `544289`
is correct. Together with `A0>157/100`, this gives `k1<0`
at the hypothetical crossing, contradicting its necessary
positive value. Thus `B0>-1/4` holds on the whole guarded domain.

Now `g>0`, `A0>77/50`, `B0>-1/4`, and `h>149/200` imply

    F>g^2-(5/4)g+4023/10000
      =(g-5/8)^2-25/64+4023/10000
      >=467/40000>0.

The strict inequality before the completed square makes the final
strict bound valid even if the square vanishes. All four quantities
come from the original coupled formulas, and the necessary guard
has been justified before any of these guarded estimates is used.

## 12. Original parameter restoration and radius export

Restoring the unchanged `0<lambda<=1`, the unconditional
`d1,k1,h` estimates give

    d>1/3, 0<k<1/8, h>3/5.

Actual `k>0` gives `k1>0`, so the guarded estimate for `F` applies.
The exact identity `g(g-d)=F+hk>0`, with `g>0`, proves `g>d`.
This establishes the full old four-output theorem, including
`lambda=1`, without a manufactured restriction on `xi` or an
assumed upper bound on `k`.

The scalar radius consequence also follows with the exact old
scope `0<R<25/12`. Dropping the nonnegative square and positive
cross term, and using `sqrt(d^2+k^2)>d`, gives the displayed
strict lower bound

    E_R>(1+h)(1+h-2Rk/d).

The bounds `k/d<3/8` and `1+h>8/5` give
`E_R>(8/5)(8/5-25/16)=3/50>0`. The relevant factors are
positive, so multiplying the lower bounds preserves direction.
As the source states, this does not itself identify a real square
point or cover a physical circle mask; those are caller obligations.

## 13. Verification record and final verdict

In addition to the independent hand derivations above, I used exact
rational arithmetic to verify the printed coefficient identities
(58)--(61) and their rational remainder. This only checked finite
displayed identities and constants. It did not search for a bound,
sample a domain, evaluate a packing, reconstruct an interval cover,
or execute either historical checker. The proof of positivity is
the complete printed continuous argument reviewed above.

The new source remained at the exact frozen hash in Section 1
throughout the review. No source repair, proof edit, change to an
original normal or mean, Lean/Lake invocation, CI/workflow dispatch,
remote write, commit, or accounting mutation was performed by this
reviewer.

**Accepted in full:** the new source supplies the identical four
scalar exports, with stronger proved reserves, over the identical
original domain. Subject to the separate exact caller join and root
adoption, the one historical certificate containing 475 terminal
boxes can be replaced by this continuous hand proof. This acceptance
does not by itself retire unrelated certificates or close any new
original graph/load row.
