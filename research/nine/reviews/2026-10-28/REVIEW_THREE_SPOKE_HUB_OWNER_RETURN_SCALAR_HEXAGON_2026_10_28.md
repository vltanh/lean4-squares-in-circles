# Full independent review: coupled three-spoke hub-owner return scalar theorem

Date: October 28, 2026. Reviewer: hexagon.

**Decision: ACCEPTED in full, with no correction.** I read the entire
scalar manuscript and entire author checker, independently rederived
the parameter-domain and lambda arguments, reproduced its complete
finite certificate, and separately proved the full two-variable
domain with a different exact Fraction interval implementation.
This is an independent acceptance of the whole stated scalar theorem,
not a check of selected boxes or sampled configurations.

## 1. Exact frozen objects reviewed

| Object | SHA-256 |
| --- | --- |
| THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_BOUNDS.md | dd6ee983deaeac1cf0c02758b2ddb2501a33175fb0281702a18027f869fdbf64 |
| certificates/three_spoke_hub_owner_return_scalar_bounds.py | d073ebfa7d1c27f8c4272a9d3b5c56e20f8de1a1ae310a8d7d790ff5c91acf99 |

The separate reviewer implementation is

    certificates/review_three_spoke_hub_owner_return_fraction.py
    fa997a188f483e06800e8c6a036749fa440fcf1ca0f3bf67d8a5ba3ba9991369.

It imports neither the author checker nor its interval code, stored
leaf cover, acceptance decisions or coefficients. It uses exact
Fraction endpoint arithmetic, separate monotone a,b formulas and an
independent 2^-64 radical enclosure, and reconstructs its own entire
binary cover. The independently generated counts differ because the
enclosures and split endpoints differ; both covers include the entire
same required actual domain.

The physical source
INNER_PENTAGON_THREE_SPOKE_HUB_OWNER_PERPENDICULAR_RETURN_DOMAIN.md,
9fa0a94b1ba2825ba4bd0b8909a0d94aa654bd8ba3b0befce4c7276501b0f1c2,
is by this reviewer and is therefore not independently accepted by
this record. Its full physical proof is assigned to a separate
reviewer. Its exact scalar map is, however, checked in Section 7
below to state precisely what the accepted theorem supplies.

## 2. Full scalar hypotheses and all mean endpoints

The hypotheses are precisely

    a>b>0, a^2+b^2=1,
    (a-b)/(a+b)<p<min(b/a,(1-b)/a),
    H=b+ap, t=1-H,
    x=1-(b/a)(1+p)>0,
    y0=a-t, v=t/(1-pH),
    E=sqrt(1+x^2), L=sqrt(1+v^2),
    g=(x+v)/(EL), h=(1-xv)/(EL),
    A0=(1+b+x*y0)/E, B0=(x(1+b)-y0)/E,
    0<lambda<=1,
    xi=B0+lambda*h, d=1-xi, k=1-A0+lambda*g>0.

I checked that no xi bound and no upper bound on k is used. In
particular lambda=1 and a possible physical k=1 remain in the
original input domain. They are not discarded at a guard or a
square-root division. There is no division by lambda, k, xi or
a proper-distance variable. The theorem proves the stronger
standalone implication without the physical caller's extra
0<xi<1 and k<=1 facts.

From 0<p<b/a<1 and H<1, the original denominator satisfies

    1-pH>1-H=t>0.

Thus 0<v<1, and 0<x<1 follows directly from its formula. Hence
g,h>0. I independently expanded

    (x+v)^2+(1-xv)^2=(1+x^2)(1+v^2)

to verify g^2+h^2=1 throughout the exact domain.

## 3. Complete elimination of the actual lambda

I rederived all three endpoint expressions

    d1=1-B0-h,
    k1=1-A0+g,
    F=g^2-g+B0*g+h(A0-1).

The only monotonicity used is h,g>0 and lambda<=1, giving
d>=d1 and k<=k1. Thus the actual strict k>0 implies the
necessary strict guard k1>0. It does not imply or assume
any upper bound on k before the certificate.

Direct expansion gives the exact identity

    g(g-d)-F = lambda*g*h-h(A0-1)=h*k.

Consequently the four certified inequalities

    d1>1/3, 1/8-k1>0, h>3/5, F>0

give d>1/3, 0<k<1/8, h>3/5 and g>d, with every
original lambda endpoint retained. No separately selected
minimum of h or g is substituted into their coupled formulas.

## 4. Entire rational rectangle and guard scope

The half-angle substitution z=b/(1+a) is bijective over the
stated positive a,b arc. Its inverse is

    a=(1-z^2)/(1+z^2), b=2z/(1+z^2).

The inequality a>b gives 0<z<sqrt(2)-1<5/12. The last strict
comparison has exact squared reserve 1/144. For the other endpoint,
r=b/a=2z/(1-z^2) increases in z, and the existence of p requires
(1-r)/(1+r)<r. The difference is strictly decreasing in r>0.
At z=19/100, its exact value is

    5213921/129538521>0.

Thus no actual point with z<=19/100 is lost by the closed cover
[19/100,5/12] x [0,1]. I recomputed both endpoint reserves by
exact rational arithmetic.

Every impossible-box test in the author checker is a necessary
strict guard, with a nonpositive upper interval endpoint:

    a-b, p-p0, b/a-p, 1-H, x, 1-pH, k1.

Each strict sign follows from the original hypotheses or the
proved lambda monotonicity. A sign cannot be inferred from a
midpoint or from a nonpositive lower endpoint. The positive
denominators a, a+b and 1+z^2 are valid on the complete outer
box; an unresolved denominator 1-pH causes subdivision, not
an interval division through zero. Intersecting t and x with
[0,infinity) is legitimate only after their strict actual
guards and retains their enlarged zero endpoints.

The separate reviewer cover uses the equivalent strict guards

    a-b, b-a+p(a+b), b-ap, 1-H, w=a-b(1+p), k1.

The denominators a and a+b are positive, so these are exactly
the same physical inequalities after multiplication. My code
does not need the author's nonnegative t,x intersections or
the multiple-expression tightening described next. It encloses
their full raw intervals and subdivides whenever a required
denominator cannot yet be certified positive.

## 5. Every interval operation and algebraic tightening checked

I read the full integer endpoint class. Its constant rounding,
four-product multiplication, positive-denominator quotient,
sign-sensitive squaring and integer-isqrt bounds are all outward.
In particular Python's floor division is used with the correct
sign for negative numerators, and ceiling division is defined
as -floor(-n/d) with positive d. The sqrt upper endpoint is
increased exactly when its integer square is below the upper
argument. No floating-point operation participates in the proof.

The three F formulas are genuinely identical. With X=1+b,

    (X+x*y0)(1-xv)+(xX-y0)(x+v)
        =(1+x^2)(X-v*y0).

Dividing by E^2 L proves A0*h+B0*g=(1+b-v*y0)/L.
The identity g^2+h^2=1 then proves the other equality. Therefore
intersecting the three independently enclosing F intervals is
safe; it does not vary g,h or the original parameters separately.

I also checked the entire subdivision routine. It normalizes
both side lengths by their root widths, chooses z on a tie,
and places the integer midpoint in both children. Their union
is exactly their parent, including every boundary. A depth
limit raises an error rather than accepting a box. Thus every
terminal decision has a mathematical reason and no unresolved
cell can be silently omitted.

## 6. Full author certificate reproduced, then independently rebuilt

Running the frozen author checker regenerated its entire leaf
file byte-for-byte. The resulting SHA-256 is

    1d6b388ad701b0a625f14c94a4b3daf7afa8d49f31f99954d414dc9b64604357.

The exact root integers, all 475 terminal decisions, all four
minimum scaled margins and the complete tree digest match the
printed source. The complete counts are

| Decision | Count |
| --- | ---: |
| Four strictly positive margins | 219 |
| Impossible p>p0 guard | 115 |
| Impossible k1>0 guard | 109 |
| Impossible p<b/a guard | 27 |
| Impossible t>0 guard | 3 |
| Impossible x>0 guard | 2 |
| Total terminals | 475 |

There are 474 splits, 949 visits and maximum depth 20. The
minimum margin numerators on denominator 2^48 are exactly

    5702628015, 39611230475,
    41648853359044, 195083550495.

The complete decision digest is

    2fa607a00554e12f173e2b44108fbf20c0b102a224262239bb96487f8f779d62.

Separately, my Fraction implementation starts at the exact
rational closed rectangle, computes a and b from their own
monotonic endpoint formulas, and uses a 2^-64 isqrt enclosure
for the remaining radicals. All other arithmetic is unrounded
Fraction arithmetic. It uses only the original F1 formula.
Its entire independent cover has

    447 splits, 895 visits,
    213 positive and 235 impossible terminals,
    448 total terminals, maximum depth 20.

The terminal/split and visit/split equalities are asserted in
the separate implementation. All four independent minimum
lower margins are strictly positive. To avoid presenting large
fractions as unexplained decimal approximations, I checked these
smaller exact rational lower floors directly against them:

| Margin | Strict lower floor for the independent positive boxes |
| --- | ---: |
| d1-1/3 | 1/13000 |
| 1/8-k1 | 1/4000 |
| h-3/5 | 7/50 |
| F | 3/5000 |

The different terminal counts are caused by the different exact
enclosures and midpoint grids. They are not a different physical
restriction: every actual point lies in both root rectangles,
each cover independently partitions its complete rectangle, and
every discard uses only the necessary guards listed above.

## 7. Exact radius consequence and physical limitation

I independently checked the complete algebraic radius expression
in Section 6. With the theorem's d,k,g,h, the terms (g-d)^2 and
2R(g-d)d/sqrt(d^2+k^2) are positive. Since k/d<3/8 and R<25/12,
the remaining term has the strict bound

    (1+h)[1+h-2R(k/d)]
       >(8/5)[8/5-25/16]=3/50>0.

The product x(x-25/16) is increasing for x>=8/5, so the last
endpoint replacement has the correct direction. No bound on a
concurrence point or a circle weight is inferred by this purely
scalar source. A physical caller must still identify its actual
point and prove the applicable radius formula for each mask.

For the stated H3 physical caller, the scalar identification is
literal: its v0 is this v, its x,y0,E,L,g,h0 are the displayed
variables with h=h0, its unchanged B-side parameter is lambda,
and its actual C coordinates are exactly xi,k. The physical
caller proves x>0 and k>0 before invoking this theorem. Its
retained lambda=1 and possible k=1 endpoints are covered by
the scalar theorem, and its additional 0<xi<1 premise is unused
by the certificate. This confirms the intended interface scope;
it is not an independent audit of my own physical proof.

## 8. Saved exact evidence and final acceptance

The author reproduction is

    /tmp/hexagon_review_h3_hub_owner_author_leaves_2026_10_28.json
    1d6b388ad701b0a625f14c94a4b3daf7afa8d49f31f99954d414dc9b64604357.

The complete independent Fraction run is

    /tmp/hexagon_review_h3_hub_owner_fraction_results_2026_10_28.json
    f2994e3a8a6f3f78af58d51cadb3c8d333031cba3a443c79e0e918ff51d62e60.

The exact endpoint, floor, hash and full count readback record is

    /tmp/hexagon_review_h3_hub_owner_scalar_exact_checks_2026_10_28.json
    61691ded3f18569233d58241f525e9fd528b3bf526957c7b9d473a7a5524979b.

The complete scalar theorem and its full checker are independently
accepted at the unchanged pins in Section 1. There is no correction,
unresolved cell, discarded original mean endpoint, or extra physical
premise. This record does not itself change a graph/load-family flag,
metadata file or frozen source. No compilation, CI or remote action
was used.
