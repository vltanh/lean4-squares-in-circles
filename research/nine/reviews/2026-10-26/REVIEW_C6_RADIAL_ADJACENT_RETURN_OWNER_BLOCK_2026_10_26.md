# Independent review of the complete strict-turn adjacent/return-owner C6 exclusion

Date: October 26, 2026.

Reviewer: block-attachments agent, independently of the source author.

**Result: PASS for all three local statements and the whole stated
physical A/T family join.** This does not close A/O, a lower-turn
placement, or the unrestricted one-radial parent.

Sources reviewed in full:

- SIX_CYCLE_RADIAL_ADJACENT_RETURN_DIAGONAL_BOUND.md;
- SIX_CYCLE_RADIAL_RETURN_OWNER_HEIGHT_BOUND.md;
- SIX_CYCLE_RADIAL_ADJACENT_AND_RETURN_OWNER_EXCLUSION.md.

The physical local charts were checked against the accepted adjacent
classification and the actual shared-return chart in
SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md.
All force and norm identities below use the original applications.

## 1. Adjacent endpoint: the full m+H>9/10 bound

The accepted adjacent chart has
V=v-tz=(tA-c,c), G=V/|V|, with the actual return normal
horizontal. Its strict turn is exactly G_x<0, so tA<c.
Substitution gives
c^2 a>(1-sc)b. With b>1/2 and a<R<133/64, this
excludes c<=3/8 by the exact contradictory reserve 83/4096.

In the actual own frame the radial port is

\[
 P=(a-1-(1-ta)/L)v+(b+tb/L)u.
\]

Thus b<=r_0, and a^2>=2d+1. These are valid also at t=0,
including an original genuine mean already at the adjacent vertex.
The exact inverse-coordinate identity is

\[
                   m+H=c(a-b)+s(a+b-2).
\]

Both coefficients are positive on the whole original domain.
Its angle second derivative is its negative, so the complete
angle interval is controlled by its two endpoints. At c=3/8,
substitution a=sqrt(R^2-b^2) gives a concave expression in
b on the full real interval [1/2,r_0]. Its two endpoints are
therefore sufficient as scalar comparisons; no physical angle or
mean is changed by these comparisons.

I independently checked the reductions at all three endpoints:

\[
 \eta=\pi/4:\quad \sqrt2(a-1)>14/15;
\]
\[
 c=3/8,\ b=1/2:\quad
       (423+41\sqrt{55})/800>227/250;
\]
\[
 c=3/8,\ b=r_0:\quad
       (27+10\sqrt{55})/112>101/112
                                  =9/10+1/560.
\]

The comparison interval stays real because r_0<R, and all
coefficients used with lower bounds are positive. This proves
the entire local adjacent theorem with its stated scope.

## 2. Return-owner height: H<7/10 on the whole original mean interval

In the original T chart, a>b>1/2, t=1-H/b in [0,1),
X=1-ta>0 and Y=1-tb>0. Hence x<=1/sqrt(2)<=y.
The unchanged radial port is P=(a-1-x,b-1-y).

Under H>=7/10, the comparison ratio X_0/Y_0 is legitimate:
Y_0>0, and the exact Cauchy inequality
a+(7/10)b<203/80 makes

\[
 b(X_0-7Y_0/12)\ge
       (77/60)b^2-(3623/1200)b+1421/800>0.
\]

The quadratic's negative discriminant was independently checked.
The exact derivative of X/Y in H is
(a/b-1)/Y^2>0, so the comparison implies x>1/2 and
y<sqrt(3)/2. This includes the original endpoint H=b.

For b>=1, the complete norm comparison follows from
|a-1-x|<1/3 and |b-1-y|<sqrt(3)/2. Its strict
upper bound 31/36 is below the actual radial norm squared.

For 7/10<=b<=1, I independently expanded the polynomial
in source equation (13) from its factored definition. The negative
fifth and sixth powers are correctly bounded by multiples of z^2
on z in [0,3/10]; deleting the positive cubic and quartic
leaves the displayed strictly positive completed square. Positive
squaring then gives x>11/10-(3/5)b on that entire interval.

The fixed-R derivative of sqrt(R^2-b^2)+(3/5)b is positive
throughout the comparison interval up to b=1. This proves the
claimed first-coordinate bound |a-1-x|<R-7/4, including
its negative-coordinate alternative.

The second-coordinate identity is exact:

\[
 y_0-r=\frac{(b-h)(a-b)}b
                 \frac{x_0+y_0}{2L_0(y_0+r)}.
\]

The inequalities x_0+y_0<=sqrt(2), y_0+r>=sqrt(2)
and 2bL_0>a-b have the required directions. The latter follows
from the displayed whole-interval linear comparison, whose weakest
point is b=1. Thus |b-1-y|<=3/10+r, with the weak
endpoint retained. The remaining radial-norm difference is the
increasing function g(R) given in the source; its exact positive
lower reserve at the original lower radius is 3/280.

Both b intervals contradict the same original radial-port norm,
proving H<7/10 without changing any mean.

## 3. Return-owner diagonal: a-H>11/10

The elementary strict bound
(a-1)x+(b-1)y>b-1 is valid on both sides of b=1.
Subtracting the original radial norm gives a+2b<3+d.
The monotone a+2sqrt(R^2-a^2) comparison and its explicit
two-square endpoint calculation give a>8/5.

For b>=1, squaring a+2b-2<d+1 is legitimate on positive
quantities. The resulting Q(a,b) is nondecreasing in a and
strictly increasing in b in the asserted domain, and
Q(8/5,7/6)=1/15. Hence b<7/6.

Under the contrary a-H<=11/10, the already proved H<7/10
therefore yields 8/5<a<9/5 and H>=H_*=a-11/10>0.
For the scalar comparison normal, Y_*>0. Independent
differentiation gives

\[
 \frac{\partial}{\partial b}(X_*/Y_*)=
 \frac{-(a-1)(b-aH_*/(a-1))^2
              -aH_*(1/10)/(a-1)}{b^2Y_*^2}<0.
\]

At each largest comparison b, X_*>0 as displayed. The ratio
monotonicity therefore propagates positivity over the entire
comparison interval before any normalized-coordinate comparison
is used. No negative or zero artificial normal enters the proof.

For b>=1, I rebuilt source equation (17) from
Xhat=3/35+(4/5)u+(6/7)u^2,
Yhat=1/3+u and lambda=6/25+u.
The four negative tails on 0<=u<=1/5 leave exactly the positive
quadratic coefficient 143471/6890625. The resulting first-coordinate
bound and x>6/25 give |P|^2<134/125, with strict radial
reserve 61/10000.

For b<=1, the actual domain is 17/10<a<9/5 and
4/5<b<=1. I rebuilt source equation (23) from
Xhat=23/50-(3/2)z+z^2,
Yhat=7/10-z and lambda=137/250-z.
The stated tail bounds leave the exact positive linear coefficient
530557/15625000, proving |a-1-x|<63/250.

The actual second-coordinate estimate uses the actual H:
L>=a-b-1/10 and the concave quadratic
-(3/2)b^2+(17/5)b-17/10 has endpoint values 3/50,1/5.
Thus a-b<(3/2)bL and the exact identity gives
y-r<=(3/4)(b-H), including H=b. The final fixed-R
comparison of 3a+b is increasing throughout its full comparison
interval, so |b-1-y|<3/10+r. The last radial norm reserve
is the source's exact 543/1750000>0.

Both full b ranges are impossible under the contrary premise.
This establishes the whole local a-H>11/10 theorem.

## 4. Independent exact arithmetic and polynomial reconstruction

A fresh standalone Fraction implementation, separate from any
author script, reproduced every coefficient of the three displayed
pressure polynomials from their squared factorizations. The useful
independently recomputed reserves include:

| Check | Exact result |
| --- | ---: |
| Height Cauchy reserve | 191/25600 |
| Height quadratic discriminant reserve | 3911/1440000 |
| Height polynomial quadratic reserve above 11/50 | 802103/200000000 |
| Height final radius-endpoint reserve | 3/280 |
| T, b>=1, retained quadratic coefficient | 143471/6890625 |
| T, b<=1, retained linear coefficient | 530557/15625000 |
| T, b>=1, radial norm reserve | 61/10000 |
| T, b<=1, radial norm reserve | 543/1750000 |
| A comparison for a>47/28 | 47/19600 |
| A comparison for r_0>29/28 | 661/122500 |
| A final endpoint reserve | 1/560 |
| Q(8/5,7/6) | 1/15 |

The auxiliary script is /tmp/review_c6_ta_block.py. It is an
independent arithmetic check, not a premise or a replacement for
the displayed continuum proofs.

## 5. Original physical join and scope

Both local endpoint inequalities use the same original R and
the same actual return height H. Thus the exact original reserve
m+(a-1)=1 contradicts

\[
           m+a-1=(m+H)+(a-H)-1>9/10+11/10-1=1.
\]

The scalar comparisons in H, b and angle do not move a physical
body, replace a mean, change a normal, or equate the radial weights.
The endpoint mean already at the adjacent A vertex and every
genuine return mean at T remain included. The contradiction is
in the original six-body core, with all three extras still present.

This accepts the complete stated all-strict-turn A/T family.
The source correctly leaves A/O and every lower-turn owner
placement explicit, and makes no unrestricted one-radial or global
nine-square gate claim.
