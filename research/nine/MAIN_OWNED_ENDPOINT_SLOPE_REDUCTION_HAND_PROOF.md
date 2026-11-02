# Eliminate every main-owned endpoint slope at a fixed multiplier

This hand proof removes an endpoint-normal parameter from the joint support
bound. It is valid for every sign and magnitude of the central separator
and retains the original shoulder center and orientation. Its multiplier
conditions in Sections1--4 are explicit: use k=207/16 on this endpoint
edge and use no endpoint-height shift on its main square. Section5
extends the comparison to every constant multiplier207/16<=k<=20,
with the unboxed endpoint bound specified there. No Lean, Lake, or CI
is used.

Put

    Q=1105/256, r=sqrt(Q), a=46, K=207/16.

Work in the right-hand frame; horizontal reflection gives the left case.
Let E own the physical endpoint-to-shoulder normal `n=(-w,1)`, with
`|w|<=1/14`. Let S be its original shoulder, with

    23/30<=x_S<=13/12.

Its physical halfwidth satisfies `h_S<=1/sqrt(2)<71/100`.
Keep the center and physical frame of S fixed in the following scalar
comparison. Set

    d=sqrt(1+w^2),
    A(w)=sqrt((a+Kw)^2+K^2),
    P_E(w)=a h_E+H_E(a e_x-Kn)+K H_E(n),

where E's frame is fixed by its ownership of n. Define

    F(w)=r A(w)-P_E(w)+K n dot c_S-K H_S(n).          (1)

Any central-edge or central-floor terms in the joint bound are independent
of w here. They may therefore be added to both sides of the comparison.
We prove

    F(w)<=F(0)-(2047/11200)|w|                       (2)

throughout the stated interval. The positive side has the stronger margin
`(2053/160)w`. This is a scalar upper-bound comparison; intermediate w
values need not describe physical packings.

## 1. The exact main-square penalty

Use E's orthonormal side frame `((1,w)/d,(-w,1)/d)`. The projection of
`a e_x-Kn` on its second axis is `-aw/d-Kd`, which stays negative:
`a|w|<=a/14<K<=Kd^2`. Its first projection is a/d. Consequently

    P_E(w)=a(1+w)/d+Kd       for w>=0,
    P_E(w)=a/d+Kd           for w<=0.                (3)

For the first branch,

    P_E'(w)=a(1-w)/d^3+Kw/d.

Since `1-w>=13/14` and `d<201/200`, this gives

    P_E'(w)> (13/14)46(200/201)^3 >40.              (4)

The last two comparisons are rational after squaring and clearing
positive denominators.

For the negative branch,

    P_E'(w)=(-w)(a/d^3-K/d)<=(a-K)/14.              (5)

Indeed `a/d^3-K/d` decreases as d increases on this interval: its
derivative has numerator `-3a+Kd^2<0`. Its value is therefore at most
a-K, proving (5).

## 2. The original shoulder supplies a directional derivative bound

Centered support is Lipschitz in its vector argument. Since n'=(-1,0),
every one-sided derivative of H_S(n(w)) belongs to[-h_S,h_S]. Therefore

    -K(x_S+h_S)
      <= d/dw [K n dot c_S-K H_S(n)]
      <= -K(x_S-h_S).                              (6)

In particular the right side is negative, since `x_S>=23/30>71/100>h_S`.
The left side is greater than `-K(13/12+71/100)`.

No physical normal owner or prescribed orientation is assumed for S.
These derivative inequalities hold across support kinks by integration.

## 3. Both signs move the upper bound toward w=0

For w>=0,

    r A'(w)=rK(a+Kw)/A(w)<=rK<(21/10)K.

Combine this with (4) and the negative upper bound in (6):

    F'(w)<(21/10)K-40=-2053/160.                    (7)

For w<=0, put `x0=a-K/14=10097/224`. The function
`x/sqrt(x^2+K^2)` increases for positive x, and `a+Kw>=x0`. The exact
squared comparison

    Q*x0^2 > (199/100)^2*(x0^2+K^2)

shows

    r A'(w)>(199/100)K.                             (8)

Using (5) and the lower bound in (6) now gives

    F'(w)>(199/100)K-(a-K)/14-K(13/12+71/100)
          =2047/11200>0.                           (9)

Integrating (7) and (9) from w to zero proves (2), including both boundary
values and w=0.

## 4. Application to the joint certificate

In the original joint dual, choose k=K and q_E=0 on every edge whose main
square owns n. Before bounding the shoulder center by its circle or box,
all terms involving this w are exactly (1). The central multiplier, its
separator, the original central square, and every other endpoint remain
fixed. Thus (2) replaces this one w by zero with a nonnegative explicit
reserve. This may be done successively at both endpoints.

At w=0 the main-square part is the exact constant

    r A(0)-P_E(0)=23Q-a-K.

Its disk-support maximizer has aligned center `(3/2,-1/16)` in the right
frame, and lies inside the original endpoint center box. Thus using the
known-frame center support and its box at this reduced endpoint does not
secretly improve the constant: the unboxed maximum is already attained
inside that box. The analogous left center is `(-3/2,-1/16)`.

Accordingly a reduced EE certificate needs only the two central slopes,
with both endpoint multipliers fixed to K and both endpoint-height shifts
zero. A reduced RE certificate needs the shoulder-owned endpoint slope
and both central slopes, with k=K and q_E=0 only on its main-owned edge.
The other nonnegative multipliers may be chosen independently for each
reduced parameter box. The remaining finite reduced tables still have to
be proved; this parameter reduction does not itself claim their closure.

If the original containing radius is strictly below r, the initial main
disk-support replacement is strict because A(w)>0. Hence the reduction
preserves the strict-radius conclusion of a completed reduced table.

## 5. A uniform interval of admissible endpoint multipliers

The monotonicity comparison also holds for every fixed

    K<=k<=20, q_E=0.                              (10)

Replace K by this k in A,P_E,F and in the shoulder term in(1). The
projection signs used to obtain(3) stay valid, since a/14<K<=k.
The exact penalty is consequently

    P_E(w)=a(1+w_+)/sqrt(1+w^2)+k sqrt(1+w^2).

For w>=0 one has the sharper lower bound P_E'(w)>42. Squaring the
positive quantities reduces this to the rational reserve

    a^2(13/14)^2-42^2(197/196)^3
       =1282027/38416>0.

At the same time rA'(w)<(21/10)k<=42, and the shoulder derivative is
strictly negative by(6). Thus F'(w)<0 on the entire positive half.

For w<=0, the penalty derivative satisfies

    P_E'(w)<=(46-k)/14.

This follows just as in(5): the derivative of a/d^3-k/d with respect
to d has numerator -3a+kd^2<0 on the stated domain. The shoulder
derivative is greater than -(269/150)k. It remains to lower-bound

    r(a+kw)/sqrt((a+kw)^2+k^2).

For fixed k this ratio is smallest at w=-1/14. At that w it decreases
as k increases, because k/(a-k/14) increases. Therefore the following
finite rational table proves the required bound throughout each row.
The fourth column is

    Q(46-u/14)^2-c^2[(46-u/14)^2+u^2],

where u is the upper endpoint of the k interval. The last column is
the lower bound for k(c-269/150)-(46-k)/14, attained at that interval's
lower endpoint. Both columns are strictly positive.

| k interval | c | Ratio lower bound | Positive squared reserve | Positive derivative reserve |
|---|---:|---|---:|---:|
| [207/16,14] | 99/50 | ratio>c | 5362281/160000 | 299/5600 |
| [14,15] | 197/100 | ratio>c | 185030121/31360000 | 197/1050 |
| [15,16] | 39/20 | ratio>c | 950573/15680 | 19/140 |
| [16,17] | 97/50 | ratio>c | 662209577/31360000 | 107/525 |
| [17,18] | 48/25 | ratio>c | 102265469/1568000 | 43/525 |
| [18,19] | 191/100 | ratio>c | 469146449/31360000 | 1/10 |
| [19,20] | 379/200 | ratio>c | 142139/30625 | 13/4200 |

It follows that F'(w)>0 throughout the negative half. Integration gives

    F(w)<=F(0),                                  (11)

strictly for w!=0, for every k in(10). Every actual shoulder variable
and every central term remains fixed during this comparison.

### The endpoint constant in the variable-k reduction

For(10), the correct reduced endpoint bound is the unboxed constant

    E_0(k)=r sqrt(a^2+k^2)-a-k.                   (12)

Thus the one-sided outer expression after eliminating an E-owned slope
is bounded by

    E_0(k)+(b(1,z)+k e_y) dot c_S
               -bH_S((1,z))-k h_S.

This keeps the original shoulder center and frame. The shoulder may
subsequently be bounded by its original circle and box constraints.

At k=K the endpoint maximizer from Section4 lies in the endpoint box.
For other k in(10) that assertion need not hold. Therefore a variable-k
table must retain(12); replacing it by a smaller boxed endpoint maximum
would not follow from(11). Its independent checker must enforce
K<=k<=20, q_E=0, and the unboxed expression(12) on every finite row.

The complete multiplier-range argument and every displayed rational
reserve have been independently hand-audited. The scalar-envelope tables
to which it is applied remain separate finite proof obligations.
