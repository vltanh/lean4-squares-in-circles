# Two smaller central disks already force capacity at most eight

Date: October 27, 2026.

**Status: complete force-free hand theorem, submitted for full root and
separate independent review.** The proof counts actual open-interior
arc measure. It retains a weak-clearance endpoint at which a square's
arc can have one missing interior point; it does not claim a connected
arc or an interior radial-center point at that endpoint.

## 1. The two complete physical statements

Let all actual unit squares be contained in the disk about the original
origin, with disjoint open interiors. Either of the following two
hypotheses makes nine actual units impossible:

| Containing-circle bound | One actual unit contains the closed central disk |
| --- | --- |
| `R^2<=1105/256` | radius `23/100` |
| `R^2<=17/4` | radius `1/5` |

All other unit orientations and positions are arbitrary. No circle
contact, load, force, graph, contact owner or positive certificate is
assumed in this theorem. In particular all original completion units
remain. The result does not assert the false unrestricted radius-Q
claim with a central disk of radius `1/5`.

It suffices to prove this arc statement in each row. Write respectively

    (Q_0,h,rho)=(1105/256,23/100,123/100),
    (Q_0,h,rho)=(17/4,1/5,6/5).

If an actual unit `E` is contained in `D_(sqrt(Q_0))` and
`dist(O,E)>=h`, then the angular measure of

    int(E) intersect {|p|=rho}

is strictly greater than `pi/4`. The use of measure, rather than a
connected-arc assertion, is essential only at the explicit endpoint
in Section 4.1.

## 2. Exact own coordinates and a uniform inner-face inequality

Choose signs and order of the actual unit's own axes so its center
coordinates satisfy `x>=y>=0`. Put

    a=x+1/2, b=y+1/2, A=a−1, B=b−1,
    E=[A,a] times [B,b],
    a>=b>=1/2,       q=a^2+b^2<=Q_0.

The nearest-point distance is

    max(A,0)^2+max(B,0)^2>=h^2.                         (1)

First suppose `a>rho`, so `A>h>=1/5`. The same elementary
own-coordinate bounds used in
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`, Section 1.1, give

    A<41/40,       −1/2<=B<1/2,
    A^2+B^2<2081/1600<36/25<=rho^2.                   (2)

Define

    E_0=A^2+B^2+sqrt(2) A B.

We prove, with strict reserve in each row,

    E_0<rho^2/2.                                      (3)

At fixed `q`, put `t=a+b`. Direct expansion gives

    E_0=(1−1/sqrt(2))q+t^2/sqrt(2)
             −(2+sqrt(2))t+2+sqrt(2).

This is convex in `t`. The full fixed-q domain `a>=b>=1/2`
has endpoint cases `b=1/2` and `a=b`; enlarging to those
endpoints is legitimate even if an endpoint fails `a>rho`.

At `b=1/2`, write `A_0=sqrt(q−1/4)−1`. The present
`q>rho^2+1/4` gives `A_0>h`. Since `1/sqrt(2)>7/10`,

    E_0<A_0^2+1/4−(7/10)A_0<=933/1600<18/25.

The quadratic is convex on the enlarged interval
`1/5<=A_0<=41/40`; its endpoint values are `3/20`
and `933/1600`. This proves (3) at this endpoint for both rows.

At `a=b=v`, one has

    E_0=(2+sqrt(2))(v−1)^2.

For the first row, enlarge to `3/4<=v<=147/100` and use
`sqrt(2)<99/70`. Then

    E_0<(239/70)(47/100)^2
          =527951/700000
          <15129/20000=rho^2/2,                       (4)

with exact reserve `1564/700000`. The endpoint `147/100`
is strictly above `sqrt(1105/512)`.

For the second row, enlarge instead to `3/4<=v<=35/24`.
Here `(35/24)^2>17/8`, and

    E_0<(239/70)(11/24)^2
          =28919/40320<18/25=rho^2/2.                (5)

The last reserve is `557/201600`. In both enlarged intervals
the larger absolute value of `v−1` is the upper endpoint's.
Convexity at fixed `q` now proves (3) throughout the actual
inner-face domain. No pose or orientation sampling is used.

## 3. The entire inner-face arc has measure greater than pi/4

Set

    alpha=arccos(A/rho),
    beta=arcsin(B/rho),
    gamma=arcsin(min(b/rho,1)).

Because `A>0`, `a>rho` and (2), the full open-interior
intersection is the open angle interval

    (beta,min(alpha,gamma)).

In particular the negative-x half-circle is ineligible, and (2)
ensures `beta>−alpha`. The original upper-face endpoint `b=rho`
introduces no extra isolated component.

Inequality (3) is equivalent to

    (sqrt(2)A+B)^2<rho^2−B^2.

It implies

    A<rho cos(beta+pi/4).

The relevant angle is in the strictly decreasing cosine interval,
since `|B|<=1/2` and `rho>=6/5` give `|beta|<pi/4`.
Thus `alpha−beta>pi/4`.

If `b<=rho`, the whole unit-strip estimate gives

    gamma−beta
      =arcsin(b/rho)−arcsin((b−1)/rho)
      >=2 arcsin(1/(2rho))
      >=2 arcsin(2/5)>pi/4.                            (6)

Its derivative is nonnegative for `b>=1/2`, and continuity
includes `b=rho`. If `b>rho`, then `gamma=pi/2` and
`beta<pi/4` give the same strict conclusion. Both candidate
interval lengths therefore exceed `pi/4`.

## 4. Every outer-face case, including the weak endpoint

Now suppose `a<=rho=1+h`, so `A<=h` and `B<=A`.

### 4.1. The full case B<=0

Equation (1) forces `A=h` exactly. Hence `a=rho` and
`1/2<=b<=1`. The relevant positive-x circle points with
`B<y<b` automatically satisfy `x>h`, because

    rho^2−1>h^2.

They also satisfy `x<rho`, except at the single point with
angle zero. Thus the entire open-interior circle set is

    (arcsin(B/rho),arcsin(b/rho)) minus {0}.

The zero point may be an endpoint rather than an interior point.
In either case its removal has zero angular measure. The total
measure of this set is at least the strip lower bound (6),
strictly greater than `pi/4`. This explicitly handles the
otherwise troublesome actual unit with its outer side tangent
to the chosen inner circle.

### 4.2. The full case B>0

Here

    0<B<=A<=h,       k^2=A^2+B^2>=h^2.

The closed circle interval has endpoints

    max(arccos(a/rho),arcsin(B/rho)),
    min(arccos(A/rho),arcsin(b/rho)).

Each of its four possible upper-minus-lower differences exceeds
`pi/4`. The two opposing-face differences have the strip bound
(6). The inner-inner difference is at least

    pi/2−2 arcsin(h/(1+h))
       >=pi/2−2 arcsin(1/5)>pi/4.                     (7)

For the outer-outer difference put

    L(A,B)=arcsin((1+A)/rho)+arcsin((1+B)/rho)−pi/2.

At fixed `k`, increase `A` from `k/sqrt(2)` to its actual
value, with `B=sqrt(k^2−A^2)`. Comparing the two positive
derivative terms and squaring shows that the derivative's sign
is the sign of

    (A−B)[(A+B−h)^2+(k^2−h^2)(A+B+1)].               (8)

This is nonnegative. The identity uses exactly `rho=1+h`;
it retains `k=h`. The entire comparison path has positive
`B` and `A<=h`. Continuity covers `A=h`, where a derivative
may be infinite. Consequently

    L(A,B)>=2 arcsin((1+k/sqrt(2))/(1+h))−pi/2
            >=2 arcsin((1+h/sqrt(2))/(1+h))−pi/2
            >=2 arcsin((4+1/sqrt(2))/5)−pi/2
            >pi/4.                                    (9)

The penultimate step uses `h<=1/4`: the displayed ratio
decreases with `h`. The last positive squared reserve against
`sin^2(3pi/8)` is `(16−9sqrt(2))/100>0`.
Thus all four endpoint differences are strictly positive by
more than `pi/4`, proving the desired open-arc measure bound.

Sections 3 and 4 cover every actual square orientation and every
weak-clearance endpoint.

## 5. Same-nine capacity and exact S-root consequences

Suppose one actual unit `H` contains the closed disk `D_h`.
Every other actual closed unit `E`, being interior-disjoint from
`H`, has `dist(O,E)>=h`. Indeed a point of `E` in the open
disk would be in `int(H)`, and an open neighborhood of a point
of a closed unit meets that unit's open interior. Such a point
would force interior overlap.

The other eight actual open unit interiors meet the chosen circle
in disjoint measurable sets. By the proved statement their eight
angular measures sum to more than `8(pi/4)=2pi`, impossible.
This proves both full physical capacity statements in Section 1.

For a genuine tilted S root in the actual own chart

    H=[U−1,U] times [V−1,V],
    U>=V>0,       U^2+V^2=d^2,
    2<R<=sqrt(1105)/16,

one has `d>14/15`. Therefore:

* If `U<=77/100`, then `V>23/100` and every own side is
  at distance at least `23/100` from the origin. The first
  capacity theorem excludes the whole same-nine configuration.
* If `R^2<=17/4` and `U<=4/5`, then `V>1/5` and every
  own side is at distance at least `1/5` from the origin.
  The second capacity theorem excludes the whole configuration.

For example the second lower bound follows from
`V^2>(14/15)^2−(4/5)^2=52/225>1/25`;
the first follows from the still stronger bound obtained by
replacing `4/5` with `77/100`. Also `U>=d/sqrt(2)>1/2`
in both cases. The upper side-distance bounds follow from
`V<=U`. Equalities `U=77/100` and `U=4/5` are retained by
the weak-clearance proof.

These are literal geometric root-domain consequences, not new
whole-cycle labels. When combined with a separately established
ordered true-S3 high-coordinate exclusion, they remove every
tilted root with `d<=1` and reduce the high tilted domain to
`77/100<U<=4/5`. Any aligned-root domain and all original
graph-specific routing or moment premises remain separate.

No metadata, remote state, original force or actual mean is changed.
No compilation, CI result or numerical configuration is a premise.
