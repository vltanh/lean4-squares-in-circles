# An analytic lower bound activating the contact-moment theorem

**Status.** Complete pen-and-paper proof that eight interior-disjoint unit
squares cannot fit in a disk of radius

    R_0 = sqrt(2)+1/2.

Consequently the minimum eight-square radius satisfies

    R_8 > sqrt(2)+1/2.                                  (1)

The proof uses the analytic central-square theorem in
`HUMAN_GLOBAL_GEOMETRY_CLOSURE.md`; it does not use the earlier lower-bound,
central-core, or marker certificates. In particular, (1) makes the strict
lower endpoint in the contact-moment theorem of
`HUMAN_CONTACT_EQUILIBRIUM.md` available analytically for an eight-square
minimizer. It is still weaker than the conjectured sharp radius.

The argument uses one auxiliary circle in each of two cases. Its radius is
chosen from the depth of the origin inside the central square. As in the
central-square theorem, `L_r(S)` denotes the total angular measure of the
intersection of a square S with the circle of radius r about zero.

## 1. Canonical exterior states and constants

Put

    Q_0 = R_0^2 = 9/4+sqrt(2),
    d   = 1/12,
    r_- = 11/12,
    r_+ = 13/12,
    k   = sqrt(Q_0/2)-1 = sqrt(2)/4,
    b   = sqrt(Q_0-1/4)-1 = sqrt(2+sqrt(2))-1,
    x_0 = sqrt(Q_0-1)-1.

An exterior square means a unit square whose open interior avoids zero.
By choosing signed square axes, every exterior square in `D_(R_0)` has
the canonical form

    S=[x,x+1] times [y,y+1],
    x>=0,  -1/2<=y<=x,
    (x+1)^2+(y+1)^2<=Q_0.                               (2)

Here `x<=b`, and if `y>=0` then `y<=k`.

We will use the elementary strict bounds

    R_0-1 < 11/12,
    b < 17/20,
    x_0 < 2/3,
    x_0 < 11/(12 sqrt(2)).                              (3)

The first follows from `sqrt(2)<17/12`. For the second,

    2+sqrt(2) < 41/12 < (37/20)^2.

For the third, `Q_0-1=5/4+sqrt(2)<11/4<25/9`.
For the last, subtracting the relevant squares gives

    (1+11/(12 sqrt(2)))^2-(Q_0-1)
      = 49/288-sqrt(2)/12 > 13/288 > 0,

where `sqrt(2)<3/2` was used. All quantities being squared are positive.

## 2. Extend the angular monotonicity below radius one

Let `R=R_0`, `Q=Q_0`, and `r>=11/12`. The factorization used in the
central-square theorem remains positive even when r is below one.

For `X>=Y>0`, `X^2+Y^2=Q`, set `s=X+Y` and

    P_r(z)=z^2(r^2-(z-1)^2).

Direct subtraction gives

    P_r(X)-P_r(Y)
      = (X-Y)[s^2-(Q+1-r^2)s+Q].                       (4)

The bracket has the useful expression

    s^2-(Q+1-r^2)s+Q
      = (s-R)^2+[r^2-(R-1)^2]s > 0.                  (5)

Indeed `r>=11/12>R-1` by (3), and `s>0`.

Exactly as in the proof of the central-square theorem, differentiation
and comparison of positive squares now give the following two facts:

* For `0<=t<=1/2`, the function

      acos((sqrt(Q-(1-t)^2)-1)/r)+asin(t/r)

  is strictly increasing. Therefore every state (2) with `y=-t` satisfies

      acos(x/r)+asin(t/r) >= acos(x_0/r).               (6)

* For `0<=y<=k`, the function

      asin((sqrt(Q-(1+y)^2)-1)/r)+asin(y/r)

  increases up to `y=k`, where its two coordinates are equal. Therefore
  every state (2) with `y>=0` satisfies

      asin(x/r)+asin(y/r) <= 2asin(k/r).                (7)

For completeness, both derivatives have the form

    1/sqrt(r^2-(Y-1)^2)
      -Y/[X sqrt(r^2-(X-1)^2)].                        (8)

Their positivity for `X>Y` is equivalent to `P_r(X)>P_r(Y)`.
All denominators are positive: `X-1<=b<17/20<11/12<=r`, and
`|Y-1|<=1/2<r`. The corner derivative is zero only at `X=Y`.

## 3. A uniform arc bound for radii between 11/12 and one

**Small-circle lemma.** Every exterior square S in `D_(R_0)` satisfies

    L_r(S) > 3/4       whenever 11/12<=r<=1.            (9)

Use the canonical state (2). If `y>=0`, the two far sides of S have
coordinates at least one, so neither cuts the open circle of radius r.
The first-quadrant arc has length

    L_r = pi/2-asin(x/r)-asin(y/r)
        >= pi/2-2asin(k/r).                            (10)

Now `k/r<=3sqrt(2)/11<sin(2/5)`. The latter strict comparison follows from

    sin(2/5) >= 146/375 > 3sqrt(2)/11,
    146^2*121=2579236 > 2531250=18*375^2.

Thus (10) is strictly greater than `pi/2-4/5>3/4`.

If `y=-t`, `0<=t<=1/2`, put

    A=acos(x/r),
    B=asin(min(1,(1-t)/r)),
    C=asin(t/r).

The far vertical side does not cut the circle, since `x+1>=1>=r`.
The intersection is the arc from `-min(A,C)` to `min(A,B)`, so

    L_r=min(A,B)+min(A,C).                             (11)

We have `B>=C`. There are three cases, including their common endpoints.

* If `A>=B`, then `L_r=B+C>=pi/3`. To see this, a clipped B equals
  `pi/2`; otherwise convexity of asin gives
  `B+C>=2asin(1/(2r))>=pi/3`.

* If `C<=A<=B`, then (6) and (3) give

      L_r=A+C>=acos(x_0/r)>pi/4>3/4.

* If `A<=C`, then `L_r=2A`. By (3),

      x/r <= b/r < 51/55 < 119/128
          <= cos(3/8).

  The final inequality is `cos z>=1-z^2/2` at `z=3/8`, and
  `51*128=6528<6545=119*55`. Hence `A>3/8`, giving `L_r>3/4`.

This proves (9). The elementary bounds on pi used here and below can all
be replaced by `157/50<pi<22/7`.

## 4. A larger-circle bound for squares avoiding a small central disk

Define

    z = 3sqrt(2)/13 = k/r_+,
    K = pi/2-2asin(z).

We will prove:

**Large-circle lemma.** If S is an exterior unit square in `D_(R_0)` and
every point of S has distance at least `1/12` from zero, then

    L_(13/12)(S) >= K > 2pi/7.                         (12)

First, the strict comparison with `2pi/7` is elementary. Since

    sin(1/3) >= 53/162 > 3sqrt(2)/13,
    53^2*169=474721 > 472392=18*162^2,

we have `asin(z)<1/3`. Consequently

    K > pi/2-2/3 > 2pi/7,                             (13)

the final inequality being equivalent to `pi>28/9`.

For the arc estimates it is convenient to record

    cos(K)=2z sqrt(1-z^2)=6sqrt(302)/169,
    0<K<pi/3.                                        (14)

For the upper bound in (14), `cos(K)>1/2` follows after squaring from
`4*10872>28561`.

### 4.1 Straddling states

Suppose `y=-t`, `0<=t<=1/2`. The nearest point of S to zero has distance
x, so the avoidance assumption gives `x>=d=1/12`. In particular
`x+1>=r_+`; the far vertical side does not cut the circle.
Use (11), now with `r=r_+`, and

    B=asin((1-t)/r_+),   C=asin(t/r_+).

There is no clipping because `1-t<=1<r_+`.

* If `A>=B`, then

      L_r=B+C>=2asin(6/13)>K.

  For the strict comparison, the cosine of the displayed lower bound is
  `97/169`, whereas `cos(K)=6sqrt(302)/169`, and
  `97^2=9409<10872=36*302`. Both angles lie in `[0,pi]`.

* If `C<=A<=B`, then (6) and `x_0<2/3` give

      L_r>=acos(x_0/r)>acos(8/13)>K.

  The last comparison follows from
  `8/13=104/169<6sqrt(302)/169`, since `104^2=10816<10872`.

* If `A<=C`, then

      L_r=2A>=2acos(b/r)>pi/3>K.

  Indeed `b/r<51/65<sqrt(3)/2` by (3).

### 4.2 First-quadrant states with x>=1/12

Suppose `y>=0` and `x>=d`. Again the far vertical side does not cut the
circle. If `y>=d`, neither far side cuts it, and (7) gives

    L_r=G:=pi/2-asin(x/r)-asin(y/r)>=K.                 (15)

If `0<=y<d`, the far horizontal side can also cut the arc. Its length is
the minimum of G and

    H_y=asin((y+1)/r)-asin(y/r).

On this interval `H_y` increases with y, and hence

    H_y>=asin(1/r)=asin(12/13)>pi/3>K.                  (16)

The strict trigonometric comparison follows from
`(12/13)^2>3/4`.

### 4.3 First-quadrant states with x<1/12

It remains to consider `0<=y<=x<d`. Both far sides can now cut the
circle. Its intersection lies in the first quadrant, with endpoints

    lower=max(asin(y/r),acos((x+1)/r)),
    upper=min(acos(x/r),asin((y+1)/r)).

Subtracting shows that the arc length is the minimum of four quantities,
provided they are positive:

    G   = pi/2-asin(x/r)-asin(y/r),
    H_x = asin((x+1)/r)-asin(x/r),
    H_y = asin((y+1)/r)-asin(y/r),
    J   = asin((x+1)/r)+asin((y+1)/r)-pi/2.             (17)

The first is at least K by (7). Both H terms exceed K by (16) and its
x analogue. Finally the nearest point of this square is `(x,y)`, so

    x^2+y^2>=d^2,       x+y>=d.

Convexity and monotonicity of asin give

    J >= 2asin((1+d/2)/r)-pi/2
      = 2asin(25/26)-pi/2 > K.                        (18)

The last inequality follows from

    (25/26)^2=625/676 > 604/676=1-z^2,

which implies `asin(25/26)>acos(z)=pi/2-asin(z)`.
Thus all four quantities in (17) are positive and at least K, proving
the asserted arc formula and completing the proof of (12).

## 5. Apply the lemmas to a hypothetical eight-square packing

Suppose eight interior-disjoint unit squares fit in `D_(R_0)`. Because
`Q_0<98/25`, the analytic theorem in
`HUMAN_GLOBAL_GEOMETRY_CLOSURE.md` supplies a unique square C containing
zero in its open interior.

Choose its signed axes so that its center has coordinates `(a,u)` with

    0<=u<=a<1/2,
    delta=1/2-a>0.

The open disk of radius delta about zero lies in the open square C.
Every other closed square avoids this open disk. Indeed, a point of such
a square inside the open disk would, by approximation from that square's
interior, give an interior overlap with C. Thus all seven exterior squares
have nearest distance at least delta.

### Case 1: delta>=1/12

Apply the large-circle lemma to all seven exterior squares. Their total
angular measure on the circle of radius `13/12` is at least

    7K > 2pi,

which is impossible for interior-disjoint squares.

### Case 2: 0<delta<=1/12

Choose the auxiliary radius

    r=1-delta=a+1/2,       11/12<=r<1.

In its own frame the central square is

    C=[-delta,r] times [u-1/2,u+1/2].

Already in the right semicircle it occupies an arc of length

    asin(min(1,(1/2+u)/r))+asin((1/2-u)/r) >= pi/3.     (19)

If the first asin is clipped, it equals `pi/2`; otherwise convexity of
asin bounds the sum below by `2asin(1/(2r))>=pi/3`.
The far right side is exactly tangent to the auxiliary circle, and the
left side does not cut this right-semicircle arc, so (19) counts actual
points of C. Any additional arcs only increase its total measure.

Every one of the seven exterior squares has angular measure greater than
`3/4` by the small-circle lemma. Consequently all eight squares occupy
total angular measure strictly greater than

    pi/3+7*(3/4) = pi/3+21/4 > 2pi.                   (20)

The last inequality follows from `pi<22/7<63/20`.

For either auxiliary circle, interior-disjoint squares have intersections
with disjoint relative arc interiors, except possibly finitely many points
where a circle meets square sides. Thus their total angular measure is
at most `2pi`, contradicting both cases. The two cases include their common
endpoint and exhaust all possible central squares. This proves (1).

## 6. Consequence and remaining scope

The radius interval required by the physical contact-moment theorem is
now analytical for any eight-square minimizer whose radius is below two:

    sqrt(2)+1/2 < R_8 < 2.

Such a minimizer has a force-bearing component with nonzero contact-moment
circulation, and hence a positive-stress cycle, by
`HUMAN_CONTACT_EQUILIBRIUM.md`. Its proof no longer needs the earlier
computational inequality `R_8^2>19/5` for this purpose.

Neither this lower bound nor the cycle conclusion forces the candidate's
interior twin pair or five-corner projected polygon. The unrestricted sharp
packing inequality is still the remaining global problem.
