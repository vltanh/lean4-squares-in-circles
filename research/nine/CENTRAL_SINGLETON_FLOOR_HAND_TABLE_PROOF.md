# A central singleton opposite two central units has high whole floor

This is a physical actual-four caller lemma. A complete 4512-leaf exact
scalar cover has passed independent replay, as recorded at the end.
No Lean or CI is used. Numerical exploration suggested the reductions,
but no numerical optimizer result is a premise of the proof.

Put

    Q=1105/256, rho=sqrt(Q-1/4)-1/2,
    l=29/60, g0=15/31, delta=331/20000,
    A=27/200, B=2g0-1/10=269/310,
    c=B-9/20=259/620, epsilon=1/1000.

## 1. Statement

Retain four original squares forming an actual horizontal four-chain
`M0<M1<M2<M3` in the centered closed Q-disk. Every additional square is
an original independently oriented physical unit, and all open interiors
are pairwise disjoint. A central outsider means `|x|<=l`.

**Theorem.** If a central outsider F is above both inner main centers and
has whole floor `y_F-h_F<=1/10`, there cannot be two distinct central
outsiders G,H below both inner main centers.

**Reflected corollary.** If three central outsiders have two above both
inner mains and one below both, the singleton below has whole upper edge
strictly below `-1/10`. With two below and one above, the singleton above
has whole floor strictly greater than `1/10`.

The theorem includes the closed Q-disk and all touching boundaries. It
does not assert that three central outsiders cannot all be above the
mains: there are physical seven-square controls of that kind.

## 2. Main inset bounds and a complete clearance formula

The actual-four bounds give

    -31/60<x1<-29/60, 29/60<x2<31/60,
    1/2<=h_i<31/60, g_i=1/(4h_i)>g0,

and the aligned square of halfwidth g_i centered at M_i is contained in
that original main square. There is also the useful coupled bound

    x1+g1>-delta,  x2-g2<delta.                    (1)

Indeed `x2+h2<=x3-h3<rho-1/2`, and `h2+g2>=1`, so
`x2-g2<rho-3/2`. The left inequality is reflected. The rational bound
`rho-3/2<delta` follows from

    (2+delta)^2-(Q-1/4)=27061/400000000>0.

For a physical unit, write the absolute side components as

    a=1/sqrt(1+t^2), b=t/sqrt(1+t^2), 0<=t<=1,
    h=(a+b)/2, k=(a-b)/2.

Let its center be vertically above an aligned main inset of halfwidth g.
If the horizontal center gap is d and `d-g<1/2`, the horizontal center
chords have common interior projection, because the unit contains its
centered half-unit disk. Their vertical order therefore persists over
their common projection, as in the adjacent-proxy barrier proof. Thus
the unit is above the upper boundary of the inset/unit Minkowski sum;
the below-side facet possibilities are not silently discarded.

The main vertical facet and the two possible unit facet slopes give the
necessary center clearance

    vertical gap >= g+h-L(s,t),  s>=d-g,

where, for `t>0`,

    L(s,t)=max(0,t(k+s),(s-k)/t).                  (2)

Both chiralities are allowed: choosing the favorable horizontal sign of
each facet only weakens the lower bound. A horizontal separating facet
is impossible because `d<g+1/2<=g+h`. Formula (2) follows directly from
the three upper facet thresholds

    g+h,
    g+h-t(k+d-g),
    g+h-(d-g-k)/t.

At `t=0`, the clearance is `g+1/2`, so define `L(s,0)=0` for `s<1/2`.

For a central coordinate x, (1) gives the common, orientation-complete
loss bounds

    L_left(x,t)=L(x+delta,t),
    L_right(x,t)=L(-x+delta,t).                   (3)

They are valid for the original left and right inner main respectively.
Here `|x|+delta<=l+delta=1/2-7/60000<1/2`, which justifies every preceding
horizontal-overlap and zero-slope clause. The reflected lower clearance
uses the identical functions.

## 3. A small loss on the unit's own half-plane

If `x>=0`, the right loss is exactly bounded by

    L_right(x,t)=max(0,t(k+delta-x))<=A.           (4)

To verify that the steep term cannot exceed the shallow term, for
`0<t<1` their difference has the sign of

    (delta-x)(1-t^2)-k(1+t^2).

It is nonpositive because
`k(1+t^2)/(1-t^2)=sqrt(1+t^2)/(2(1+t))=1/(4h)>delta`.
At t=1 they agree; t=0 was treated above. Finally `k<=(1-t)/2` gives

    t(k+delta)<=t((1-t)/2+delta)
                   <=(1/2+delta)^2/2<A,

with exact reserve `1270439/800000000>0`. The left own-half-plane
statement is reflected.

Reflect horizontally so `x_F>=0`. If F has whole floor at most 1/10,
(2)--(4) imply

    y2 <=1/10-g2+A.

Every central unit below M2 has vertical center gap greater than g2:
its centered half-unit disk must avoid the main inset, while its
horizontal distance to that inset is strictly less than 1/2 by (1).
Thus every central G or H below both mains has reflected height

    Y=-y >2g0-1/10-A=B-A>3/5.                    (5)

The exact reserve in the last comparison is `823/6200`.

The upper-column theorem now applies to the two reflected lower squares.
Their horizontal distance is strictly greater than l. They cannot both
have nonnegative x or both have nonpositive x, because either half of the
central strip has width l. Neither may lie on x=0. Label them so

    x_G=-v<0<x_H=w,  0<v,w<=l,  v+w>l.

F and H lie in the same closed half-plane. Applying the two opposite
vertical clearances through M2 and adding gives

    Y_H-h_H >= B-L_right(x_F,t_F)-L_right(w,t_H)
              >=B-2A>9/20.                      (6)

The last reserve is `229/1550`. The ordered theorem in
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md` says that a central unit
with whole floor at least 9/20 cannot have a central unit with a higher
or equal center in the Q-disk. Therefore

    Y_H>Y_G,  Y_G-h_G<9/20.                       (7)

## 4. Eliminate the original F completely

Write its two losses as `p=L_left(x_F,t_F)` and
`r=L_right(x_F,t_F)`. For the reflected opposite-half unit G, write
`q=L_left(-v,t_G)` and `s=L_right(-v,t_G)`; q is its own-half loss, so
`q<=A`. Adding the F/G clearances through each original main gives

    Y_G-h_G >= B-min(p+q,r+s).

By (7), `min(p+q,r+s)>c`. In particular

    p>c-A.                                       (8)

We claim the much stronger estimate

    r<epsilon=1/1000.                            (9)

There is nothing to prove if r=0. Otherwise (4) gives
`r=t_F(k_F+delta-x_F)`, with `t_F>0`. Substitute
`x_F=k_F+delta-r/t_F` into the two far-loss terms:

    p=max(0,2t_F(k_F+delta)-r,
                    2delta/t_F-r/t_F^2).

The shallow term is at most `2A-r<=2A<c-A`; the exact reserve is
`c-3A=79/6200`. The other term is at most `delta^2/r`, by completing
the square in `1/t_F`. Inequality (8) therefore forces

    r<delta^2/(c-A)<1/1000,

where the final exact comparison is

    c-A-1000delta^2=109609/12400000>0.

No parameter of F remains in what follows. Put `B0=B-epsilon`. For G
and H we have the simultaneous whole-floor lower bounds

    Y_G-h_G >= B0-L(v+delta,t_G)=f_G,
    Y_H-h_H >= B0-max(0,t_H(k_H-w+delta))=f_H.     (10)

The loss in the first line retains all three terms of (2); the second
line uses the proved own-half formula. In particular the original F,
both independent main insets and both below units have supplied (10).
They have not been replaced by a hypothetical common-frame packing.

## 5. The small t_G interval is excluded by hand

Suppose `0<t_G<=1/1000`. Put `d=sqrt(1+t_G^2)` and
`eta=7/60000`. Since `v+delta<=1/2-eta`, the steep term can be written

    (v+delta-k_G)/t_G
       =(v+delta-1/2)/t_G+1/(2d)+t_G/(2d(d+1))
       <=-eta/t_G+1/2+t_G/4
       <=4603/12000.

The shallow term is at most `t_G<=1/1000`. Thus the full loss is at
most 4603/12000. Formula (10) then gives

    f_G>=B0-4603/12000>9/20,

with reserve `2467/74400>0`, contradicting (7). At t_G=0 the loss is
zero, with the same conclusion. It remains only to consider

    0<=v,w<=l,  1/1000<=t_G<=1,  0<=t_H<=1.      (11)

## 6. Original circle bounds and all pair separating axes

For any x>=0 and folded slope t, define h,k,a,b,d as in Section 2 and
the upper height function

    U_+(x,t)=min(sqrt(Q-(x+k)^2)-h,
                 sqrt(Q-(x+h)^2)+k),
    U_-(x,t)=min(sqrt(Q-(x-k)^2)-h,
                 sqrt(Q-(x+h)^2)-k),
    U(x,t)=min(rho,max(U_+(x,t),U_-(x,t))).         (12)

Every contained physical unit at positive center height Y and horizontal
center magnitude x satisfies `Y<=U(x,t)`. For one chirality its actual
corners include `(x+k,Y+h)` and `(x+h,Y-k)`, giving U_+. For the other
they include `(x-k,Y+h)` and `(x+h,Y+k)`, giving U_-. The maximum
retains both physical chiralities; the center-radius bound is independent.
All square-root arguments in (11) are strictly positive.

Let

    Y0=h_G+f_G, Z0=h_H+f_H,
    M_G=U(v,t_G), M_H=U(w,t_H),
    D=v+w, V=max(0,M_H-Y0).

By (7), the actual positive vertical center gap is at most V. The folded
relative angle of the two actual square frames is at least
`|atan(t_G)-atan(t_H)|`: opposite chiralities give either the sum of the
absolute angles or its complement in pi/2, and both are at least their
difference. Thus their support sum in any owned unit normal is at least

    sigma=(1+(1+t_G t_H+|t_G-t_H|)/(d_G d_H))/2.    (13)

All four owned-axis scalar products with the center displacement are
bounded above, including every sign and chirality, by the four values

    a_G D+b_G V, b_G D+a_G V,
    a_H D+b_H V, b_H D+a_H V.

The separating-axis theorem therefore requires their maximum to be at
least sigma. No physical pair normal has been discarded.

Consequently every original counterexample must satisfy all six scalar
necessary inequalities

    9/20-f_G>=0,
    M_G-Y0>=0,
    M_H-Z0>=0,
    M_H-Y0>=0,
    D-l>=0,
    max(a_G D+b_G V,b_G D+a_G V,
        a_H D+b_H V,b_H D+a_H V)-sigma>=0.        (14)

The variables in (11) exhaust their entire domain.

## 7. The complete four-variable exact cover

`central_singleton_floor_cover.json` is a full exact midpoint partition
of the one closed rational root

    [0,29/60] x [0,29/60] x [1/1000,1] x [0,1].

Its 9023 nodes contain 4512 strict leaves and no unresolved node.
At every leaf, the minimum of the six expressions in (14) has a strictly
negative rational interval upper bound. Thus at least one necessary
inequality fails everywhere in the root.

`certify_central_singleton_floor.py` constructs this cover with outward
96-bit dyadics and integer square roots. The independent checker
`verify_central_singleton_floor.py` imports no producer or discovery code;
it reconstructs (10)--(14), the exact root, every midpoint split and
every strict leaf using the separately audited 64-bit dyadic arithmetic
kernel. It ignores the producer's claimed upper bounds.

Each evaluator combines direct interval evaluation with a centered
mean-value enclosure. At min, max and absolute-value branch changes,
the derivative hull includes every branch that can be active. All radical
and division denominators are strictly positive in (11). Integrating
these enclosures along segments validates the centered bounds through
branch changes. Section 5, not a numerical convention for division by
zero, covers the omitted small-angle interval.

The complete independent dyadic replay passed all 4512 strict leaves,
with maximum tree depth 35 and largest replayed upper bound

    -767457591586915/18446744073709551616<0.

The certificate SHA-256 is

    9dd295e9755acfa9087736752fd8d33d4b1c52604fcfd41a43952bb56a0639f9.

A separate agent reviewed the complete original-square reduction,
including the center-chord order, every inset facet, the coupled bound
delta, all seven displayed exact reserves, the own-half loss estimate,
the elimination of F, the small-slope boundary, both circle chiralities
and all pair separator owners. That analytic audit passed. The same
agent also completed a second arithmetic replay through the independent
Fraction kernel. All 9023 nodes and 4512 strict leaves passed; the largest
Fraction upper bound was

    -32176225981534223778098014939238314646094854978207436467
      /773393360787276245866461151706387410748946136073554956475750 < 0.

That second replay uses a different arithmetic implementation with the
same reviewed structural formulas. It is recorded in
`central_singleton_floor_cover_fraction_replay.json`. These are agent
reviews and exact arithmetic replays, not human or proof-kernel checks.

Therefore (14) is impossible, contradicting the
assumed two central units below a bad-floor F. This proves the theorem
and the reflected singleton-floor corollaries in Section 1.
