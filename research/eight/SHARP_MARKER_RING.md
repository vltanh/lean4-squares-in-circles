# A sharper global ring reduction: every exterior gap lies below pi/3

This is an intermediate computer-assisted theorem for arbitrary packings at
squared radius at most 98/25. It does not assume the candidate contact graph.
It strengthens, rather than silently reuses, the earlier 4/5 marker lemma.

## 1. New marker and exact pair theorem

For an exterior square use sorted local coordinates (a,sigma*u), where

    a>=1/2,  0<=u<=a,
    (a+1/2)^2+(u+1/2)^2<=98/25.

Define the new label

    ell(a,u)=min(11u/10, 5/9+3u/5-17a/50, 157/200).

The marker is the primary frame angle plus sigma*ell. The label lies in
[0,157/200] on the full containing rectangle a in [1/2,3/2], u in [0,1].
The cap is smaller than pi/4, using pi>157/50.

**Pair theorem.** Two interior-disjoint exterior squares satisfying the disk
bound have marker distance strictly greater than 7/8.

For a hypothetical directed gap g in [0,7/8], let

    d=g+sigma*ell(a,u)-tau*ell(A,v),
    X=A cos d-tau*v sin d,  Y=A sin d+tau*v cos d,
    H=(|cos d|+|sin d|)/2.

The certificate proves each of

    a+1/2-X+H,
    1/2+sigma*u-Y+H,
    1/2-a+X+H,
    1/2-sigma*u+Y+H

strictly positive. Reversing the pair and reflecting the frame gives the same
gap and reversed signs, so the four inequalities also hold in the second
frame. No edge axis of either square can separate them; the separating-axis
theorem implies that their open interiors intersect.

## 2. Executed full-domain certificate

`verify_sharp_exterior_markers.cpp` uses exact 48-bit dyadic interval endpoints,
128-bit integer products, and integer floor/ceiling operations. Every terminal
acceptance is an exact interval inequality. It starts with the complete boxes

    a,A in [1/2,3/2],  u,v in [0,1],  g in [0,7/8].

Admissibility permits the following sound contractions:

    a >= u_lower,
    a <= sqrt(98/25-(u_lower+1/2)^2)-1/2,
    u <= min(a_upper, sqrt(98/25-(a_lower+1/2)^2)-1/2).

Only points violating these necessary conditions are removed. A remaining
box is accepted only when all four margin lower bounds are strictly positive;
otherwise it is bisected into two closed halves. Node/depth/resolution limits
raise errors, never a successful result.

The cosine and sine terms are kept correlated with their absolute-value width.
The minimum of alpha*x+|x|/2 over a rectangle is attained at one of its four
corners or at x=0; this exact elementary fact supplies the margin bounds.

The phase is always in [-157/100,489/200], contained in [-5/2,5/2]. At rational
endpoints, alternating Taylor polynomials give

    S19<=sin<=S17 and C18<=cos<=C16

for nonnegative arguments, with odd/even reflection otherwise. Potential
interior extrema at +/-pi/2 and 0 are conservatively included, using
157/50<pi<22/7. No trigonometric library output accepts a bound.

The only floating-point operation is an initial guess for an integer square
root. Exact correction loops then prove r^2<=n<(r+1)^2, so even an inaccurate
guess cannot cause an invalid root enclosure. The fixed domains keep interval
values below 16 in magnitude; 48-bit dyadic products and the factorials through
19! fit the stated integer types. The largest case was also run with the
compiler's undefined-behavior sanitizer, without a reported error.

Executed results:

| sigma | tau | Nodes | Positive terminal boxes | Maximum depth | Smallest certified leaf margin |
| --- | --- | ---: | ---: | ---: | --- |
| -1 | -1 | 181747 | 90874 | 39 | 630745552 / 2^48 |
| -1 | +1 | 45593 | 22797 | 30 | 241133457 / 2^48 |
| +1 | -1 | 2928045 | 1464023 | 47 | 1111076 / 2^48 |
| +1 | +1 | 452349 | 226175 | 42 | 1237811 / 2^48 |

No empty terminal boxes were needed after the admissibility contractions. Each
row satisfies nodes=2*leaves-1. All four finite trees terminated successfully.
These leaf margins are interval slack, not estimates of the true minimum.
The coefficients were discovered experimentally, but the theorem rests on the
full-domain verification, not on that discovery procedure.

## 3. Global consequences for eight arbitrary squares

There is exactly one square containing the disk center in its open interior:
eight exterior markers would have total cyclic separation greater than
8*(7/8)=7>2*pi. Disjoint interiors make the containing square unique.

Let g1,...,g7 be the successive gaps of the other seven markers. Then

    7/8 < gi < 2*pi-6*(7/8) < 29/28 < pi/3.       (1)

The sum of all excess gaps is particularly small:

    sum_i (gi-7/8)=2*pi-49/8 < 9/56.              (2)

Thus, after choosing one real marker representative phi0, all subsequent ones
satisfy

    0 < phi_k-phi0-7k/8 < 9/56,   1<=k<=6.

This is a continuous, rigorous near-heptagonal ordering constraint. It does
not impose equal gaps or a uniform mesh. Any partition into four consecutive
half-open quadrants still has counts (2,2,2,1): three markers in one quadrant
would span more than 7/4>pi/2.

Every open arc of length 29/28 meets an exterior marker. Therefore a central
square location that makes such a marker arc unavailable is impossible. This
is a sharper starting point for central-obstacle and separator analysis than
the old upper gap bound 52/35.

## 4. Negative result: the OLD label cannot simply use 7/8

The change of label is essential. With the old label

    ell_old=min(11u/10,3/5+4u/7-3a/8,3/4),

take source state (a,u,sigma)=(9/10,9/10,-1), target state
(A,v,tau)=(34/25,1/6,-1), and relative frame angle d=37/120.
The two labels are 3/4 and 11/60, so their marker gap is exactly 7/8.
Both states satisfy the disk bound; the target squared far-corner distance is
87841/22500<98/25. Nevertheless the first-frame vertical support margin is

    -2/5+(2/3)cos(37/120)-(43/50)sin(37/120).

Using only C4 as a cosine upper bound and S3 as a sine lower bound gives

    margin <= -960636307/37324800000 < -1/50.

Hence these two squares are separated and disjoint. This is an exact
counterexample to strengthening the old marker theorem by changing its gap
constant alone. The new label avoids that obstruction.

## 5. What this still does not prove

The new ring theorem constrains every hypothetical subcandidate packing, but
it does not yet select its central/exterior separating axes or show that six
squares are parallel. All central-square constraints and non-neighbor pair
constraints must remain present. The earlier seven-exterior counterexample
continues to rule out discarding the central obstacle.

The remaining task is to derive the five-corner chain of
FIVE_CORNER_OPTIMALITY.md, or to certify other structures impossible. No Lean
formalization is being attempted before that mathematical gap is closed.
