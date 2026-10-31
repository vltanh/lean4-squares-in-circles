# A high-square chord barrier with an exact lower-route length test

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed force-free reusable theorem, frozen for full
separate independent and root review.** It lets a caller supply a lower
height bound relative to the bottom of H, instead of having to prove its
actual A-to-B port is already above the top of H. The whole actual B
segment either reaches that top barrier or exceeds the unit diameter.

## 1. Complete statement

Let H,A,B be actual unit squares with pairwise disjoint open interiors,
contained in the original circle about O, with

    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<=epsilon<1/60,
    H=[h-1,h] times [g-1,g],
    h<=epsilon, 37/50<=g<=1.

Suppose there are real numbers ell,eta>0 such that

    ell+eta>sqrt(2),
    min_A x>=h-1,
    min_A y>g-1+eta.                                (1)

If the actual B contains a point P with

    P_x<=h-ell, P_y<7/10,                            (2)

then A and B cannot physically touch.

No positive force, graph degree, physical circle-contact mask or chosen
normal is a premise. In particular P may be any original C-to-B mean,
with the actual whole C only used by a caller to establish (2). No
conclusion that P is a vertex is made. Both horizontal strip endpoints
and equality P_x=h-ell are retained.

## 2. Every contact in H's closed horizontal strip reaches its top

Suppose V is an actual point of A intersection B. It satisfies

    V_x>=h-1, V_y>g-1+eta>g-1.                      (3)

If h-1<V_x<h and V_y<g, then V belongs to the open interior of H.
Since V is a point of the actual full-dimensional A, arbitrarily close
interior A points would remain in int H. This contradicts the disjoint
open interiors.

If V_x=h-1 and V_y<g, the first bound in (1) makes every interior
A point have x>h-1. Choose such points sufficiently near V. Their
abscissas are still below h, and their heights remain between g-1 and g.
They too lie in int H. Thus the exact left-side endpoint is excluded.

Consequently h-1<=V_x<h implies V_y>=g. The actual points P,V
then meet every hypothesis of the full signed-support high-square
barrier, and are impossible.

If V_x=h and V_y>=g, that same barrier includes the exact right-side
endpoint. If instead V_x=h and V_y<g, the actual B segment from V
toward P immediately enters int H: it moves strictly left from a
height strictly between its bottom and top. No sign of that segment's
vertical slope is required. This also contradicts physical disjointness.

## 3. A contact to the right cannot pass below H

Only V_x>h remains. Let E be the unique actual intersection of PV
with x=h. Since P_x<h<V_x, it is strictly between P and V, and the
whole segment belongs to the unchanged convex square B.

If E_y<=g-1, split this actual straight segment at E. Its two lengths
have the separate rigorous bounds

    |P-E|>=h-P_x>=ell,
    |E-V|>=V_y-E_y>eta.

They add because E is between P and V. Therefore

    |P-V|=|P-E|+|E-V|>ell+eta>sqrt(2),              (4)

contrary to the diameter of the same actual unit B. This includes
E_y=g-1 and P_x=h-ell.

If g-1<E_y<g, the portion from E toward P immediately enters int H.
If E_y=g, the same conclusion holds because P_y<7/10<g, so that
portion moves down and left. These cases are physically impossible too.
Hence E_y>g. The actual B points P,E now satisfy the signed-support
barrier at its included right endpoint E_x=h, again a contradiction.

This exhausts all positions of the original V. The auxiliary E has
only been used as a point of the actual B chord, never substituted
for an original force application or mean.

## 4. Two useful uniform numerical instantiations

The theorem applies, in particular, to each whole interval described by

    ell=1,   eta=5/12;
    ell=6/7, eta=679/1200.

For the first, ell+eta=17/12 and

    (17/12)^2-2=1/144>0.

For the second,

    6/7+679/1200-17/12=53/8400>0.

No upper bound on the actual horizontal A port is needed in either
case. The inequalities are complete continuous bounds, independent of
the orientation, selected normal, physical circle mask or force degree
of B. The original all-nine-unit setting is preserved by any literal
caller; no completing square is removed.

| Operative source | SHA256 | Literal use |
| --- | --- | --- |
| HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md | e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58 | Entire force-free signed-support barrier, including both closed horizontal endpoints and all actual B frames |

There is no numerical pose, sampling, mesh, force deletion, normal
reselection, changed mean, Lean run, CI, original ledger change or
remote mutation. A graph application must supply the literal actual
unit A and its complete extent in (1), rather than only one convenient
point with that height.
