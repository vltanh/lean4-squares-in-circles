# A radius-free angular budget for near-origin unit squares with unequal distance bounds

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete new continuous geometric lemma, frozen for independent review.** The distance bounds may differ from unit to unit. The proof retains every actual frame and every possible position of the origin relative to a square. It makes no containing-circle, force, degree, contact, or common-orientation assumption.

The useful three-unit specialization allows two actual units within 1/40 of O and a third within 13/300, provided all their vertices have norm greater than 19/300. This does not infer any of these premises from a small center or from pocket occupancy.

## 1. General unequal-distance theorem

Let S_1,...,S_N be actual closed unit squares with pairwise disjoint open interiors. Fix a radius d satisfying

    0<d<1/2.

For each i let

    0<=delta_i<d,
    dist(O,S_i)<=delta_i,

and suppose every vertex of every S_i has norm strictly greater than d.

Then

    sum_i acos(delta_i/d)<=pi.                       (1)

Consequently, if prescribed bounds delta_i make the sum in (1) strictly greater than pi, no such actual squares exist.

The statement uses distance to the actual whole square, not distance to its center. Every delta_i may be attained. The common vertex inequality remains strict.

## 2. Complete angular measure bound for one square

Let S satisfy the stated conditions for one delta. Measure the angular length of

    int(S) intersection {|z|=d}.

I prove that this length is at least

    2acos(delta/d).                                  (2)

### 2.1. O is outside S

The actual nearest point of S cannot be a vertex: that would give a vertex of norm at most delta<d. In an actual own frame, after a rigid rotation or reflection about O, therefore

    S=[a,a+1] x [b,b+1],
    0<a<=delta, b<0<b+1.

Both vertices of the nearest face are outside the closed d disk. Hence

    -b>sqrt(d^2-a^2),
    b+1>sqrt(d^2-a^2).

Every point on the d circle satisfying x>a lies strictly inside S. Its horizontal coordinate is at most d<a+1, and its transverse coordinate has absolute value strictly below sqrt(d^2-a^2). Thus the entire open arc x>a lies in int(S).

Its angular length is

    2acos(a/d)>=2acos(delta/d).

The possible equality a=delta is retained. No strict measure improvement is silently asserted from the strict vertex margin.

### 2.2. O lies on the boundary of S

O cannot be a vertex, so it lies in the relative interior of an actual side. The same frame argument has a=0. The two side endpoints have norm greater than d; the opposite side is one unit away. Consequently the full open semicircle x>0 lies in int(S), giving angular length at least pi.

This is at least 2acos(delta/d), since delta>=0. The delta=0 equality is retained.

### 2.3. O lies in the interior of S

Opposite faces are one unit apart, whereas the d circle has diameter less than one. Therefore at most two faces can cut the circle; if there are two, they are adjacent.

If no face cuts it, the full circle lies in int(S), apart from irrelevant possible tangencies. If exactly one face cuts it, that face is at a strictly positive distance from O and removes an arc of length strictly below pi. More than pi remains.

If two adjacent faces cut it, let their positive distances from O be a,b<d. Their common actual square vertex has norm greater than d, so

    a^2+b^2>d^2.

It follows that

    acos(a/d)+acos(b/d)<pi/2.

For example, a/d>sqrt(1-(b/d)^2), and both inverse-cosine arguments are in (0,1), so acos(a/d)<asin(b/d)=pi/2-acos(b/d).

The two outward half-planes remove angular length at most twice that sum, strictly below pi. Thus more than pi remains in int(S). Tangencies remove zero angular length.

In all interior-origin cases the measure is greater than pi and hence at least the quantity in (2). These three cases exhaust the actual location of O relative to S and prove (2).

## 3. Sum the actual disjoint arcs

The open interiors of different actual squares are disjoint. Their intersections with the same d circle are therefore disjoint measurable sets. The total angular length is at most 2pi.

Summing (2) gives

    2 sum_i acos(delta_i/d)<=2pi,

which is exactly (1). No connectedness of the complete circle intersection is assumed in the interior-origin case. Only the explicit contained arc or complete measure bound is used.

This proves the full unequal-distance theorem.

## 4. Two units within 1/40 and a third within 13/300

Take

    d=19/300,
    delta_1=delta_2=1/40,
    delta_3=13/300.

All distances are strictly below d, and d<1/2. The relevant normalized values are

    delta_1/d=delta_2/d=15/38,
    delta_3/d=13/19.

Put

    alpha=acos(15/38),
    beta=acos(13/19).

Both 2alpha and pi-beta are in (pi/2,pi). Their exact cosines satisfy

    cos(2alpha)=2(15/38)^2-1=-497/722,
    cos(pi-beta)=-13/19=-494/722.

Thus

    cos(pi-beta)-cos(2alpha)=3/722>0.

Strict cosine monotonicity gives

    2alpha>pi-beta,
    2alpha+beta>pi.                                  (3)

Equation (3) contradicts the general angular budget (1).

**Unequal near-three corollary.** Three pairwise interior-disjoint actual unit squares cannot have two distances to O at most 1/40 and the third at most 13/300 while every one of their actual vertices has norm greater than 19/300.

Every distance endpoint is included. The strict reserve is supplied by (3), rather than by pretending the prescribed distance bounds are strict.

## 5. A second convenient specialization with the older vertex constant

For callers having only the older common vertex margin 3/50, take

    d=3/50,
    delta_1=delta_2=1/40,
    delta_3=3/80.

The normalized distances are 5/12,5/12,5/8. If alpha=acos(5/12) and beta=acos(5/8), then

    cos(2alpha)=-47/72,
    cos(pi-beta)=-5/8=-45/72.

The positive difference is 1/36. The same monotonicity argument gives 2alpha+beta>pi. Therefore those three distance bounds are also impossible when all actual vertices have norm greater than 3/50.

This is a separate exact specialization. It does not replace the stronger vertex premise in Section 4 or mix radii between its arcs.

## 6. A coordinate criterion for the third unit

The first specialization is particularly convenient for an actual hub already written in its own axes as

    U=[x-1,x] x [p-1,p],
    0<x<61/60,
    0<p<26/25.                                      (4)

The distance from O to this actual rectangle is exactly

    dist(O,U)^2=max(x-1,0)^2+max(p-1,0)^2.

Consequently (4) gives

    dist(O,U)^2
       <(1/60)^2+(1/25)^2
        =169/90000
        =(13/300)^2.                                (5)

Thus, if every U vertex has norm greater than 19/300 and two other distinct actual units satisfy the first two distance and vertex conditions of Section 4, the whole configuration is impossible.

This coordinate criterion preserves both x>=1 and p>=1 possibilities. It does not claim that U contains O and does not infer (4) from a small center. A force or pocket caller must establish (4) and the four actual vertex inequalities separately.

For comparison, the already proved radial-tip injection gives the stronger third-unit distance 1/60 and vertex margin 7/100, so it lies strictly within both near-three specializations.

## 7. Relation to the actual side-channel and central-unit constants

The constants in Section 4 match two separately established actual geometric conclusions:

- An occupied force-free width-one side-channel pocket supplies its unchanged transmitter H with distance to O less than 1/40 and every vertex farther than 7/100.
- The enclosed-unit side/corner restrictions supply an actual central extra E with distance less than 1/40 and every vertex farther than 19/300.

The latter margin is strictly larger than the older convenient 3/50 margin. It is retained here rather than weakened before the angular comparison. No conclusion about a third unit U follows automatically; Sections 4 and 6 are conditional on its actual distance and vertex bounds.

In particular a bare small-center hypothesis such as |c_U|<3/4 is insufficient for (4) or (5), and no such inference is made.

## 8. Proof provenance and verification boundary

The equal-distance near-origin lemma is in Section 4 of

    SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md
    SHA256 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c.

Its complete one-square argument is reproduced and extended to separate delta_i in Sections 1--3 above. There is no unprinted mathematical premise in the new general theorem. In particular the interior-origin case is not restricted to one connected arc.

The separately proved geometric constants mentioned only in Section 7 are:

| Source | SHA256 | Scope mentioned |
| --- | --- | --- |
| FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md | 5e8f69ad14c78b6ad99a1ba46855fc3627df5ccc1d5451f295826d2b06709abb | Actual occupied side-channel transmitter distance and vertex margin. |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Enclosed-unit own-center and strict vertex margins, with their actual finite enclosing ring retained. |
| TERMINAL_HUB_AXIS_RADIAL_TIP_NEAR_ORIGIN_INJECTION.md | acd1a2b515779188a9e029d7e9b4a4c0182cde9c43b58fb52cd2a4237094761a | The distinct local radial-tip theorem giving the stronger actual third-unit bounds; not needed in Sections 1--6. |

The exact trigonometric comparisons reduce to the displayed rational cosine reserves 3/722 and 1/36. The coordinate threshold is the exact 5-12-13 identity (5). All cases are continuous and every stated endpoint is retained.

This manuscript performs no original-row or coarse-family closure, ledger edit, physical motion, force deletion, mean substitution, pose sampling, angle grid, numerical exclusion certificate, Lean compilation, CI, remote mutation, or commit.

