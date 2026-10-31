# Independent review of the long-endpoint return locus and tilted vertex reduction

**Date:** October 30, 2026 UTC. **Reviewer:** annular-capacity agent.

**Verdict: PASS at the complete stated scope. No source repair is required.**

## 1. Frozen source, independence, and input boundary

I read the entire manuscript
`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`
and independently reconstructed Sections 1--9 and their joins. The reviewed
source is 21,325 bytes with SHA256

`cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`.

The source was not edited. I independently read Section 1 of
`C7_HIGH_CENTER_CONTACT_TYPES.md` and reconstructed the complete face lemma
before reading this manuscript. I previously supplied the author with the
observation that this face lemma can be applied using the long-endpoint own
coordinates, and with the preliminary moment-sign calculation. This review
is therefore a full independent reconstruction of the finished proof, with
that prior mathematical communication disclosed; it is not a claim that the
underlying idea was developed without discussion. The later tilted-vertex
reductions and their two-circle calculations were independently checked
from the author's frozen source.

All five input SHA256 pins in Section 10 match the current source bytes:

- coupled endpoint bounds: `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6`;
- high-center face lemma: `68e94d3f80274c07f3a4f6c0d01eab753733b1e808838c6abf6e4448cfc481b8`;
- true-channel barrier and original means: `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05`;
- whole-return-side theorem: `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e`;
- exact contact lens: `3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3`.

The local face and lens arguments are fully reproduced. No all-owned
selection, radial center lower bound, generic point contact, or free-normal
selection theorem from the older C7 sources is imported.

## 2. Endpoint coordinates and all contact exclusions

The support-gap-two pair gives the actual endpoint center projections
`89/60<X_A,X_B<91/60` and the coupled height bound
`|y_A|+|y_B|<=1/8`. At the right endpoint the dominant outward own axis
and upper transverse axis have coefficients `a>=b>=0`. The half-width
bound `a+b<16/15` gives `a-b>9/10` and `b<1/12`. These imply

    P-|T|>721/600>1,
    |T|<589/1800<1/2.

The signs needed for every subsequent moment are consequently strict:
`P-1/2>0` and `T+1/2>0`. The more accurate orientation estimates follow
in the stated order: `a>99/100`, then `ab<31/450`, then
`b<62/891<7/100`, then `a>399/400`. In particular none depends on
the endpoint being tilted or on its radius being at least three-halves.

The actual supporting-face unit-chord proof covers every point of a shared
side and its endpoints, as well as every admissible vertex normal. It gives
the contact radius squared at most `849/256`. The entire outward own side
has global x coordinate greater than `29/15`; the strict difference of
squares is `24271/57600`. Thus that whole closed side is physically free.

For the inward own side, the old face lemma applies with
`kappa=P+1/2` and `ell=|T|+1/2`. Physical boundary contact gives
`kappa^2+ell^2=q`; the own-coordinate difference is above one. At a
neighbor's maximum-x support, an actual vertex in the source side interval
always exists. In the parallel-support-side case this uses the equal unit
lengths of the two intersecting intervals, so no side-endpoint case is lost.
All four neighbor corners are strictly inside the disk by the two adjacent
corner bounds and the opposite-corner bound. This excludes precisely the
inner own-axis separator with a boundary neighbor, not every contact at
the inner vertices under a different normal.

Finally the complete lower transverse side lies below `-13/40`. It cannot
meet a square wholly above zero. Combining these three exclusions leaves
exactly the upper transverse side without its outward endpoint. At its
relative interior the normal is v. At its inner endpoint every actual
normal is `-alpha*u+beta*v`, with `alpha>=0` and `beta>0`; the zero-beta
case is the excluded inward-face separator. Both actual support cones at
a vertex/vertex contact are respected. No neighbor ownership is inferred.

The origin moment is positive in both remaining cases. At the vertex it
is `(P-1/2)*beta+(T+1/2)*alpha>0`. Reflection changes this sign at the
left endpoint and preserves the above-side condition. This proves the
force-free locus over its whole claimed domain.

## 3. Full-star moment sign and tilted long-contact geometry

For the true two-transmitter channel, the imported torque result supplies
the original means `(s-1,t),(s,t),(s+1,t)`, with `|s|<1/60` and
`|t|<=9/16`. It does not require either internal mean line to pass through
a center, nor equal internal center heights.

At the right endpoint the long inward force has origin moment `mu*t`.
Under the explicit full-star premise every other positive edge contributes
a strictly positive moment, and there is at least one such edge. Each
original circle atom is radial and has zero origin moment, even when two
circle corners carry independent weights. Hence full angular balance gives
`t<0`. The left equation gives the same sign. The premise on **every**
additional positive endpoint edge is needed and is correctly retained.

If the right endpoint is tilted, the other tilt sign would expose a
minimum-x long vertex above zero. Thus its actual axes are
`u=(a,-b),v=(b,a)` and its actual long mean is the lower-inner vertex
`q_B=c_B-(u+v)/2`. Every return normal now has positive global y component.
The full y-force equation requires a negative total circle y resultant.
If `T>0`, the unique circle corner instead has height
`t+a-b>=27/80>0`, a contradiction. Therefore `T<=0`, including the
two-circle-corner case `T=0` with both original weights retained.

The exact identity `T=b(s+1)+a*t+1/2` yields

    t<=-(1/2+b(s+1))/a<-1/2.

It follows that this endpoint's center height is negative. If the opposite
endpoint is aligned, its long mean lies on its full inward vertical side,
so its center height is at most `t+1/2<0`. If it is tilted, the reflected
argument applies. No equality of endpoint or internal center heights is
introduced.

## 4. Tilted true-degree-two endpoint: the two-circle calculation

I checked the exclusion of the own upper-axis return normal from the full
force and torque equations at their original means.

Write `K=P+1/2` and let the upper-side mean be
`p=q_B+v+zeta*u`, `0<=zeta<=1`. Divide by twice the positive total
circle load. Its positivity follows directly from the y-force equation,
so this normalization does not omit a zero-load branch.

When `T<0`, put `w=1/2-T`. In own coordinates the long mean is
`(K-1,-w)` and the only circle corner is `(K,-w)`. The two normalized
contact magnitudes are `K/a` and `w+bK/a`. Taking moments about the
actual long mean gives exactly

    (w+bK/a)*zeta=w.

Since `w>=1/2`, this implies `zeta>=a/(a+2Kb)`.

When `T=0`, the original circle weights give a normalized transverse
coordinate `eta` anywhere in `[-1/2,1/2]`. The actual positive return
magnitude is `bK/a-eta`, and the normalized circle moment about the long
mean is the negative of `(K-1)*eta+K/2`. Thus

    zeta=((K-1)*eta+K/2)/(bK/a-eta).

On its actual positive-denominator interval this quotient is strictly
increasing: the derivative numerator is `(K-1)*bK/a+K/2>0`. Its
minimum at `eta=-1/2` is again `a/(a+2Kb)`. This proves the same
bound for every permitted two-circle weighting without asserting that each
individual circle atom points down.

Using `K<121/60`, `a>399/400`, `b<7/100` in the original global
x coordinate yields the stated function g. Its derivative is negative
on the whole closed interval because the maximum denominator squared is
less than the numerator coefficient. The exact difference is
`170554543/72000000>0`. Its minimum exceeds `21/25` by
`18263/3077600`. Therefore the unchanged actual return mean has

    p_x>547/300,
    (547/300)^2-849/256=11719/1440000>0,

contradicting the contact radius. The argument includes both endpoint
values of zeta. The only remaining return locus is the upper-inner vertex,
now with `alpha>0` and `beta>0`, but with no normal-ownership restriction.

## 5. Aligned other endpoint under the same low force line

If the right endpoint is aligned and `t<=-1/2`, let
`K=X+1/2,w=1/2-y`. Its actual long side gives `y<=0`, while the
coupled height estimate gives `1/2<=w<=5/8`. Boundary containment
gives `q=K^2+w^2` and `K^2<=Q-1/4`. If `y=0`, both outer circle
corners are retained in their actual normalized mean `(K,eta)`.

For an own upper-axis return, force balance makes `eta<0`, with
`-eta<=w`. The original origin-moment equation then forces
`p_x=(-t)K/(-eta)>=K/(2w)`. The actual normal chord puts
`p+e_y=(p_x,2-w)` inside the return square. Its squared norm exceeds
q by at least

    -(9/25)*(Q-1/4)+3/2=231/6400>0.

Both estimates on w are used with the correct inequality signs. This
contradiction is valid at the closed thresholds `t=-1/2`, `w=1/2`,
and `w=5/8`; the radial two-circle case is not lost. Hence this endpoint
also has its return mean exactly at its upper-inner vertex with both
inward and upward own-normal components strictly positive.

## 6. Complete caller and exact remaining scope

The opposite long/short seven-cycle caller uses the previously proved
whole-square return localization in the stated radius window. Its actual
return squares lie above `1/120`, so they meet every local halfplane
premise. When the two long endpoints have full true degree two, their
only other positive forces are exactly those return joins. Thus both
full-star hypotheses and both local two-edge calculations apply.

If either endpoint is tilted, the original line lies in
`[-9/16,-1/2)`, both endpoint centers have negative height, and both
direct return means are their original upper-inner vertices. All actual
vertex normals, both physical circle atoms when present, and the two
remaining physical packing units are retained. The source appropriately
does not extend the two-edge conclusions to arbitrary additional forces.

The manuscript stops at this uniform reduction. It does not claim that
the remaining short-channel gap is impossible, that both endpoints are
aligned in every packing, or that the nine-square sharp theorem is closed.
Those stronger conclusions require additional geometric coupling.

All ten displayed rational constants checked in this review were
recomputed with exact rational arithmetic, in addition to the complete
hand reconstruction. No pose search, numerical certificate, graph
re-selection, Lean compilation, CI run, original ledger mutation, or
publication was performed. The entire frozen source passes without repair.
