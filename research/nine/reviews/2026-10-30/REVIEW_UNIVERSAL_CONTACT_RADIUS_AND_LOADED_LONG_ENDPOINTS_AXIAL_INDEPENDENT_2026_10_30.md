# Independent full review: universal contact radius and loaded long endpoints

**Date:** October 30, 2026 UTC. **Reviewer:** axial-chain agent, separate
from the author. The complete source, including all three geometric/
force scopes and the optional global same-pair consequence, was read
and independently reconstructed.

Reviewed source:

`UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md`

* Bytes: 10904.
* SHA256: `d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705`.
* Git blob: `dc386733b03fb00d3f165b7e4dca897a091da7ce`.

## Conclusion

**PASS at the full stated scope, with no repair required.** Every
actual two-square contact point has norm strictly below 29/15.
A support-gap-two endpoint has its entire dominant outward own side
free from every other closed square. If it has a positive inward
contact in a complete translational balance, its circle load is
positive. Hence every genuine two-internal unloaded true-degree-two
channel ends at two positively loaded bodies, regardless of their
other degrees, contacts or block roles.

No lower radius window, torque, physical plane embedding, endpoint
boundary assumption, degree restriction on the endpoints, or change
of certificate is used in these main theorems.

## 1. Universal contact-radius reconstruction

The exact corner formula gives `|c|<M=91/60`, with comparison reserve
`31/57600`. Every point of a unit square is within `sigma=1/sqrt(2)`
of its center, while distinct physical centers have separation at
least one by their open incircles.

Suppose a common point p has radius r>=K=29/15, and put e=p/r.
For any incident square its displacement v=c-p is nonzero, since
its center radius is below M<K. Write t=|v|<=sigma. If v were
not strictly inside the inward radial cone of half-angle pi/4,
then `-e.v<=t/sqrt(2)`. Consequently

`|c|^2>=r^2+t^2-sqrt(2)*r*t>=r^2-r+1/2`.

The second inequality is valid on the full closed interval
`0<=t<=sigma`: its quadratic decreases there when r>1. The
printed endpoint-factor proof has the correct signs. The radial
expression is increasing for r>=K and at K equals `M^2+1/240`,
contradicting the strict center bound. Thus every incident center
displacement lies strictly within that inward forty-five-degree
cone, including the threshold r=K.

Two such nonzero vectors have strictly positive dot product. In
coordinates `v_i=-a_i e+b_i e_perp`, one has `a_i>|b_i|`, so
`v_1.v_2>=a_1*a_2-|b_1*b_2|>0`. Their center separation squared
is therefore strictly less than `|v_1|^2+|v_2|^2<=1`, impossible.
This proves the full contact-radius statement for every actual
contact point, including shared-side interiors, side endpoints,
zero-stress contacts and junctions.

## 2. The entire outward own side is free

For a support gap of two, center and minimum-width bounds give
endpoint projections beyond `+-L`, where L=89/60, and
`h_A+h_B<31/30`, hence each halfwidth is below 8/15. In an
endpoint's own frame, choose its side axis pointing outward with
the larger absolute long-normal coefficient a; call the other
absolute coefficient b. Then `a>=b>=0`, `a^2+b^2=1`, and
`a+b<16/15`.

It follows that `(a-b)^2>194/225>81/100`, with exact comparison
reserve `47/900`. Thus a-b>9/10 and the dominant axis is unique.
Every point of the actual full outward side, including its two
corners, has long-axis projection magnitude greater than

`L+(9/10)/2=29/15`.

The universal contact-radius theorem excludes every other closed
square from that whole side. This selects an existing own side;
it does not replace the long normal by that side's axis or rotate
the square.

## 3. The endpoint force argument retains every incident force

For a square with own outward axis u, any support normal n with
`n.u>0` exposes only points on the own side with u-coordinate
`+1/2`. Such a contact is impossible if that entire closed side
is contact-free. Therefore every actual positive incident contact
normal has nonpositive u component.

The source's complete translational equation is

`2*sum lambda*z + sum mu*n=0`,

with n oriented from the square toward its neighbor. This convention
is consistent with the tight separator gradient. If one inward
contact has strictly negative u component, the sum of all contact
terms has strictly negative u component: the other retained terms
are nonpositive and cannot cancel it. Zero total nonnegative circle
weight would remove the circle term and contradict the full equation.
Thus positive total circle load is forced. The argument neither
assumes nor deletes any other endpoint force.

For the first endpoint, the long-path normal d has component -a in
its outward own axis, and for the second endpoint the actual inward
normal -d has the analogous strictly negative component. The signs
in both applications are correct. The geometric other endpoint is
only a witness for the support gap and need not touch the tested
endpoint itself.

## 4. Full graph caller and optional joint consequence

At each of the two genuine unloaded true-degree-two internal bodies,
its complete force equation makes its two positive forces equal
and opposite. Propagation supplies the common signed normal along
the three actual contacts. Tight support equalities telescope to
the required endpoint gap with internal reserve at least two. The
first and last path contacts have positive magnitude and the inward
normal signs just checked. Both endpoints therefore have positive
circle load in the same retained certificate.

The conclusion covers arbitrary unloaded branching, articulation,
ear or hub endpoints by excluding them, even if they physically
touch the circle with zero selected weight. It does not claim the
same for shorter runs. All endpoint degrees and all other actual
positive forces remain in the proof.

In an actual nine-unit packing, combining this result with the
frozen two-channel capacity theorem correctly says that every
two-internal suppressed label has the same unordered pair of
positively loaded endpoints. The imported theorem applies to the
same full translational stress and was independently reviewed in
full. Parallel channels on that same pair are preserved. The source
does not claim that every large block contains such a label.

## Exact audit and boundaries

The source byte record and all rational comparisons were recomputed,
including `K^2-K+1/2-M^2=1/240` and the outward-side reserve.
The main theorems are self-contained; the only optional external
pin is the already frozen two-channel source `e05fa052...`.
The proof retains every actual unit, original mean, positive force
and zero-stress physical contact. No original fine/coarse flag,
metadata, Lean file, CI state or remote publication was changed.
