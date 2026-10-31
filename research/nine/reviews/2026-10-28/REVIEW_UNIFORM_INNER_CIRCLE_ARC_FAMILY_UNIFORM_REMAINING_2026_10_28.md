# Independent review of the continuous inner-circle arc family

Date: October 28, 2026 UTC. Reviewer: uniform_remaining continuation.

**Disposition: PASS at the complete stated scope.** I independently read
and checked the entire new manuscript, including its own-frame domain,
both continuous comparisons, the weak-clearance tangency residue, the
radial-center assertion, every nine-body consequence, both radius-endpoint
examples, and the precise older-kernel joins. I found no mathematical or
scope gap requiring a source change.

## 1. Exact reviewed bytes and independence

| Source | Frozen SHA256 |
| --- | --- |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | a8e38f8fa30e50933a0548ddd61fc831531249bf68b1a918a67ad6a6b0bc95f0 |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb |

The first manuscript was authored by root. I did not contribute to its
derivation or edit its source. Before the review assignment, root had
described its intended smaller-clearance consequence in one short progress
message; that did not supply a proof, and I independently checked all the
proof details in the final manuscript. The second source was read in full
to verify the exact older exports and channel premises claimed in Section
10. It is not a hidden premise for the new geometric proof.

The proposed theorem concerns the same actual units in one fixed disk and
one fixed comparison circle. It never changes an original orientation,
force, contact normal, application, shared mean, mask, degree, or body.
This review credits no whole original fine family or coarse cell.

## 2. Constants and full parameter interval

I verified the identities

    r_-^2=2*(2+sqrt(2))*(sqrt(Q/2)-1)^2,
    r_+=1/(2*sin(pi/8)), Q=1105/256,

and the complete positive comparison chain

    6/5<r_-<157/128<13/10<r_+<4/3.

Each squaring is applied to positive numbers. The printed rational
reserves were rechecked exactly using rational arithmetic. In particular:

| Comparison | Exact positive reserve |
| --- | --- |
| `Q/2-(117/80)^2` | `247/12800` |
| `(2351/1600)^2-Q/2` | `2201/2560000` |
| `23273/16000-36/25` | `233/16000` |
| `(157/128)^2/2-(239/70)*(751/1600)^2` | `11919/716800000` |
| `2-(238/169)^2` | `478/28561` |
| `(23/16)^2-2` | `17/256` |
| `1377/2000-933/1600` | `843/8000` |

The additional trigonometric comparison follows by the exact squared
difference `(3-2*sqrt(2))/32>0`, with both sides positive. No decimal
inverse-trigonometric evaluation supplies a premise.

These elementary checks establish the stated interval and the rational
choice `r=157/128`, `h=29/128`. They are transcription checks for the
written proof, not a finite orientation or pose exclusion certificate.

## 3. Own-frame normalization and the entire a>r case

Independent sign changes and exchange of the actual own axes make the
actual center coordinates satisfy `x>=y>=0`. Thus

    E=[A,a] times [B,b],
    A=a-1, B=b-1, a>=b>=1/2, a^2+b^2<=Q.

This is the complete orientation domain. Its nearest-point formula is
`(max(A,0),max(B,0))`; no boundary-contact hypothesis is introduced.
The three cases in the source exhaust this domain under clearance.

When `a>r`, the source's bounds `0<A<41/40`, `|B|<=1/2`, and
`A^2+B^2<2081/1600<r^2` are valid. The strict upper A comparison has
reserve `219/6400`; the lower radius comparison follows from `r>6/5`.

I rederived the fixed-q expansion in the variable `t=a+b`:

    A^2+B^2+sqrt(2)*A*B
      =(1-1/sqrt(2))*q+t^2/sqrt(2)
        -(2+sqrt(2))*t+2+sqrt(2).

Its coefficient of `t^2` is positive. Consequently its maximum over the
entire fixed-q interval is at `b=1/2` or `a=b`. The proof deliberately
enlarges its domain to that interval; it does not assume its endpoints
satisfy the original a>r or clearance conditions.

At the first endpoint, the convex quadratic has the stated endpoint
values `3/20` and `933/1600`. At the equal-coordinate endpoint,
`3/4<w<=sqrt(Q/2)` holds, and the upper endpoint of `(w-1)^2` is the
larger one because `sqrt(Q/2)>5/4`. This proves the uniform bound by
`E_*`, followed by the strict inequality `E_*<r^2/2` from `r>r_-`.

For the actual intersection, the positive x-coordinate leaves only the
right semicircle. The inequality `A^2+B^2<r^2` gives `beta>-alpha`,
so the source's interval

    [beta,min(alpha,gamma)]

is the complete closed intersection. Its open version is precisely the
open-interior intersection. No second arc or isolated point is omitted.

The equivalence with
`(sqrt(2)*A+B)^2<r^2-B^2` is exact. Taking the positive square root
gives the desired bound even if its left unsquared expression is
negative. The subsequent cosine comparison stays in its decreasing
branch because `|beta|<pi/4`. Therefore the inner-face candidate length
is strictly greater than pi/4.

The other candidate is the entire strip width
`asin(b/r)-asin((b-1)/r)`. Its derivative is nonnegative for b>=1/2
because `b>=|b-1|`. Its minimum is `2*asin(1/(2*r))`, strictly greater
than pi/4 by r<r_+. Continuity covers b=r; b>r is covered separately.
Thus this whole case proves a connected open arc with the required
strict length.

## 4. Outer faces with positive B: the full derivative factor

When `a<=r` and `B>0`, the exact complete domain is

    0<B<=A<=h<1/3, k^2=A^2+B^2>=h^2.

The stated intersection interval imposes all four actual square faces.
Checking all four upper-minus-lower differences is sufficient to prove
both existence and the strict length of that entire interval.

The two opposite-face differences have the strip bound already proved.
The inner-inner difference is at least
`pi/2-2*asin(h/r)>pi/4`, since `h/r<1/4<sin(pi/8)`.

I checked the remaining outer-outer derivative independently. Along
`B=sqrt(k^2-A^2)`, compare its two positive derivative terms. After
clearing their positive denominators and squaring, the relevant
difference is

    B^2*(r^2-(1+B)^2)-A^2*(r^2-(1+A)^2)
      =(A-B)*[(A+B)^2
               +(k^2-2*h-h^2)*(A+B)+k^2]
      =(A-B)*[(A+B-h)^2
               +(k^2-h^2)*(A+B+1)].

Here `r^2=1+2*h+h^2`. Both factors on the last line are nonnegative.
The path from A=B to the actual A>=B stays entirely in the stated
domain; `k/sqrt(2)<=h`. Endpoint infinite derivatives cause no problem
because the original inverse-sine expressions are continuous there.

The lower bound at the equal-coordinate point therefore holds even at
the weak clearance k=h. Its inverse-sine argument is strictly greater
than `3/4+1/(4*sqrt(2))`, and hence greater than cos(pi/8). This proves
the fourth strict difference. All inverse-sine arguments remain in
[0,1] and all uses are on the increasing branch.

Thus the full outer-face positive-B domain, including its weak
clearance boundary and its own-face tangencies, passes.

## 5. The weak-clearance tangent side is handled exactly

In the last case `a<=r`, `B<=0`, the nearest-point formula and
clearance force exactly `a=r`, `A=h`, and `-1/2<=B<=0`.
There is no such case under strict clearance.

The inner x face does not truncate the interval between the two y-face
angles, since `h^2+b^2<10/9<r^2`. The outer x face is tangent at
angle zero. The actual open intersection is consequently

    (beta,gamma) minus {0}, when 0 belongs to that interval.

For B=0, zero is already an excluded endpoint. For B<0 it is an
interior deleted point and the set has two connected components.
The source correctly declines to assert connectedness in that case.
Removing the point preserves angular measure, so the same full strip
bound proves measure strictly greater than pi/4.

This exact treatment is essential for the source's weak-clearance
count and its central-disk statement with tangent sides. It is present
and correct; no limiting connectedness argument is substituted.

## 6. Radial center point and all counting consequences

Under strict clearance the nearest-point supporting normal has
minimum support greater than h. Every unit-square projection
halfwidth is at least 1/2. Thus `|c|>h+1/2=r-1/2`.
The actual farthest corner gives

    |c|^2+|c|+1/2<=Q,
    |c|<91/60,

with exact reserve `31/57600` at 91/60. Since r>6/5, the latter is
less than r+1/2. Therefore `abs(|c|-r)<1/2`, which puts the actual
radial center point in the square's open incircle and hence in its
already proved unique open arc. It does not assert that the whole
intersection is a centered arc.

For different actual interior-disjoint units, their open intersections
with the same comparison circle are disjoint measurable subsets.
Eight measures each strictly greater than pi/4 cannot fit on that
circle. The at-most-seven statement needs no connectedness, so it
also covers the exact tangent residue reviewed above.

The nine-unit count then forces at least two distinct actual units
at distance strictly less than h. If one unit contains the closed
disk D_h, its interior contains the open disk, even with side
tangency. Every other closed unit avoids that interior by actual
interior nonoverlap; thus all eight others have distance at least h,
contradicting the count. This proves the entire weak central-disk
containment exclusion.

In the original radius window, every physical boundary unit has
distance at least `R-sqrt(2)>19/40>h`. Hence the two near units
are physically circle-clear. Their zero selected load, when a stress
certificate is present, is a consequence of this geometric fact.
The direction of implication is correct; zero load is never used to
infer physical clearance.

## 7. Both endpoint examples are actual and sharp for the strict arc claim

At r=r_-, the source's square `[v-1,v]^2` has farthest-corner norm
sqrt(Q), and both outer faces exceed r. Its actual open circle arc
is exactly `(pi/8,3*pi/8)`, of length pi/4. Its clearance is strictly
greater than r_--1. Thus the lower endpoint genuinely fails the
claimed strict arc inequality, rather than only a relaxed estimate.

At r=r_+, the square `[1/2,3/2] times [-1/2,1/2]` is contained in
the smaller squared-radius-5/2 disk. Its clearance 1/2 exceeds r_+-1.
Neither x face cuts the arc controlled by its two horizontal faces,
whose length is exactly `2*asin(1/(2*r_+))=pi/4`.

Both examples preserve strict clearance. They justify excluding the
two interval endpoints for the strict-length family, without asserting
that either example is an equality nine-square packing.

## 8. Existing-kernel joins and final disposition

I read the complete older `GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`.
Its first section assumes an actual containing half-plane of height
greater than 1/4, hence actual distance greater than 1/4. Its
connected arc and radial-center exports are the r=5/4 instance of
the new theorem, with all old physical hypotheses retained.

Its second section has the specific entire multi-load simple positive
cycle, real true-degree-two unloaded transmitter, and actual channel
applications. It proves height strictly greater than 3/10, and its
third section places each whole exterior extra in the actual cap.
Those exact extras therefore have strict clearance for every
`r in [157/128,13/10]`. The new source correctly retains the need for
a separate actual occupied-crosscut routing and capacity argument.

The old source hash matches its displayed pin. No source is silently
replaced and no historical review is made to certify new bytes.

**The entire manuscript passes independent review at the frozen hash
in Section 1.** It supplies a continuous force-free kernel, a strictly
smaller central-disk obstruction, and at least two actual physically
clear near units in the original nine-unit problem. It does not alone
close an original graph/load family, classify equality, discharge all
prerequisites, or complete the global sharp theorem.

No Lean compilation, CI, workflow, pose search, normal reselection,
metadata mutation, or remote write was used in this review.
