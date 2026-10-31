# Independent review: complete side-channel leaf-feature reduction and low/critical house-TC exclusion

Date: October 28, 2026 UTC. Reviewer: house_finish_v2, separately from
the fan_tc construction author and the root adopter.

**Verdict: PASS for the complete written local theorem, its two exact
high-radius necessary-domain reductions, and its entire original
strict-low/critical HOUSE.HUB.LTC.S conclusion. The whole original
high-radius family and the global nine-square theorem remain OPEN.**

I read all 383 lines of the target and all 2,949 lines of its nine
direct source manuscripts. This review concerns the written proofs
and complete stated scopes, not a displayed-claim comparison, a
sampled pose check, or an inference from another review. I independently
reconstructed the feature cover, norm comparisons, actual-coordinate
identities, critical-radius join, and every used degree premise.
The frozen target was not changed.

## 1. Exact target and full direct-read record

Target:

    GENUINE_S_ROOT_HIGH_SIDE_CHANNEL_COMPLETE_LEAF_FEATURE_REDUCTION.md
    SHA256 4f8da84dcc3f1fa9b8f5e231486751b134b3438905e8271f6f3484a3f10d275a
    15,961 bytes; 383 newline-terminated lines.

Every target direct pin agrees with the actual current bytes:

| Fully read source | SHA256 | Bytes / lines |
| --- | --- | --- |
| HIGH_SUPPORT_SIDE_CHANNEL_TOUCHING_RETURN_FORCES_TWO_POSITIVE_CIRCLE_CORNERS.md | 2a6f8da941de756abbea77f5c9aac75e5225968efdf278c683295b0dec900143 | 17,930 / 427 |
| SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md | 5a1607a588e45d0702c46c3d74074561f31109dccc0b8f94c665991cd4a9f5ee | 11,411 / 246 |
| ALIGNED_S_ROOT_PARALLEL_CHANNEL_TRIANGLE_EXCLUSION.md | 1b1c1572b29b110596afe25ef660b0f264b97d1910f110f287bfddeb9451465a | 20,320 / 461 |
| ALIGNED_S_ROOT_PERPENDICULAR_CHANNEL_TRIANGLE_EXCLUSION.md | 2fe9347a1f4e45653b427d1217db129faeff56e871ef0cdf4cd957c1ba654dd9 | 12,973 / 301 |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | 14,902 / 327 |
| UNIT_BYPASS_NORMAL_CHANNEL.md | db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258 | 6,573 / 186 |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | 8,686 / 226 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | 17,789 / 376 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | 17,993 / 399 |

The historical transitive pins printed inside the older parallel and
perpendicular manuscripts are not substituted for these exact current
direct pins. Their previously accepted results are used at their
literal hypotheses. This review does not rewrite historical sources
or assert a new audit of every transitive manuscript in the project.

## 2. The local theorem is force-free and its feature cover is complete

The target starts with an actual tilted unit

    A=P+[0,1]u+[0,1]v,
    P=(h,q), u=(-a,t), v=(-t,-a),
    a,t>0, a^2+t^2=1,
    |h|<=epsilon<1/60, 0<q<5/8, d=1+epsilon.

Its premise is an actual p=d e in A maximizing the actual radial
unit direction e. Neither a force balance nor a containing-circle
hypothesis is used in this local statement. For an axis direction
the maximizing face is a complete own side; for any non-axis
direction it is a unique actual vertex. These eight possibilities
exhaust the full support-feature cover, including own-side endpoints.
There is no additional sign convention between a and t.

I checked the three excluded side directions separately. The support
of -u is at most epsilon. The support of -v is bounded by |P|<2/3,
because 1/3600+25/64<4/9. The support of v is
1-h t-q a<=1+epsilon t-q a<1+epsilon. Each is strictly below d.
The remaining direction u has support d exactly when
q t-h a=epsilon. Writing b=h t+q a yields
P=epsilon u-b v; actual membership of d u in the complete side
is precisely b in[0,1]. Thus both endpoints are retained.

The initial vertex P has norm<2/3 and cannot equal d e. If the
lower adjacent vertex P+v were radially maximal, its u coordinate
would have to be on the minimum-u face. This gives

    q t<=h a<=epsilon a.

In particular h>0. If a<=q/2, then t<=epsilon/2<1/120, while
a<5/16, contradicting a^2+t^2=1. Therefore a>q/2 and

    |P+v|^2=1+h^2+q^2-2h t-2q a<1+h^2<d^2.

The case epsilon=0 had already failed h>0, so the last strict
comparison does not hide an endpoint division. This argument retained
the weak radial-support boundary q t=h a until its contradiction.

For the opposite vertex I expanded the norm independently. The
subtracted expression is bounded below by

    h^2-epsilon^2+(1-q)^2-2epsilon(1+sqrt(2))
      >9/64-5/60-1/3600=821/14400>0.

This excludes that entire feature without a partition of h, q, a,
t, epsilon or the radial normal cone. The sole remaining non-axis
feature is P+u. Its exact radius equation is

    q^2+2q t=2epsilon+epsilon^2-h^2+2h a,
    q^2<4epsilon+epsilon^2.

At epsilon=0 this is impossible, and the surviving side row would
give q t=0. Thus the local theorem's strict epsilon>0 conclusion
is proved for the whole stated feature cover.

## 3. The original high channel really supplies every local premise

The literal house graph is AT, DT, AD, AB, BC, CD, AL. Its true
degrees are A4, D3, B2, C2, T2, L1, and the positive circle loads
are exactly T, C, L. The source 5a160 proves q>0 using full B2,
C2 and D3 and the physical AT edge; no positive BD edge is assumed.
Its complete q=0 endpoint is independently present in the source,
rather than being discarded by a strict-concurrence shortcut.

The full 2a6f source preserves the actual unloaded B2 channel,
the loaded C2, the unloaded D3, all physical masks and individual
weights. Its all-normal D3 support theorem needs the actual AT
contact and both whole returned units. It gives q<5/8 and excludes
all unique physical C masks. Its Section 8 separately excludes
both possible zero-coefficient endpoints of the two-corner mask;
therefore both C weights really are positive in the target's entry.

The remaining C alternatives are exactly the aligned radial square
with h=epsilon, 0<q<=1/2, or the tilted radial square with

    h+1=d c-s/2, q=d s+c/2,
    c,s>0, c^2+s^2=1, 0<s<=4epsilon, q>1/2.

For a tilted A, its unchanged maximum-x point is the actual original
P_AB=(h,q). The genuine S-leaf application is exactly d e_L and
maximizes e_L on A, by the actual leaf theorem. Consequently every
local premise is supplied without deleting the fourth root force,
moving a channel mean, or assigning C a degree-one leaf equation.

## 4. Both high-radius coordinate reductions are complete necessary conclusions

In the tilted-C row q>1/2, while the upper-vertex alternative would
give q^2<241/3600<1/4. Thus the actual genuine leaf is forced to
the u-owned side. The two unchanged point identities

    (h+1)^2+q^2=d^2+1/4,
    h^2+q^2=epsilon^2+b^2

subtract to b^2=1/4+2(epsilon-h). Since b>=0 and h<epsilon,

    1/2<b<=sqrt(1/4+4epsilon)<5/8.

The original first coordinate gives b t=h+epsilon a<2epsilon,
so 0<t<4epsilon. These are exact necessary physical bounds on
the entire tilted-C/tilted-A row. The closed upper bounds, both
positive C coefficients and the unchanged actual mean are retained.

There is a harmless directional wording issue in the sentence after
the target's equation (17): the displayed leaf vector u=(-a,t) is
near West, whereas C's vector (c,s) is near East. They are nearly
opposite to each other, with both positive transverse components.
The formulas and every inference use these correct vectors; the
phrase that both are nearly opposite to the channel axis has no
operative mathematical role. This review does not edit frozen bytes.

For aligned C, h=epsilon. The upper-vertex equation simplifies to
q^2+2q t=2epsilon(1+a), implying
q<2sqrt(epsilon)<31/120. The exact final rational reserve is
(31/120)^2-1/15=1/14400. In the side row b^2=q^2 and b>=0,
q>0 force b=q. Solving the two actual point-coordinate equations
gives exactly

    a=(q^2-epsilon^2)/(q^2+epsilon^2),
    t=2epsilon q/(q^2+epsilon^2), epsilon<q<=1/2.

The denominators are positive; the strict lower q bound follows
from a>0. No realization is asserted for every scalar choice.
These remain necessary-domain reductions, not high-family closures.

## 5. The strict-low proof covers the entire original family

For d<1, the actual genuine root contains its radial inward unit
segment from d e_L to (d-1)e_L, hence contains O. The full actual
unloaded B2 and real physical bypass D give a side-normal channel
of reserve exactly one. In its actual outward direction the root
support h is nonnegative. Every actual point of C therefore lies
beyond support h+1>=1. The degree-free sharp support bound in
Section 1 of 20a845 requires h+1<=d<1, a contradiction.

The argument does not depend on a tilted root, a particular leaf
feature, a C mask, or positive-radius division. It retains the
whole original graph and the other three actual completion units.

## 6. The critical proof exhausts every actual root frame

At d=1 the complete high chart, including its epsilon=0 boundary,
applies. Its tilted-C row is impossible, so h=0, 0<q<=1/2 and
C=[1,2] times[-1/2,1/2]. The local theorem excludes every A tilted
relative to the channel. Hence A is channel-aligned with actual
rectangle [-1,0] times[y0,y0+1].

If its genuine radial direction were not an own axis, its radius-one
application would be a strictly exposed actual vertex. A vertex
on x=-1 can have norm one only at (-1,0), giving the own West
axis. A vertex on x=0 can have norm one only at (0,1) or (0,-1),
giving an own vertical axis. Thus every supposed non-axis alternative
contradicts itself. No assumption that O is in the open root is made.

The genuine axis is consequently parallel or perpendicular to the
actual horizontal B channel. I read both entire direct exit sources,
including the parallel source's full critical radial-C/D-frame proof
and the perpendicular source's two physical bypass alternatives.
The parallel source uses full A4 and D3 where it needs force balance,
and treats the actual two-corner C mask separately from its
unique-corner inside-concurrence argument. The perpendicular source
uses the full A4 and actual D geometry; it does not impose a D2
balance. Both include d=1, side-mean endpoints, all physical masks
and all individual circle weights. Their hypotheses are supplied
by the original house without further selection or motion.

Therefore the target proves the whole original HOUSE.HUB.LTC.S
domain 79/40<=R<=sqrt(17)/2 impossible. Strictly high radius is
the exact remaining radius domain of that original family.

## 7. Adoption boundary and retained obligations

The local feature theorem is valid at arbitrary actual root degree
once its displayed physical hypotheses are supplied. The high
house applications retain both positive C coefficients and the
unchanged original forces. The whole low/critical radius theorem
uses the genuine S leaf and the literal complete original graph.

The high-radius channel-aligned A cases, aligned-C upper-vertex
and side rows, and tilted-C side row still need complete exclusions
or an all-completion capacity argument. This source proves none of
those remaining whole branches impossible by the coordinate chart
alone. It closes no existing whole TC.S flag and retires no numerical
certificate. All nine actual units, original selected normals, true
degrees, unchanged actual applications and aggregate means, full
force and torque equations, physical circle masks and individual
zero coefficients remain part of the original problem.

This independent review is complete and passing for the exact
target above. Root adoption is separate. No Lean/Lake invocation,
CI/workflow, numerical pose search, certificate generator, source
rewrite, metadata/count edit, staging, commit or remote action was
performed in this review.
