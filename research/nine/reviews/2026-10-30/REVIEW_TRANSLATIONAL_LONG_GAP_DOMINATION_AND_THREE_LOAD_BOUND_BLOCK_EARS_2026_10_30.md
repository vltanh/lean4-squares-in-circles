# Independent review: long-gap domination and the translational three-load bound

Date: October 30, 2026 UTC. Reviewer: block_ears.

**Verdict: PASS for the complete source, with no repair required.**
The exact frozen source is

    TRANSLATIONAL_LONG_CHANNEL_DOMINATING_PAIR_AND_THREE_LOAD_CYCLE_BOUND_2026_10_30.md
    SHA256 5b3c31c3aae5afc91cb2bbba0cabfdd9fcb6ff9f7893b5bd8673f43852a471b0
    9943 bytes

I read the entire source and reconstructed every physical, force-only,
path-count and cycle assertion. I did not author its new domination or
translational extension. I independently reviewed its expanded-square
input in full in
REVIEW_EXPANDED_ENDPOINT_COVER_AND_COMPLETE_THREE_LOAD_SEVEN_CYCLE_BLOCK_EARS_2026_10_30.md.
That separate review verifies the precise frozen geometric input

    TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md
    SHA256 78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6.

My prior independent rediscovery of the already published endpoint
matching observation is not represented as a new source or gate here.

## 1. The domination conclusion uses actual occupied squares

The expanded-square theorem places c_C strictly within distance 3/2
of A or B. Choosing a nearest actual point p of that compact square
is legitimate. If |p-c_C|<=1/2, p lies in the actual closed incircle
of C, hence in C. Otherwise the point at distance 1/2 from c_C toward
p lies in C and is strictly less than distance one from p. Thus

    dist(C,A)<1 or dist(C,B)<1.

The argument works at every threshold, including d_C=0, d_C=1/2,
and any actual weak square contact. It uses neither the frame nor any
force at C. It therefore covers all other physical units, including
units outside the chosen positive component.

The equivalence between the long support-gap hypothesis and
dist(A,B)>=2 is valid. At closest points of two disjoint compact convex
sets the displacement direction is a common separating normal, as
follows by one-sided variation along either set. Its support gap is
the actual distance. Conversely every positive support gap bounds all
pairwise distances from below. This equivalence does not prescribe
the later short-channel directions.

## 2. The path identity really needs only translational balance

At an internal body of true positive degree two with zero circle
coefficients, the two nonzero contact forces cancel. Their magnitudes
are equal and their outward signed normals are opposite. Consistently
orienting the actual path makes its signed normals equal at consecutive
edges. The full tight projection equalities therefore telescope to

    n.(c_V-c_U) = h_U(n)+h_V(n)+2 sum_internal h_i(n).

No angular stationarity or contact application point appears in this
calculation. The width of each original independently tilted unit is
only bounded below by one. The source correctly refrains from asserting
the discrete physical-torque alternatives one and sqrt(2) in this
translational setting.

The exact center bound |c|<M=91/60 gives endpoint projection less than
2M=91/30. Three internal bodies would give projection at least four,
so every actual retained path has at most two internal bodies. A
closed path of this type has zero telescoped displacement but strictly
positive summed widths, and is impossible. Different genuine paths
with the same endpoint pair remain permitted.

The word unloaded refers to zero circle coefficients; the proof does
not infer that a body is physically circle-clear merely because its
coefficients vanish. It also does not turn a higher-degree body into
a transmitter by dropping a positive force. Both distinctions are
preserved throughout.

## 3. The full matching argument and its parallel-path boundary

The source repeats the purely geometric proof of the previously
accepted matching theorem. If b=(r,0) has two partners at distance at
least three, then r>=3-|a|>3-M>0. The function

    (M^2+r^2-9)/(2r)

has derivative 1/2+(9-M^2)/(2r^2)>0. Thus both partner centers have
x<-7919/5460<-29/20. They lie in the same open disk centered at
(-29/20,0), of squared radius 89/450, so their squared separation
is below 178/225<1. This contradicts the two disjoint open radius-1/2
incircles.

I independently rechecked the exact identities

    7919/5460-29/20 = 1/2730,
    M^2-(29/20)^2 = 89/450,
    4(89/450) = 178/225.

An actual two-internal-body path gives center distance at least three
by the force-only identity. Hence the **distinct endpoint pairs** of
such paths form a matching. The target expressly retains parallel
paths between the same endpoint pair. It does not mistakenly assert
a matching of individual multigraph edges.

## 4. The forbidden triangle retains arbitrary full endpoint stars

For three distinct retained endpoints with actual internal counts at
least 2,1,1, the path identities give a gap at least two for AB and
at least one for AC and BC. The latter two inequalities imply
dist(A,C)>=1 and dist(B,C)>=1 by projection. These contradict the
physical domination theorem.

All other forces at A,B,C are irrelevant to these three path identities
and remain in the original system. The endpoints may be loaded or
unloaded, may have arbitrary degree, and may be articulations of other
blocks. No endpoint is assigned a two-force equation. Only the genuine
internal path bodies require true positive degree two and zero circle
coefficients.

Suppressing these paths changes only the notation. The squares, their
actual widths, all other physical contacts and all remaining units are
retained. Neither a planar drawing nor torque balance enters the
contradiction. This is a valid new consequence for the translational
certificate independently of the separately selected physical torque
certificate.

## 5. The full simple-cycle conclusion is exhaustive

In an entire positive simple cycle with exactly three positive
circle-loaded bodies, every other body is unloaded of true degree two.
The three loads split the cycle into three maximal unloaded runs with
counts k_1,k_2,k_3 in {0,1,2}. Their endpoint pairs are distinct.

Two counts equal to two would share a loaded endpoint but have distinct
other endpoints, contradicting the preceding matching theorem. At
most one run has size two, so the sum is at most four. A component
with at least seven bodies must then have exactly seven and counts
(2,1,1), which the new translational triangle theorem excludes. This
proves the complete bound of at most six bodies.

The proof includes all actual widths, orientations, original separator
normal choices and physical circle contacts with zero coefficients.
The application to seven, eight and nine bodies is one common argument.
The eight- and nine-body consequences are correctly identified as
previously known; the seven-body exit is the new geometric contribution.
No six-body conclusion is inferred from this source.

## 6. Final scope and dependency audit

The only new geometric input is the frozen expanded-square cover,
whose complete separate review is named above. The matching proof is
reconstructed directly here; its existing published source is

    LONG_CHANNEL_ENDPOINT_MATCHING.md
    SHA256 38fa41694cc24fcbe7ac13bc64481323117bcf9d283832a9ec95049cc265cf59.

SPARSE_MINIMIZER_STRESS.md is cited in the target only as an example
of a standard certificate satisfying its explicit hypotheses. No
unstated property of that source is used to derive the present
conditional theorem. In particular no simultaneous angular/planar
selection or generic shared-mean identity is assumed.

The exact seven-core equality packing is not a three-load simple
cycle, so the theorem makes no false claim to exclude it. The closed
radius endpoint Q and all weak gap hypotheses were retained by the
strict expanded cover. A general large block need not contain the
forbidden retained triangle, and the target states that limitation.

I approve the complete source at these exact scopes. This review
changes no original count or checklist and proves neither the full
n=9 lower bound nor equality classification. No Lean compilation,
CI, numerical pose search, mesh, packing certificate or remote write
was performed.
