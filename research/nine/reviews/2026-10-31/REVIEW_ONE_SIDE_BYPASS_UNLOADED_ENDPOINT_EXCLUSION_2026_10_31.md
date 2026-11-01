# Independent review: common-side bypass applications at two unloaded channel endpoints

Date: October 31, 2026. Reviewer: module_universal.

**Verdict: PASS at the complete stated actual-star scope.**
The full common-side application feature and its complete acute-normal
corollary are excluded. The nonacute feature without a common side,
the direct-triangle unicyclic row, and higher endpoint degrees remain
outside this result. No original status or source was changed.

## 1. Entire source and exact geometric input

The complete new manuscript was read and checked:

`ONE_SIDE_BYPASS_APPLICATIONS_EXCLUDE_TWO_UNLOADED_THREE_FORCE_CHANNEL_ENDPOINTS_2026_10_31.md`

SHA-256:
`d6e9f31560e8fb2665bb698ad1b88cddff91c27d643b64f2add190dc63cb8534`.

The complete existing `UNIT_BYPASS_NORMAL_CHANNEL.md` was retrieved
from the current branch and read through Section 4, at Git blob
`8c08b57321074c57fbbac76025883fd888994e0f`. Sections 1--2 prove the
required radius-free single side-transmitter reduction from a genuine
normal channel and an arbitrary actual unit touching both endpoints.
No degree, circle or force condition on that bypass is needed.

The review uses printed hand mathematics only. No numerical pose,
mathematical script, Lean, build or CI was used.

## 2. Exact geometry, including singleton and mean endpoints

The full `U2` force and torque equations give the original channel;
the bypass theorem makes its reserve exactly one. Its support bounds
and an attained unit displacement give `dist(A,C)=1`. The original
applications `p,q` lie in A,C and on one unit side of B, so their
distance is exactly one. They must be its two endpoints, and the
unchanged signed channel normal is `q-p`.

In the printed frame this gives

\[
B=[0,1]^2,\quad p=(0,1),\quad q=(1,1),\quad
U=[0,1]\times[v,v+1].
\]

Open-interior disjointness forces `v>=1` or `v<=-1`. The unchanged
channel means are `(0,t),(1,t)`. If either terminal's horizontal
support face were a vertex, it would force `t=v=1`, an actual
singleton vertex/vertex channel contact with a forbidden axis-endpoint
normal. Thus both endpoint frames are aligned. This deduction uses
the existing strict singleton convention explicitly; no normal is
changed after the certificate is chosen.

The lower alternative gives `t=0,v=-1` and the same forbidden aligned
singleton. In the upper alternative, each channel contact has positive
geometric side length, while its original weighted mean may still be
either endpoint. The printed deductions `0<a,c<=1` and `1<=t<=2`
follow without strengthening a mean to an interior point.

## 3. Full endpoint torque and disk span

The two original B-outward normals have the stated quadrant signs
at its two support vertices. At A, its complete three-force equation
gives

\[
f_A=(-\lambda_A\alpha-\mu,\lambda_A\beta).
\]

If `beta=0`, the actual third neighbor contains a point of x-coordinate
`-2`. If `beta>0`, the original AB support forces `a=1`, the third
application is exactly `(-1,2)`, and the full moment equation about
`p` is

\[
\lambda_A(\beta-\alpha)=\mu(2-t).
\]

Both its sign and the `t` dependence check directly. Subtracting
the vertical component from the absolute horizontal one gives
`mu(t-1)>=0`. Thus the normalized third normal has leftward component
at least `1/sqrt(2)`. The inward-support-segment fact on the actual
outside square supplies an actual point with x-coordinate at most
`-1-1/sqrt(2)`. The exact reflected complete C equation gives an actual
outside point with x-coordinate at least `2+1/sqrt(2)`.

These are genuine points of the original packing. Their horizontal
span is at least `3+sqrt(2)>2R`, a contradiction even if the two outside
neighbor labels coincide. The beta/delta zero cases and all full mean
endpoints satisfy the same conclusion. No equation at B is used.

## 4. Normal-fan corollary and remaining scope

The acute-normal support claim checks for every unit-square normal
fan. If one normal is an axis, a positive dot product puts the other
support on that same side. If neither is an axis, opposite support
vertices would give a negative dot product; identical or adjacent
vertices share a side. This includes arbitrary owned-side means.

Consequently the complete acute domain of the literal unicyclic
`(t,s)=(1,0)` row is excluded, because its two channel endpoints are
genuinely unloaded full-degree-three bodies and its one internal
transmitter is genuinely full degree two. Every surviving instance
has nonpositive bypass-normal dot product and **no single closed side
of B contains both original applications**. This last formulation is
the precise meaning of the source's phrase about different sides.

The theorem does not apply to an endpoint carrying an additional
positive force. It does not exclude the remaining orthogonal/obtuse
feature merely by continuity. Subject to these expressly retained
limits, the complete manuscript passes independent hand review.
