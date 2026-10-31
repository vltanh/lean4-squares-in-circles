# Independent review of the exact radial-pair gap exclusion

Date: October 30, 2026. Reviewer: common-certificate continuation.

**Decision: ACCEPT at the exact scope stated in the source.** I read the
entire proposed source and all three complete direct inputs, and independently
reconstructed the geometric distance lemma, the exact angle comparisons,
the physical circular-order caller and the final integer count. There is
no outstanding mathematical objection.

## 1. Exact reviewed source and complete inputs

| Source | SHA-256 |
| --- | --- |
| ALL_RADIAL_SHORT_SEVEN_CYCLES_EXCLUDED_BY_EXACT_CENTER_GAPS_2026_10_30.md | `8da022d6dc6f432981d2f348e808f81a67fc00b95af620170117ac5e847e0e7d` |
| SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md | `5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635` |
| PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | `ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab` |
| RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | `2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e` |

The input mathematical tree is the source's declared
`3132896f3c306faecfdd69daafb0b577bf7d70a1`. The three direct inputs retain
their accepted physical-certificate and embedding prerequisites. This review
does not replace those transitive dependencies by a fresh unrestricted
certificate proof.

## 2. Physical radial classification and exact angle interval

Two actual circle corners in the stated radius window give the radial
square

\[
S_e=[d,d+1]e+[-1/2,1/2]Je,
\qquad d=\sqrt{R^2-1/4}-1.
\]

This classification is physical; it does not require both individual
circle coefficients to be positive, equal, or varied. The source correctly
excludes the opposite-corner possibility using the actual radius window.

Both rational comparisons proving \(9/10<d<61/60\) are strict at the
closed radius endpoints. With
\(\rho^2=d^2+1/4\) and \(\tan\phi=1/(2d)\), the upper bound
\(\phi<\pi/6\) follows from \(25/81<1/3\).

For the lower bound, \(d^2<25/24\) gives
\(\tan\phi>\sqrt6/5\). I independently expanded the seventh power
used in the source:

\[
7-35(6/25)+21(36/625)-216/15625=-3191/15625<0.
\]

For \(\theta=\arctan(\sqrt6/5)\), one has
\(0<7\theta<7\pi/4<2\pi\), so this negative sine forces
\(7\theta>\pi\). Consequently
\(\pi/7<\phi<\pi/6\) follows with no rounded trigonometric value
or sampled radius argument.

## 3. Exact distance of the complete radial squares

The normalized actual axes

\[
e_A=(-\sin a,\cos a),\qquad e_B=(\sin a,\cos a)
\]

describe both original physical squares by reflection. They do not move
either square or impose a symmetry on any other body.

If \(a<\phi\), the strict interval

\[
\frac d{\cos a}<h<
\min\!\left\{\frac{d+1}{\cos a},\frac1{2\sin a}\right\}
\]

is nonempty. The same point \((0,h)\) then lies in both open square
interiors. Thus physical disjointness really forces \(a\ge\phi\).

For \(\phi\le a<\pi/2\), the facing horizontal support points are
the unique inner vertices, at the common height
\(d\cos a+\tfrac12\sin a\). Every cross-square distance is at least
their nonnegative horizontal gap, and these two points attain it. Hence

\[
\operatorname{dist}(A,B)=2d\sin a-\cos a
                         =2\rho\sin(a-\phi).
\]

This argument includes the exact contact limit \(a=\phi\). At
\(a=\pi/2\), the two actual inner faces give distance \(2d\);
no face midpoint or weighted mean is selected. Since
\(a-\phi\in[0,\pi/2-\phi]\), the inverse sine formula has the
declared branch throughout the complete domain.

## 4. The whole-cycle caller supplies the actual angular gaps

Lemma N.1 of the complete parallel-transmission source uses both force
and torque on every original unloaded degree-two body. It gives equal
positive forces and an original application difference \(w n\), with
\(w=1\) or \(\sqrt2\) for one transmitter. The two endpoint support
half-planes prove that this difference attains the set distance. The
means remain the original full contact means. A direct edge gives set
distance zero.

I checked the complete force-polygon input, including its nonzero common
moment, exterior circle spokes, one-winding order and the outward-channel
half-plane conclusion. Its Sections 3--5 supply the actual consecutive
loaded-center gaps, rather than an arbitrarily chosen minor angle. This
caller includes physical two-corner loads whose concurrences are outside
their squares. It also retains individual zero circle coefficients and
physical circle contacts at unloaded transmitters.

The source correctly keeps the antipodal case in the distance lemma and
then excludes it in the channel caller: \(2d>9/5>\sqrt2\). Direct gaps
are already strictly below pi under the accepted angular-neighbor
conclusion. Thus no large-arc or endpoint branch is lost.

## 5. Simultaneous count and exact scope

The unchanged geometry gives consecutive gaps

\[
\gamma_i=2\phi+2\arcsin\frac{w_i}{2\rho}.
\]

The three original alternatives are exactly \(2\phi\) for a direct
edge, \(4\phi\) for a side transmitter, and strictly greater than
\(4\phi\) for a diagonal transmitter. The last is a necessary
inequality; the proof does not assert actual existence of a radial-pair
diagonal channel.

With \(t\) loads and \(k\) isolated unloaded bodies, there are exactly
\(t-k\) direct gaps and \(k\) positive-reserve gaps. Therefore the
actual one-winding sum yields

\[
2\pi=\sum_i\gamma_i\ge2\phi(t+k).
\]

At \(m=t+k\ge7\), the strict lower angle bound contradicts this.
If every transmitter is side normal, equality gives
\(m=\pi/\phi\in(6,7)\), impossible for every integer cycle length.
This also includes \(k=0\). The short-C7 cases with four, five and six
loads are genuine simultaneous callers of the same theorem.

All actual additional contacts and both completion squares remain
unrestricted. No canonical minimizer, movement, absence of physical
blockers, equal corner split or special side mean is assumed. The
theorem excludes the all-physical-two-corner loaded mask; mixed masks
with a unique loaded circle corner remain outside its conclusion. A
long unloaded run also remains outside the count, as the source
explicitly states.

## 6. Verification and adoption boundary

This is a complete hand review of the new source and its three direct
inputs. No numerical pose search, angle grid, Lean/Lake invocation,
computational packing certificate, CI dispatch, original ledger change
or remote write was used. The accepted conclusion is the exact
whole-mask exclusion above, not unrestricted nine-square optimality.
