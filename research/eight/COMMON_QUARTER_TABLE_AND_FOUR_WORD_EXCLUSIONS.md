# A common hand table and four complete word exclusions

The three whole-domain pair lemmas now use the same marker functions.
They therefore telescope around an arbitrary core/outer boundary cycle.
This gives a short hand exclusion of all four quarter words containing
a jump of two. The one remaining external geometric hypothesis is the
global frame-concentration conclusion stated below.

## 1. Exact hypotheses and common markers

Work at the squared-radius ceiling \(Q=9789/2500\). Apply the hand
central-core and radial-boundary reductions, and order the seven exterior
squares by their center rays. Each center lies on the core curve \(C\)
or the outer curve \(O\); no restriction on the resulting seven-letter
radial word is assumed. Every adjacent pair retains a true separating
axis, and its positive center-angle gap satisfies
\[
 \delta_i>\frac{19}{25},\qquad \sum_i\delta_i=2\pi.
\]

**Frame hypothesis.** The seven physical square frames admit lifts
\(\theta_i\) in one interval of length \(D<7/10\).

This is the conclusion of the still separate global frame gate. It is
not proved by the quarter table and must not be inferred from it.

Choose nearest-axis representatives as in SEVEN_QUARTER_WORDS.md:
\[
 \phi_i=\theta_{i+1}-\theta_i+k_i\frac\pi2,
 \qquad k_i\in\{0,1,2\},\qquad \sum_i k_i=4.
\]
The signed local center is \((a_i,-\sigma_i b_i)\), with
\(0\le b_i\le a_i\), and its signed tangent angle is
\(\alpha_i=\sigma_i\arctan(b_i/a_i)\). Thus
\[
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1}.
\]
At a nearest-axis tie either representative can be chosen; at zero
tangent either sign can be chosen. Make each choice once for the state
and use that same choice on both of its incident edges.

Put
\[
 L_O(a,b)=-\frac9{100}+\frac{13}{200}a+\frac{203}{200}b,
\qquad
 L_C(a,b)=\frac{73}{10}(\frac7{12}-a)+\frac{291}{250}b.
\]
Use the signed marker \(\ell_i=\sigma_iL_{\operatorname{kind}(i)}\).
The same constants and functions are used on every edge of every word.

## 2. The complete common table

The hand pair theorems give:

| Increment \(k_i\) | Full frame interval for \(\phi_i\) | Bound on \(\phi_i+\ell_i-\ell_{i+1}\) | Hand proof |
|---:|---|---:|---|
| 0 | \([-7/10,7/10]\) | \(>391/400=.9775\) | QUARTER_ZERO_ALL_BOUNDARY_STATES_HAND_PROOF.md |
| 1 | \([\pi/2-7/10,\pi/2+7/10]\) | \(>157/200=.785\) | QUARTER_ONE_ALL_BOUNDARY_STATES_HAND_PROOF.md |
| 2 | \([\pi-7/10,\pi+7/10]\) | \(>163/200=.815\) | QUARTER_TWO_ALL_BOUNDARY_STATES_HAND_PROOF.md |

Every row covers all four source/target boundary-type pairs, all four
tangent-sign patterns, both surviving source axes, and their reflected
reverse target axes. The common-point and backward-axis lemmas exclude
the other four signed axes. Consequently the table applies to any true
separator of an adjacent pair, including a tie between axes.

The proofs consist of fixed circle supports, endpoint concavity,
elementary trigonometric inequalities, and displayed rational comparisons.
Their optional arithmetic replays contain no adaptive search or sampled
coverage premise. The table does not select owners or impose a preferred
contact axis before proving its inequality.

## 3. Telescoping and the four exclusions

The markers telescope exactly:
\[
 \sum_i(\phi_i+\ell_i-\ell_{i+1})
 =\sum_i\phi_i=\sum_i\delta_i=2\pi.                       \tag{1}
\]
Suppose a cyclic word contains a 2. The hand word classification gives
exactly one 2, two 1s, and four 0s. The common table and (1) imply
\[
 2\pi>
 4\frac{391}{400}+2\frac{157}{200}+\frac{163}{200}
 =\frac{1259}{200}=6.295.                                 \tag{2}
\]
But \(\pi<22/7\), while
\[
 \frac{1259}{200}-\frac{44}{7}=\frac{13}{1400}>0.
\]
This contradicts (2). Therefore no such word exists. In particular the
following four entire continuous families are excluded:
\[
 0010012,\qquad0010102,\qquad0010201,\qquad0011002.
\]
The argument treats every radial assignment in \(\{C,O\}^7\), every
allowed frame and tangent, all signed separator choices, and all closed
boundary junctions. It does not require separate enumeration of the
128 radial words.

## 4. The exact remaining hand gate

Conditional on the global frame hypothesis, the seven-word theorem now
leaves only
\[
 0010111,\qquad0011011,\qquad0101011.
\]
The first two require their own global word inequalities. The candidate
word \(0101011\) requires either a direct global sharp bound or a hand
derivation of all hypotheses of HAND_EXACT_CENTER_SQUARE_COMPLETION.md.
That sharp terminal is already proved for mismatch sum \(S\le1/500\),
the stated common tilt and projected-slider ranges, arbitrary anchored
centers, and all 32 relevant owner assignments.

Thus the four exclusions above are complete hand theorems under their
explicit frame hypothesis. They do not close the unrestricted hand proof
until the frame hypothesis and the three remaining word tasks are proved.
