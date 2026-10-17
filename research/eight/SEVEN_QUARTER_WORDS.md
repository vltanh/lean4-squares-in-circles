# Seven whole-domain quarter-increment words

This is a hand reduction of the global capture problem. It assumes the
separate frame-concentration conclusion that all seven physical square
frames have lifts in one interval of length less than (7/10). It does
not assume any of the 123 numerical role-domain exclusions.

Under that one frame hypothesis, a physical exterior seven-cycle has one
of the seven integer words in Section 3. The six noncandidate words still
require exclusion; the candidate word still requires a sharp geometric
argument. Those later steps are not claimed here.

## 1. A slightly stronger common-point lemma

In `COMMON_POINT_AND_THREE_QUARTER_ANGLE.md`, replace (h=3/8) by

\[
h=19/50,
\qquad \lambda=103/100.
\]

The proof is unchanged. The elementary trigonometric bounds are

\[
\frac{9286}{10000}<\cos h<\frac{9287}{10000},
\qquad \sin h<\frac{371}{1000}.
\]

They follow from the cosine series through degrees six and eight and the
sine series through degree nine. Use the polynomial notation from
`CENTRAL_BAND_COMMON_POINT_LEMMAS.md`, with

\[
A=5/9,\quad C_-=(103/100)(9286/10000),\quad
C_+=(103/100)(9287/10000),\quad D=(103/100)(371/1000).
\]

The complete replacement Bernstein table is as follows. Each entry divided
by (10^6) is a lower bound for a coefficient in the indicated interval.

| Polynomial | Interval | Lower coefficient numerators, denominator (10^6) |
|---|---|---|
| (P) | ([0,1/2]) | 162127, 155663, 147423, 113496, 58204, 18515, 11198 |
| (P) | ([1/2,1]) | 11198, 3882, 28939, 103141, 223065, 312256, 111146 |
| (V) | ([0,3/14]) | 117870, 74905, 37789, 13961, 9001 |
| (V) | ([3/14,3/7]) | 9001, 4041, 17949, 56303, 122825 |

All entries are positive. These four fixed rows prove that the point

\[
(103/100,0)
\]

lies in the interior of every square avoiding the open radius-(1/12)
core whose center ray belongs to the closed angle sector ([-19/50,19/50]).
The only core estimate used is

\[
a\ge1/2+1/(12\sqrt2)>5/9.
\]

Thus disjoint neighboring squares have smaller center angle greater than

\[
2h=19/25.
\]

If the seven consecutive gaps sum to (2\pi), each consequently satisfies

\[
\frac{19}{25}<\delta_i<2\pi-\frac{114}{25}. \tag{1}
\]

This argument needs disjoint interiors only for neighboring pairs. It
therefore applies to the adjacent-pair representatives used in the radial
boundary reduction. The exact arithmetic for the four rows is included in
`central_band_polynomials.py` under `strong_exterior`.

## 2. Integer quarter increments

Write \(L=\pi/2\). Choose increasing center-angle lifts \(\beta_i\), with
\(\beta_{i+7}=\beta_i+2\pi\), and physical square-frame lifts

\[
\theta_i\in[J,J+D],\qquad D<7/10,\qquad \theta_{i+7}=\theta_i.
\]

For every (i), select a nearest square axis to the center ray. Equivalently,
choose (m_i\in\mathbb Z) and (alpha_i\in[-\pi/4,\pi/4]) such that

\[
\beta_i+\alpha_i=\theta_i+m_iL.
\]

The endpoint tie between two nearest axes can be resolved in either way.
Choose the periodic extension with (m_{i+7}=m_i+4). Set

\[
k_i=m_{i+1}-m_i,\qquad
\epsilon_i=\theta_{i+1}-\theta_i.
\]

Then

\[
\delta_i=\epsilon_i+k_iL+\alpha_i-\alpha_{i+1},
\qquad \sum_{i=0}^6k_i=4. \tag{2}
\]

If (k_i\le-1), then (2) gives (delta_i<D<7/10), contradicting
(1). If (k_i\ge3), then

\[
\delta_i>\pi-7/10>2\pi-114/25,
\]

again contradicting (1). The second strict inequality follows already from
\(\pi<22/7<193/50\). Therefore

\[
k_i\in\{0,1,2\}. \tag{3}
\]

Three consecutive zeros are impossible. If (k_i=k_{i+1}=k_{i+2}=0),
telescoping (2) gives

\[
\delta_i+\delta_{i+1}+\delta_{i+2}
 =\theta_{i+3}-\theta_i+\alpha_i-\alpha_{i+3}
 <\frac7{10}+\frac\pi2
 <\frac{159}{70}<\frac{57}{25},
\]

whereas (1) makes the sum greater than (57/25). Hence

\[
\text{the cyclic word contains no }000. \tag{4}
\]

There cannot be two entries equal to 2: their sum already accounts for 4,
so the other five entries would be zero. The two 2s divide the five zeros
into two cyclic runs, one of length at least three, contradicting (4).

## 3. The entire finite list

Conditions (2)--(4) leave precisely the following seven words, up to cyclic
rotation and plane reflection combined with reversal of the center order:

| Word | Number of entries equal to 2 | Status in the hand reduction |
|---|---:|---|
| (0010012) | 1 | Requires exclusion |
| (0010102) | 1 | Requires exclusion |
| (0010201) | 1 | Requires exclusion |
| (0011002) | 1 | Requires exclusion |
| (0010111) | 0 | Requires exclusion |
| (0011011) | 0 | Requires exclusion |
| (0101011) | 0 | Contains the proposed optimum |

Here is a direct enumeration without a search. If there is no 2, the word
contains four 1s and three 0s. The zero runs in the four gaps between 1s
have lengths at most two and sum three. Their multisets are therefore

\[
(1,1,1,0)\quad\text{or}\quad(2,1,0,0).
\]

The first has one dihedral arrangement; the second has two, according as
the entries 2 and 1 are adjacent or opposite. This yields three words.
If there is one 2, there are two 1s and four 0s. The three zero runs have
multisets

\[
(2,2,0)\quad\text{or}\quad(2,1,1).
\]

For either multiset the exceptional run may be the run between the two 1s
or a run touching the unique 2. Reflection identifies the two latter
choices. This yields four words.

For the candidate word (0101011), a direct named-role convention is

\[
(H,G,A,B,T,D,E),\qquad (m_0,\ldots,m_6)=(0,0,1,1,2,2,3).
\]

Thus its three double primary sectors are (HG,AB,TD), with (E) alone.
Its nominal mixed-frame edges are (G\to A) and (E\to H). At the four
radial endpoints its boundary kinds are

\[
(O,\operatorname{kind}(G),O,O,\operatorname{kind}(T),O,O),
\]

where each of (G,T) may be on the core or outer boundary.

## 4. A useful exact charge for proving word inequalities

This identity provides additional whole-cycle information beyond the
separate edge bounds (|\epsilon_i|<7/10). For any real edge numbers
\(\nu_0,\ldots,\nu_6\), summation by parts gives

\[
\sum_i\nu_i\epsilon_i
 =\sum_i(\nu_{i-1}-\nu_i)\theta_i.
\]

Subtract the midpoint of the common frame interval from every \(\theta_i\).
The coefficients sum to zero, so

\[
\left|\sum_i\nu_i\epsilon_i\right|
 \le\frac D2\sum_i|\nu_i-\nu_{i-1}|
 <\frac7{20}\sum_i|\nu_i-\nu_{i-1}|. \tag{5}
\]

Suppose continuous pair inequalities for a fixed word give

\[
\delta_i-\nu_i\epsilon_i
 +\psi_{i+1}(s_{i+1})-\psi_i(s_i)\ge\gamma_i,
\]

where (s_i) is the full radial state. Their sum and (5) imply

\[
2\pi\ge\sum_i\gamma_i-
\frac7{20}\sum_i|\nu_i-\nu_{i-1}|. \tag{6}
\]

For geometric markers (psi_i=\alpha_i-\ell_i), set

\[
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i
       =\epsilon_i+k_iL.
\]

The pair cost becomes

\[
(1-\nu_i)\phi_i+\nu_i k_iL
+\ell_i(s_i)-\ell_{i+1}(s_{i+1}). \tag{7}
\]

Thus affine marker functions in the local center coordinates retain the
one-dimensional frame-angle support-function reduction: both state
variables can be eliminated by circular-arc support bounds. Equations
(5)--(7) are exact identities. Any numerical fit of their coefficients is
only a discovery aid until the resulting continuous pair inequalities have
an independent hand proof.
