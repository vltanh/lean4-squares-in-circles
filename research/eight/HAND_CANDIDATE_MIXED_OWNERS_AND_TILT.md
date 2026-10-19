# Conditional hand capture of all candidate owners and the common tilt

## 1. Three precise conclusions

This note completes the conditional owner and tilt interface. It does not
assume that the global mismatch argument has already reached the thresholds
below. Its first conclusion also strengthens the earlier quarter-owner
theorem from (S\le1/500) to (S\le3/200).

Use the candidate cyclic roles and quarter increments

\[
(H,G,A,B,T,D,E)=(0,1,2,3,4,5,6),\qquad
k=(0,1,0,1,0,1,1).
\tag{1}
\]

Let the real frame lifts have total range less than (7/10), normalize
(\theta_A=0), and put (t=\theta_G). Thus (|t|<7/10).
For the five edges (I=\{0,2,3,4,5\}), put

\[
d_i=\theta_{i+1}-\theta_i,\qquad S=\sum_{i\in I}|d_i|.
\tag{2}
\]

Each unit square avoids the open radius-(1/12) disk, lies in a centered
disk of squared radius (q), and is separated from its two cyclic
neighbors. Assume the following closed signed-tangent bounds:

\[
\begin{array}{c|rrrrrrr}
\text{role}&H&G&A&B&T&D&E\\ \hline
u\text{ interval}&[1/2,1]&[-4/5,-1/20]&[0,1]&[-1,0]&
[1/20,4/5]&[-1,-1/2]&[-1,0].
\end{array}
\tag{3}
\]

The independent hand cuts and the mismatch sign lemma provide these bounds
in the intended application. For this note they are explicit hypotheses.
All centers satisfying them are included; a center need not lie on either
radial boundary curve.

Write

\[
Q_0=\frac{9789}{2500},\qquad
Q_1=\frac{1957767069}{500000000}=3.915534138.
\tag{4}
\]

The three conclusions are:

| Hypotheses in addition to (1)–(3) | Conclusion |
|---|---|
| (q\le Q_0, S\le3/200) | Every feasible retained canonical separator on B→T and D→E is axis 3 or 4. |
| (q\le Q_0, S\le1/10000) | Every feasible retained canonical separator on G→A is axis 1; on E→H it is axis 2. |
| (q\le Q_1, S\le1/100000) | All seven intended owner sets hold, and (1/10<t<4/25). |

The full intended owner sets, in cyclic order, are

\[
\boxed{
\{1,3\},\ \{1\},\ \{1,3\},\ \{3,4\},\
\{1,3\},\ \{3,4\},\ \{2\}.}
\tag{5}
\]

The zero-quarter edges H→G, A→B and T→D already have only axes 1 or 3
by `HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md`, which applies at all three
thresholds. As in the earlier quarter-owner proof, axes mean the four
retained forward axes of the hand angular reduction: source +f,
target +e, target +f, source −e, respectively.

All exclusions are strict. They exclude a forbidden feasible axis even if
another axis on the same pair also separates. This point is useful for
pulling the owners back through a deformation that preserves each initially
selected separator.

The last line and the automatic-slider terminal give a complete conditional
sharp theorem: once (S\le1/100000) is reached under (1)–(4), the original
five-anchor square-completion inequality applies and gives (q\ge q_*).
Its equality implications remain unchanged. This note does not assert a
new global mismatch bound.

## 2. Coordinates and the stronger bounds for G and T

In each canonical own frame write the center as

\[
(a_i,-\sigma_i b_i),\qquad
\sigma=(+,-,+,-,+,-,-),\qquad a_i\ge b_i\ge0.
\tag{6}
\]

At a zero tangent either sign describes the same center. Containment gives

\[
(a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_0.
\tag{7}
\]

The distance from the origin to the square is

\[
\sqrt{(a_i-1/2)_+^2+(b_i-1/2)_+^2}\ge1/12.
\tag{8}
\]

Equations (7)–(8) imply the weak bounds

\[
\frac{447}{800}\le a_i\le\frac{283}{200},\qquad
0\le b_i\le\frac9{10}.
\tag{9}
\]

Indeed, (8) is at most (\sqrt2(a_i-1/2)_+), so
(a_i\ge1/2+\sqrt2/24>447/800). The inequalities
(\sqrt2>141/100),
((283/200+1/2)^2+1/4>Q_0), and
(2(9/10+1/2)^2>Q_0) prove the remaining assertions directly by
squaring. The proof uses only the weak versions in (9).

For G and T, (3) strengthens (9) to

\[
\boxed{\frac7{12}\le a_G,a_T\le\frac{349}{250}.}
\tag{10}
\]

For the lower bound, if (a<7/12), then (b\le(4/5)a<1/2),
and (8) reduces to ((a-1/2)_+<1/12), a contradiction.
For the upper bound use (b\ge a/20) in (7). The increasing expression
((a+1/2)^2+(a/20+1/2)^2) already exceeds (Q_0) at
(a=349/250). This proves (10) for every center, including core-corner
centers, without any assumed radial equality.

Let (r_i^-,r_i^+) be the lower and upper bounds for (b_i/a_i):

\[
r^-=(1/2,1/20,0,0,1/20,1/2,0),\qquad
r^+=(1,4/5,1,1,4/5,1,1).
\tag{11}
\]

Order the variables as (x=(a_0,\ldots,a_6,b_0,\ldots,b_6)).
For each role take, in the stated order, the five linear inequalities

\[
a_i\ge l_i,\quad -a_i\ge-h_i,\quad
b_i-r_i^-a_i\ge0,\quad r_i^+a_i-b_i\ge0,\quad -b_i\ge-9/10,
\tag{12}
\]

where (l_i=7/12,h_i=349/250) for G and T, and
(l_i=447/800,h_i=283/200) for the other roles. Denote these 35 rows by
(K_j\cdot x\ge v_j), (0\le j<35).

## 3. Necessary nominal separating inequalities

For a source ((a,-\sigma b)), target ((A,-\tau B)), and relative
canonical frame angle (\phi), the four forward projections are

\[
\begin{aligned}
F_1&=\sigma b+A\sin\phi-\tau B\cos\phi,\\
F_2&=-a\cos\phi+\sigma b\sin\phi+A,\\
F_3&=a\sin\phi+\sigma b\cos\phi-\tau B,\\
F_4&=a-A\cos\phi-\tau B\sin\phi.
\end{aligned}
\tag{13}
\]

A feasible separator has (F_j\ge W(\phi)), where

\[
W(\phi)=\frac{1+|\sin\phi|+|\cos\phi|}{2}.
\tag{14}
\]

Every actual center has norm less than (3/2): its radius-(1/2)
incircle lies in the containing disk, whose radius is less than 2.
Changing (\phi) rotates only one center in each line of (13). Therefore

\[
|F_j(\phi+v)-F_j(\phi)|\le\tfrac32|v|.
\tag{15}
\]

Also (W\ge1), and (W) is globally (1/2)-Lipschitz. Its derivative
on each quadrant has magnitude at most (1/2); continuity extends the
same bound across the quadrant endpoints.

For any declared upper bound (S\le\varepsilon), replace the five
aligned canonical angles by (k_i\pi/2). A necessary inequality is

\[
F_i^{\rm nom}\ge1-\tfrac32\varepsilon\qquad(i\in I).
\tag{16}
\]

G→A has the exact angle (\pi/2-t). The last edge has angle

\[
\phi_{EH}=\pi/2+t-(d_0+d_2+d_3+d_4+d_5).
\tag{17}
\]

Consequently its error has magnitude at most (\varepsilon), and

\[
F_{GA}^{\rm nom}\ge W_t,\qquad
F_{EH}^{\rm nom}\ge W_t-2\varepsilon,\qquad
W_t=\frac{1+\cos t+|\sin t|}{2}.
\tag{18}
\]

Using the separate weaker losses in (16)–(18) is legitimate: every
configuration with the shared total mismatch bound satisfies all of them.
No inference in the opposite direction is needed.

Write (s=\sin t,c=\cos t). The zero-quarter nominal projections are
(b_H+b_G,b_A+b_B,b_T+b_D), independently of the retained owner 1 or 3.
The two other aligned edges have these nominal values:

| Edge | Axes 1 and 2 | Axes 3 and 4 |
|---|---|---|
| B→T | (a_T-b_B) | (a_B-b_T) |
| D→E | (a_E-b_D) | (a_D+b_E) |

Thus their two nominal classes may be represented by index 1 or 3. The
mixed projections retain their distinct indices:

| Axis | G→A | E→H |
|---|---|---|
| 1 | (-b_G+a_Ac-b_As) | (-b_E+a_Hc+b_Hs) |
| 2 | (-a_Gs-b_Gc+a_A) | (a_Es-b_Ec+a_H) |
| 3 | (a_Gc-b_Gs-b_A) | (a_Ec+b_Es-b_H) |
| 4 | (a_G-a_As-b_Ac) | (a_E+a_Hs-b_Hc) |

## 4. A positive circle dual eliminates every center simultaneously

For a nominal owner pattern let its seven necessary rows be
(f_i(t)\cdot x\ge w_i(t)), as in (16)–(18). Choose fixed nonnegative
rational multipliers (\lambda_i,\kappa_j) and positive rational
(\mu_i). Set

\[
C(t)=\sum_{i=0}^6\lambda_i f_i(t)+\sum_{j=0}^{34}\kappa_jK_j,
\qquad
L(t)=\sum_i\lambda_iw_i(t)+\sum_j\kappa_jv_j+
\frac12\sum_{r=0}^{13}C_r(t).
\tag{19}
\]

Adding the necessary inequalities and completing a square gives

\[
\begin{aligned}
L(t)
&\le\sum_{i=0}^6(C_{a_i},C_{b_i})\cdot(a_i+1/2,b_i+1/2)\\
&\le Q\sum_{i=0}^6\mu_i+
\sum_{i=0}^6\frac{C_{a_i}(t)^2+C_{b_i}(t)^2}{4\mu_i}.
\end{aligned}
\tag{20}
\]

The second inequality is just
(C\cdot y\le\mu|y|^2+|C|^2/(4\mu)), followed by (7).
It does not require a sign restriction on the coordinates of (C).
Thus a strict reverse of (20) excludes the chosen owner pattern for
all admissible centers at once.

## 5. The fixed rational polynomials and their complete cover

Put

\[
z=\tan(t/2),\quad D=1+z^2,\quad
s=\frac{2z}{D},\quad c=\frac{1-z^2}{D}.
\tag{21}
\]

On a closed interval with a fixed sign of (z), every entry of (C)
and (L) has numerator of degree at most two over the denominator (D).
Let these numerator polynomials be (\widehat C,widehat L). The reverse
of (20) is equivalent to positivity of the quartic

\[
P(z)=D\widehat L(z)-Q D^2\sum_i\mu_i-
\sum_i\frac{\widehat C_{a_i}(z)^2+
                  \widehat C_{b_i}(z)^2}{4\mu_i}.
\tag{22}
\]

The half-angle range is covered by ([-3/8,3/8]), since

\[
\arctan(3/8)\ge3/8-(3/8)^3/3>7/20.
\tag{23}
\]

The complete finite constants are supplied in the three data files below.
Every row gives an owner pattern, exact rational endpoints ([l,r]),
seven nonnegative integer numerators for (\lambda), the nonzero indexed
integer numerators for the 35 cone multipliers, and seven positive integer
numerators for (\mu). All these weights have denominator (10^8).
The final five positive integers are lower bounds for the Bernstein
coefficients of (22), with denominator (10^{12}).

For completeness, if (P(z)=\sum_{n=0}^4p_nz^n), define

\[
q_j=\sum_{n=j}^4p_n{n\choose j}l^{n-j}(r-l)^j,
\qquad
B_i=\sum_{j=0}^i q_j\frac{{i\choose j}}{{4\choose j}}.
\tag{24}
\]

Then, for (v=(z-l)/(r-l)\in[0,1]),

\[
P(z)=\sum_{i=0}^4 B_i{4\choose i}v^i(1-v)^{4-i}.
\tag{25}
\]

Every (B_i) is at least its supplied strictly positive lower bound.
The nonnegative basis in (25) sums to one. Hence every supplied row
proves (P>0) on its entire closed interval, including both endpoints.
This is a finite rational polynomial proof, not an inference from sampled
states or a numerical optimization.

| Data file | (Q) | (\varepsilon) | Owner patterns | Quartics | Positive coefficients |
|---|---:|---:|---:|---:|---:|
| `candidate_quarter_owner_large_mismatch_dual_data.json` | (Q_0) | (3/200) | 48 | 1,545 | 7,725 |
| `candidate_mixed_owner_dual_data.json` | (Q_0) | (1/10000) | 15 | 561 | 2,805 |
| `candidate_tilt_dual_data.json` | (Q_1) | (1/100000) | 1 | 83 | 415 |

The standalone companion `verify_candidate_mixed_owner_and_tilt_duals.py`
reconstructs (12)–(25) using rational arithmetic. For each pattern it sorts
the supplied closed intervals and verifies that every successive left
endpoint equals the preceding right endpoint. It also checks both outer
endpoints and rejects duplicates, overlaps, missing intervals, missing
patterns, or any nonpositive coefficient. Its three reports bind the exact
source and data hashes. It neither chooses nor subdivides a cell, and it
imports no other proof program.

## 6. Exhaustion of the three alternatives

For the quarter theorem, the exact pattern set is

\[
\mathcal P_Q=\{(1,g,1,b,1,d,h):
g,h\in\{1,2,3,4\},\ b,d\in\{1,3\},\ (b,d)\ne(3,3)\}.
\tag{26}
\]

It contains 48 patterns. Each has a closed cover of ([-3/8,3/8]).
If a forbidden B→T or D→E separator existed, select that separator and
any feasible separator on the other edges. Nominally identify the two
classes on each aligned edge as in Section 3. The resulting pattern lies
in (26), which (20)–(25) exclude. This proves the first line of Section 1.

At (S\le1/10000) the first line already applies. The only mixed
alternative to the desired pair is represented by

\[
\mathcal P_M=\{(1,g,1,3,1,3,h):
g,h\in\{1,2,3,4\},\ (g,h)\ne(1,2)\}.
\tag{27}
\]

There are 15 such patterns; each again has a closed cover of
([-3/8,3/8]). Choosing any putative forbidden feasible mixed separator
would produce one of them. This proves the second line, including owner
ties.

At (S\le1/100000, q\le Q_1<Q_0), both owner conclusions apply.
The nominal pattern is therefore ((1,1,1,3,1,3,2)). Its final table
has exactly the two closed covers

\[
[-3/8,1001/20000],\qquad[2/25,3/8].
\tag{28}
\]

It follows that (1001/20000<z<2/25). Elementary arctangent bounds give

\[
2\left(\frac{1001}{20000}-\frac13
\left(\frac{1001}{20000}\right)^3\right)>\frac1{10},
\qquad
2\arctan(2/25)<2(2/25)=\frac4{25}.
\tag{29}
\]

Hence (1/10<t<4/25), proving the third line.

All inequalities excluding alternative owners or the tilt tails are
strict. Equality in the global radius theorem therefore reaches the same
intended owner family and interior tilt chart; the five anchored centers,
two exterior sliders and central-square freedom are classified by the
separate exact square-completion and equality-domain theorems.
