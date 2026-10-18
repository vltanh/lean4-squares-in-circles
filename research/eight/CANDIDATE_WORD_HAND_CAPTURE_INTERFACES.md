# Hand interfaces for the surviving quarter word 0101011

## Status and purpose

This note proves three continuous interfaces needed by the candidate-word
capture: a reflection normalization, a coarse tangent-to-slider implication,
and a full-SAT cyclic-budget implication. They reduce the statements still
needed from the candidate pair inequalities. **They do not assert those
unproved global pair inequalities or close the candidate capture gate.**

All finite constants below are exact rationals. The fixed comparison file
`candidate_word_hand_interfaces_arithmetic.json` is reproduced by
`verify_candidate_word_hand_interfaces.py`; the geometric arguments and
the cyclic-budget implication are given here.

## 1. Coordinates and the reflection normalization

Use the roles

\[
 (0,1,2,3,4,5,6)=(H,G,A,B,T,D,E),\qquad
 k=(0,1,0,1,0,1,1).
\tag{1}
\]

The completed hand frame theorem puts the seven actual square frames in
one lifted interval of length less than .7. Let their real values be
\(\theta_i\), and let

\[
 \phi_i=k_i\pi/2+\theta_{i+1}-\theta_i.
\tag{2}
\]

Thus \(\sum\phi_i=2\pi\). A canonical boundary state has center
\(a_i e_i-a_i u_i f_i\), where \(-1\le u_i\le1\), and the local
canonical frame has its recorded quarter offset from the actual frame.
Relative to A's canonical frame, the offsets can be taken to be

\[
 (m_H,m_G,m_A,m_B,m_T,m_D,m_E)=(-1,-1,0,0,1,1,2).
\tag{3}
\]

Reflect the whole packing and reverse its cyclic indexing by
\(i\mapsto5-i\pmod7\). The new role list is
\((D,T,B,A,G,H,E)\), and the new quarter word is

\[
 k'_i=k_{4-i\pmod7}=(0,1,0,1,0,1,1).
\tag{4}
\]

Every signed canonical tangent changes from \(u\) to \(-u\); role E
is fixed by the indexing permutation. Consequently, after this permitted
isometry and relabeling, one may assume

\[
 u_E\le0.
\tag{5}
\]

The choice at zero is harmless: every later sign domain is closed and a
single choice is retained on both incident edges. Reflection preserves
the radial kinds, actual SAT inequalities, circle containment, frame
range and physical center-angle sum. In particular it is a normalization
of the whole candidate domain, with no contact assumption.

## 2. Coarse tangent bounds already suffice for both sliders

Suppose, in addition to (1)--(3), that

\[
 -\frac45\le u_G\le-\frac1{20},\qquad
 \frac1{20}\le u_T\le\frac45.
\tag{6}
\]

Both C and O radial kinds are allowed independently at G and T. Work
throughout the terminal radius interval
\(7831/2000\le q\le Q=9789/2500<4\).

For a core boundary state with \(|u|\le4/5<6/7\), the radius-1/12
core-avoidance boundary is its side, so
\(a=7/12\). For an outer boundary state,

\[
 (a+1/2)^2+(|u|a+1/2)^2=q.
\tag{7}
\]

The left side is strictly increasing in both nonnegative variables.
At \(a=349/250=1.396\), \(|u|=1/20\), it exceeds Q by
\(97201/25000000>0\). At \(a=7/12\), \(|u|=4/5\), it is less
than \(39/10\) by \(6451/3600>0\). Therefore both radial kinds in
(6) satisfy

\[
 \frac7{12}\le a<\frac{349}{250}.
\tag{8}
\]

Every unit square contains the radius-1/2 disk about its center. Since
the whole square is contained in a disk of radius less than 2, its center
has norm less than \(3/2\). This also proves the norm bound for the
boundary-deformed squares being used here.

Normalize \(\theta_A=0\), put \(t=\theta_G\), and define

\[
 S=|\theta_G-\theta_H|+|\theta_B-\theta_A|
   +|\theta_T-\theta_B|+|\theta_D-\theta_T|
   +|\theta_E-\theta_D|.
\tag{9}
\]

Assume \(S\le1/500\) and \(1/10\le t\le4/25\).
The A-to-T path in (9) gives \(|\theta_T|\le S\). By (3), T's
actual center is the rotation through \(\theta_T\) of
\((u_Ta_T,a_T)\). Since \(|R(\theta)v-v|\le|v||\theta|\),

\[
 |T_y-a_T|\le\frac32 S\le\frac3{1000}.
\tag{10}
\]

It follows from (8) that

\[
 \frac{29}{50}<T_y<\frac75.
\tag{11}
\]

The lower and upper reserves are respectively at least \(1/3000\)
and \(1/1000\).

For G, its actual frame is exactly t. Formula (3) gives

\[
 p_G=-u_Ga_G e_t-a_G f_t.
\tag{12}
\]

Let the stationary comparison anchor be

\[
 p_H^0=(h_1+1/2)e_t+(h_2+1/2)f_t.
\]

The completed hand stationary calculation proves
\(-29/20<h_2<-7/5\) over this full q,t interval; see
`HUMAN_BROAD_TERMINAL_ARITHMETIC.md`, Section 7 and its endpoint
brackets. Thus the actual transverse comparison coordinate is

\[
 \eta=(p_G-p_H^0-e_t)\cdot f_t=-a_G-h_2-1/2.
\tag{13}
\]

Using (8),

\[
 -\frac12<\eta<\frac{37}{100},
\tag{14}
\]

with lower and upper reserves greater than \(1/250\) and \(1/300\).
Equations (11) and (14) are exactly the broad sharp terminal's two
projected-slider hypotheses. No condition on the proximity of the other
five centers has been used.

This argument also applies before outer-radius expansion: the signed
tangents and all frames stay fixed under that expansion, and (7)--(8)
hold throughout the lower terminal radius interval. Therefore capture
at the upper radius supplies these slider interfaces at the radius where
the sharp dual must actually be applied.

## 3. A single full-SAT budget can force owners and S < 1/500

Define the frame-mismatch function

\[
 h(x)=\frac{|\sin x|+|\cos x|-1}{2}.
\tag{15}
\]

It is nonnegative and \(\pi/2\)-periodic. For
\(0\le d\le\pi/4\), it equals \((\sin d+\cos d-1)/2\), a
concave function that vanishes at zero. The endpoint chord gives

\[
 h(d)\ge d/4.
\tag{16}
\]

Indeed its endpoint slope exceeds 1/4 because
\(8(\sqrt2-1)>\pi\), already implied by \(\sqrt2>7/5\) and
\(\pi<22/7<16/5\).

Set

\[
 \beta_i=\begin{cases}1/50,&i\in\{0,2,3,4,5\},\\0,&i\in\{1,6\},\end{cases}
 \qquad \varepsilon=\frac{19}{10^6}.
\tag{17}
\]

Suppose role labels \(\ell_i\) and constants \(\gamma_i\) have the
following **whole-domain** properties:

1. For every actual retained separating axis on edge i,
   \(C_i=\phi_i-\beta_i h(\phi_i)+\ell_i-\ell_{i+1}\ge\gamma_i\).
2. For every axis outside that edge's allowed owner set,
   \(C_i\ge\gamma_i+\varepsilon\).
3. \(\sum_i\gamma_i+\varepsilon>2\pi\).

These are the still-required pair-certificate premises of this interface,
not conclusions being assumed about an arbitrary candidate cycle.
They must include both radial kinds, every permitted sign, all arc
endpoints and every feasible retained separator.

Put \(e_i=C_i-\gamma_i\). Telescoping the labels yields the exact identity

\[
 \sum_i e_i+\frac1{50}\sum_{i\in\{0,2,3,4,5\}}h(\phi_i)
 =2\pi-\sum_i\gamma_i<\varepsilon.
\tag{18}
\]

Every term on the left is nonnegative. Hence an excluded owner would
make the left side at least \(\varepsilon\), a contradiction. This
argument proves the owner restriction from a full-SAT baseline; it does
not presume the desired owners when obtaining the mismatch bound.

Because all actual frame differences have magnitude less than .7,
their absolute values are their shortest orientation-circle distances.
For the five charged edges these are precisely the five summands in S.
Equations (16) and (18) first imply

\[
 S<4\varepsilon/(1/50)=\frac{19}{5000}<\frac1{250}.
\tag{19}
\]

On \(0\le d\le1/250\), the elementary Taylor inequalities give

\[
 h(d)\ge\frac d2-\frac{d^2}4-\frac{d^3}{12}
 \ge\left(\frac12-\frac1{1000}-\frac1{750000}\right)d
 >\frac{49}{100}d.
\tag{20}
\]

At d=0 the weak inequality \(h(d)\ge(49/100)d\) is sufficient.
Applying it in (18) improves (19) to

\[
 S<\frac{\varepsilon}{(1/50)(49/100)}
  =\frac{19}{9800}<\frac1{500}.
\tag{21}
\]

Thus a total cyclic deficit below .000019 is sufficient for the
completed sharp terminal. The older computer-assisted capture's much
smaller mismatch bound is unnecessary for this route.

### The allowed owners, including all ties

In the canonical forward-pair numbering, axes 1,2,3,4 are source +f,
target +e, target +f and source -e respectively. The allowed sets are

| Edge | Ordered pair | Allowed canonical axes |
|---|---|---|
| 0 | H to G | 1, 3 |
| 1 | G to A | 1 |
| 2 | A to B | 1, 3 |
| 3 | B to T | 3, 4 |
| 4 | T to D | 1, 3 |
| 5 | D to E | 3, 4 |
| 6 | E to H | 2 |

Using (3), these are the terminal's named normals on AB, TB, DT, ED,
GA, HG and HE. There are exactly \(2^5=32\) assignments. If more
than one of an edge's allowed axes is feasible, choose any of them;
the terminal theorem includes each choice. An axis that is feasible
on a tie boundary is covered by the same closed pair inequalities.

### Tilt interface

For the uncharged edge G to A, (2) and (18) give

\[
 t=\pi/2-\gamma_1+\ell_G-\ell_A-e_1,
 \qquad 0\le e_1<\varepsilon.
\tag{22}
\]

Consequently the label-range bound

\[
 \frac1{10}+\varepsilon
 \le\pi/2-\gamma_1+\ell_G-\ell_A\le\frac4{25}
\tag{23}
\]

would supply \(1/10<t\le4/25\). A separate full-domain exclusion
of the complementary tilt intervals is an equally valid way to supply
this hypothesis. Neither alternative is counted as proved in this note.

## 4. The resulting remaining capture exits

After normalization (5), the following four complementary tangent
domains suffice to establish (6):

* \(u_G\in[-1,-4/5]\);
* \(u_G\in[-1/20,1]\);
* \(u_T\in[-1,1/20]\), after the two G exclusions;
* \(u_T\in[4/5,1]\), after the two G exclusions.

Closed bad domains are convenient because they include their equality
boundaries; excluding them gives the strict interior of (6), which is
more than is needed. These four exclusions, a full-SAT budget satisfying
Section 3, and a tilt bound satisfying (22)--(23) or an independent
equivalent are the outstanding analytic candidate work. Once supplied,
this note gives the broad slider bounds and the completed sharp terminal
applies to arbitrary anchored centers and all 32 allowed owner choices.
