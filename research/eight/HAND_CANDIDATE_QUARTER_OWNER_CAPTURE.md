# Conditional hand capture of the two aligned quarter owners

## 1. Statement and scope

Let the seven exterior squares have the candidate cyclic order

\[
(H,G,A,B,T,D,E)=(0,1,2,3,4,5,6),\qquad
k=(0,1,0,1,0,1,1).
\tag{1}
\]

Use the real frame lifts supplied by the hand frame-concentration theorem,
normalize \(\theta_A=0\), and put \(t=\theta_G\). Thus \(|t|<7/10\).
Write

\[
d_i=\theta_{i+1}-\theta_i,\qquad
I=\{0,2,3,4,5\},\qquad S=\sum_{i\in I}|d_i|.
\tag{2}
\]

This theorem has the following **explicit conditional hypotheses**:

\[
\begin{gathered}
q\le Q=9789/2500,\qquad S\le1/500,\\
\tfrac12\le u_H\le1,\quad
-\tfrac45\le u_G\le-\tfrac1{20},\quad
0\le u_A\le1,\quad -1\le u_B\le0,\\
\tfrac1{20}\le u_T\le\tfrac45,\quad
-1\le u_D\le-\tfrac12,\quad -1\le u_E\le0.
\end{gathered}
\tag{3}
\]

Each square avoids the open radius-\(1/12\) disk, is contained in the
centered radius-\(\sqrt q\) disk, and is separated from both cyclic
neighbors by the true square separating-axis theorem. Neither radial-boundary
membership nor a contact equality is assumed. In particular every independent
assignment of C and O radial types is included.

**Conclusion.** On both B→T and D→E, every feasible retained canonical
separator is axis 3 or axis 4. The three zero-quarter edges H→G, A→B and
T→D already have only axes 1 or 3 by
`HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md`. Together these statements leave
exactly

\[
\boxed{\quad
\{1,3\},\quad\{1,2,3,4\},\quad\{1,3\},\quad\{3,4\},
\quad\{1,3\},\quad\{3,4\},\quad\{1,2,3,4\}.
\quad}
\tag{4}
\]

The two mixed-owner restrictions and the final tilt interval are not asserted
here. Nor does this theorem supply the still-required global bound on S.
The strict contradiction below includes all boundary and owner-tie cases,
so a forbidden axis cannot remain feasible even when another axis also
separates.

The proof consists of the elementary continuous reduction in Sections 2–5
and a fixed rational quartic table. The complete table is
`candidate_quarter_owner_circle_dual_hand_data.json`; its supplied constants
are checked by the standalone Fraction-only
`verify_candidate_quarter_owner_circle_duals.py`. The table has 1,440
quartics and 7,200 strictly positive Bernstein coefficients. Its verifier
does not search, optimize, sample states, bisect an interval, or call any
other proof program.

## 2. Unsigned coordinates and valid linear cuts

In its own canonical frame, write square i's center as

\[
(a_i,-\sigma_i b_i),\qquad
\sigma=(+,-,+,-,+,-,-),\qquad a_i\ge b_i\ge0.
\tag{5}
\]

Choosing the displayed sign at a zero tangent has no effect on the center
or any formula. The circle condition is exactly

\[
(a_i+1/2)^2+(b_i+1/2)^2\le Q.
\tag{6}
\]

Core avoidance and containment give the already proved bounds

\[
\frac{447}{800}<a_i<\frac{283}{200},\qquad b_i<\frac9{10}.
\tag{7}
\]

For clarity, core avoidance implies
\(a_i\ge1/2+\sqrt2/24>447/800\). Setting \(b_i=0\) in (6)
excludes \(a_i\ge283/200\); setting \(a_i\ge b_i\) excludes
\(b_i\ge9/10\). The proof will use only their weak versions.

The lower and upper bounds on \(b_i/a_i\) in (3) are

| Role | \(r_i^-\) | \(r_i^+\) |
|---|---:|---:|
| H | 1/2 | 1 |
| G | 1/20 | 4/5 |
| A | 0 | 1 |
| B | 0 | 1 |
| T | 1/20 | 4/5 |
| D | 1/2 | 1 |
| E | 0 | 1 |

Order the fourteen real variables as
\(x=(a_0,\ldots,a_6,b_0,\ldots,b_6)\). The fixed table uses the
following 35 linear inequalities, in this order for each successive role:

\[
\begin{array}{rlrl}
a_i&\ge447/800,&-a_i&\ge-283/200,\\
b_i-r_i^-a_i&\ge0,&r_i^+a_i-b_i&\ge0,\\
-b_i&\ge-9/10.&&
\end{array}
\tag{8}
\]

Denote them by \(K_j\cdot x\ge v_j\), \(0\le j<35\).
Every one is necessary for (3), (6); adding them in a nonnegative linear
combination is therefore valid.

## 3. A nominal separating inequality with an explicit error

For a forward pair, axes 1, 2, 3, 4 are source +f, target +e, target +f,
source −e. With relative canonical frame \(\phi\), their projections are

\[
\begin{aligned}
F_1&=\sigma b+A\sin\phi-\tau B\cos\phi,\\
F_2&=-a\cos\phi+\sigma b\sin\phi+A,\\
F_3&=a\sin\phi+\sigma b\cos\phi-\tau B,\\
F_4&=a-A\cos\phi-\tau B\sin\phi.
\end{aligned}
\tag{9}
\]

An actual separator satisfies
\(F_j\ge W(\phi)=(1+|\sin\phi|+|\cos\phi|)/2\).
In each expression (9), only one center is rotated when \(\phi\)
changes. Every center has norm less than \(3/2\): its radius-\(1/2\)
incircle lies in a containing disk of radius less than 2. Consequently,

\[
|F_j(\phi+v)-F_j(\phi)|\le\frac32|v|.
\tag{10}
\]

Also W is globally \(1/2\)-Lipschitz. On every quadrant its derivative
has magnitude at most \(1/2\), and the same bound passes across the
finitely many quadrant junctions.

For each aligned edge \(i\in I\), replace \(\phi_i=k_i\pi/2+d_i\)
by its nominal value \(k_i\pi/2\). Since the actual W is at least 1,
any actual separator implies

\[
F_i^{\rm nom}\ge1-\frac32|d_i|\ge\frac{997}{1000}.
\tag{11}
\]

For G→A, the relative angle is exactly \(\pi/2-t\), with no error.
For E→H it is

\[
\pi/2+t-(d_0+d_2+d_3+d_4+d_5).
\tag{12}
\]

The perturbation in (12) has magnitude at most S. Equations (10) and
the Lipschitz bound on W therefore give

\[
F_{GA}^{\rm nom}\ge W_t,\qquad
F_{EH}^{\rm nom}\ge W_t-\frac1{250},\qquad
W_t=\frac{1+\cos t+|\sin t|}{2}.
\tag{13}
\]

These error bounds are intentionally weaker than the shared total-error
constraint. Using them independently preserves a necessary condition and
cannot discard a counterexample.

Put \(s=\sin t,c=\cos t\). On each zero-quarter edge the allowed
nominal projections are identical, namely
\(b_H+b_G,b_A+b_B,b_T+b_D\). On B→T, nominal axes 1 and 2 give
\(a_T-b_B\), and axes 3 and 4 give \(a_B-b_T\). On D→E,
nominal axes 1 and 2 give \(a_E-b_D\), and axes 3 and 4 give
\(a_D+b_E\). Thus either member of a nominally identical pair may
be represented by its first index, 1 or 3.

The two mixed-edge projections are explicitly:

| Axis | G→A | E→H |
|---|---|---|
| 1 | \(-b_G+a_Ac-b_As\) | \(-b_E+a_Hc+b_Hs\) |
| 2 | \(-a_Gs-b_Gc+a_A\) | \(a_Es-b_Ec+a_H\) |
| 3 | \(a_Gc-b_Gs-b_A\) | \(a_Ec+b_Es-b_H\) |
| 4 | \(a_G-a_As-b_Ac\) | \(a_E+a_Hs-b_Hc\) |

If a forbidden aligned-quarter separator exists, select such an axis on
one offending edge and select any feasible axis on every other edge.
The resulting necessary nominal pattern has the form

\[
(1,g,1,b,1,e,h),\quad
g,h\in\{1,2,3,4\},\quad b,e\in\{1,3\},\quad(b,e)\ne(3,3).
\tag{14}
\]

There are exactly \(16\cdot3=48\) such patterns. No mixed owner has
been presumed in obtaining this cover.

## 4. The circle-dual identity

Fix one pattern (14). Let the seven necessary inequalities (11), (13)
be written \(f_i(t)\cdot x\ge w_i(t)\). Choose any nonnegative
rational numbers \(\lambda_i,\kappa_j\), and any strictly positive
rational numbers \(\mu_i\). Define

\[
C(t)=\sum_{i=0}^6\lambda_i f_i(t)+\sum_{j=0}^{34}\kappa_j K_j,
\qquad
B(t)=\sum_i\lambda_iw_i(t)+\sum_j\kappa_jv_j.
\tag{15}
\]

Adding valid inequalities gives \(C\cdot x\ge B\). After translating
each pair of coordinates by \((1/2,1/2)\), this becomes

\[
L(t):=B(t)+\frac12\sum_{j=0}^{13}C_j(t)
\le\sum_{i=0}^6(C_i,C_{7+i})\cdot(a_i+1/2,b_i+1/2).
\tag{16}
\]

The exact square identity

\[
\mu|v|^2+\frac{|w|^2}{4\mu}-w\cdot v
=\mu\left|v-\frac{w}{2\mu}\right|^2\ge0
\tag{17}
\]

and (6) bound the right side of (16) by

\[
Q\sum_i\mu_i+\sum_i\frac{C_i(t)^2+C_{7+i}(t)^2}{4\mu_i}.
\tag{18}
\]

Thus any fixed weights for which L is strictly greater than (18) give
a contradiction on their whole stated t domain. The argument does not
require the weights to solve an optimization problem, to be stationary,
or to come from a particular numerical procedure.

## 5. Fixed quartics and complete closed coverage

Set \(z=\tan(t/2)\), \(D=1+z^2\). Then

\[
s=\frac{2z}{D},\qquad c=\frac{1-z^2}{D}.
\tag{19}
\]

The elementary bound \(\arctan x\ge x-x^3/3\) gives

\[
\arctan(3/8)-7/20\ge19/2560>0.
\tag{20}
\]

Hence the entire actual range \(|t|<.7\) is contained in
\(-3/8<z<3/8\). Cover its closure by the 30 fixed intervals

\[
J_j=[-3/8+j/40,-3/8+(j+1)/40],\qquad0\le j<30.
\tag{21}
\]

Zero is a partition endpoint, so the sign of z is fixed on every
interval. It fixes the sign in \(|\sin t|\), including the common
zero endpoint. Equations (15), (19) show that
\(\widehat C_j=DC_j\) and \(\widehat L=DL\) have degree at most
two. Multiplying the strict reverse of (18) by \(D^2>0\) gives the
single polynomial

\[
P(z)=D\widehat L(z)-Q D^2\sum_i\mu_i
-\sum_i\frac{\widehat C_i(z)^2+\widehat C_{7+i}(z)^2}{4\mu_i}.
\tag{22}
\]

It has degree at most four and rational coefficients.

The fixed data file contains one row for each of the 48 patterns and
30 intervals. Each row gives seven \(\lambda\) numerators, the
nonzero \(\kappa\) numerators with their indices from (8), and seven
\(\mu\) numerators; all these are divided by \(10^8\).
All \(\lambda,\kappa\) are nonnegative and every \(\mu\) is
positive. There is no other numerical input to (22).

For \(J=[l,l+h]\), put \(z=l+hv\). Expand
\(P(l+hv)=\sum_{j=0}^4 q_jv^j\), and define

\[
\beta_k=\sum_{j=0}^k q_j\frac{\binom{k}{j}}{\binom4j},
\qquad0\le k\le4.
\tag{23}
\]

Then the polynomial identity

\[
P(l+hv)=\sum_{k=0}^4\beta_k\binom4k v^k(1-v)^{4-k}
\tag{24}
\]

proves positivity on the whole closed interval whenever all five
coefficients are positive. The table supplies five positive integer
lower numerators, divided by \(10^{12}\), for precisely these
coefficients. The smallest displayed numerator among all 7,200 is

\[
\boxed{1970267266>0.}
\tag{25}
\]

The accompanying arithmetic report records the minimum for each of the
48 owner patterns. The standalone checker reconstructs (9), (8), (22),
(23) from the fixed rational data, verifies each displayed lower bound,
expands (24) back into the power basis, and checks the exact Cartesian
product (14), (21), with no omitted, repeated, or open end interval.
Its fresh result is

\[
48\text{ patterns}\times30\text{ closed intervals}
=1440\text{ positive quartics}.
\tag{26}
\]

For every putative bad-owner packing, (14), (20), (21) select one
row. Equations (22)–(25) contradict the necessary circle inequality
(16)–(18). This proves (4).

## 6. Equality and the next interface

Every excluded nominal pattern has a strictly positive polynomial
reserve. Thus this theorem creates no additional equality configuration
and needs no special treatment of a circle contact, tangent zero, radial
endpoint, partition endpoint, or simultaneous separating axes.

The next hand interface may therefore assume the five owner sets in
(4) while working conditionally on (3). The two mixed edges still require
their own owner proof, and the common tilt still requires capture in the
sharp terminal chart. Neither conclusion is inferred merely from the
existence of this fixed table.
