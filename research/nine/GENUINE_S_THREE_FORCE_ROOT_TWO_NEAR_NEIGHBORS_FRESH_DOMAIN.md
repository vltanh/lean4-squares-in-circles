# A genuine S three-force root with two actual near neighbors

**Status: complete fresh local force/feature and initial-selection theorem,
saved for full independent review. No whole attachment is claimed here.**

Work in the original nine-unit packing with

\[
 \sqrt{17}/2<R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1=1+\varepsilon,
 \qquad 0<\varepsilon<1/60.
\tag{1}
\]

Let B have a genuine S leaf L and exactly two other positive neighbors
A,C. Suppose each of the actual A,C contains a point of the closed disk
\(D_\varepsilon\). Their degrees, loads, other forces and physical
circle masks are arbitrary. No AC edge is assumed. Every actual contact
mean and all nine squares remain.

The full support theorem
`GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md` makes B aligned with its
real leaf. Normalize its leaf direction east:

\[
 B=[\varepsilon,d]\times[-b,a],\qquad
 a,b\ge0,\quad a+b=1,
 \qquad p_{BL}=(d,0).
\tag{2}
\]

The actual B-to-A and B-to-C supports satisfy

\[
 h_B(n_A)\le\varepsilon,\qquad
 h_B(n_C)\le\varepsilon.
\tag{3}
\]

Indeed every point of an actual neighbor is beyond its actual supporting
line, including the stated near point. The full unloaded B equations are

\[
 \beta E+\mu n_A+\nu n_C=0,\qquad
 \mu\det(P_A,n_A)+\nu\det(P_C,n_C)=0,
 \qquad\beta,\mu,\nu>0.
\tag{4}
\]

The leaf contributes its original zero radial moment.

**Theorem.** There are exactly the following remaining alternatives.

1. Both actual nonleaf normals are West. Their original means satisfy
   \(\mu y_A+\nu y_C=0\).
2. Both nonleaf normals strictly expose the two left B vertices. After
   exchanging A,C,
   \[
   P_A=(\varepsilon,a),\quad n_A=(-c,s),\qquad
   P_C=(\varepsilon,-b),\quad n_C=(-c',-s'),
   \tag{5}
   \]
   with all four normal components and both a,b strictly positive.
   A compatible simultaneous initial selection makes each of these two
   normals owned by its other endpoint A or C.

If A and C are themselves distinct genuine S roots, the parallel means
in alternative 1 have strictly opposite signs. In particular they are
actual distinct points of the same left unit side of B. All statements
have arbitrary A,C degree scope.

The transverse-owned calculation in Section 1 was supplied by root and
independently re-derived here. The right-vertex extension and the complete
selection/parallel-mean cover are recorded below so the whole scope does
not rely on a triangle between A and C.

## 1. A transverse B-owned nonleaf normal is impossible

Suppose BA is North, with its actual mean \((x,a)\) and magnitude
\(\mu>0\). By (3), \(a\le\varepsilon\), hence
\(b=1-a>59/60\). The other full force in (4) is

\[
 F_{BC}=(-\beta,-\mu).
\]

It is strictly southwest and its actual B application is
\((\varepsilon,-b)\). With \(k=\beta/\mu>0\), the entire B torque
gives

\[
 x=\varepsilon+bk.
\tag{6}
\]

The original mean remains on B's unit top side, so \(x\le d\) and

\[
 k\le1/b<60/59.
\tag{7}
\]

The actual BC support is therefore

\[
 h_B(n_C)=\frac{b-\varepsilon k}{\sqrt{1+k^2}}
 >\frac{59/60-1/59}{3/2}
 =\frac{3421}{5310}>\varepsilon.
\tag{8}
\]

The denominator estimate is strict because

\[
 \frac94-\left(1+\frac{3600}{3481}\right)
 =\frac{3005}{13924}>0.
\]

This contradicts (3). Reflection excludes South. Both endpoints of the
actual North/South mean interval were included. No neighbor equation or
AC contact entered (6)--(8).

East is impossible directly from \(h_B(E)=d>\varepsilon\).

## 2. A strict right B vertex is impossible as well

Suppose BA strictly exposes B's upper-right vertex, with

\[
 P_A=(d,a),\qquad n_A=(c,s),\quad c,s>0,\quad c^2+s^2=1.
\]

The actual support \(dc+as\le\varepsilon\) forces
\(a<\varepsilon\): since \(d>1\ge a\), one has
\(dc+as>a\), including a=0. Thus again \(b>59/60\).

The complete other force and its actual application are

\[
 F_{BC}=(-\beta-\mu c,-\mu s),\qquad
 P_C=(\varepsilon,-b).
\]

The full torque (4), using d-epsilon=1 and a+b=1, is

\[
 \mu(s-c)=b\beta.
\tag{9}
\]

Put \(k=\beta/\mu>0\). Then \(s>c\) and

\[
 k+c=\frac{s-ac}{b}\le\frac{s}{b}.
\tag{10}
\]

The original BC support satisfies

\[
\begin{split}
 h_B(n_C)
 &=\frac{bs-\varepsilon(k+c)}{\sqrt{(k+c)^2+s^2}}\\
 &\ge\frac{b-\varepsilon/b}{\sqrt{1+b^{-2}}}
 >\frac{3421}{5310}>\varepsilon.
\end{split}
\tag{11}
\]

The numerator used here is positive, so the denominator comparison has
the stated direction. Equation (11) contradicts (3). Reflection excludes
the lower-right vertex. These two cases exhaust the strict normals with
positive horizontal component; no side-owner hypothesis at A or C was
used.

## 3. The full remaining force and moment cover

Every nonleaf normal now has negative horizontal component. If either
is the B-owned West axis, the vertical component of (4) forces the other
to be West too. All other surviving normals strictly expose left vertices.
Their vertical components must have opposite signs, giving (5).

The full vertical force and torque equations in that case give

\[
 \mu s=\nu s',\qquad
 a\mu c=b\nu c'.
\tag{12}
\]

Since a+b=1 and every normal component and magnitude in (12) is positive,
both a,b are strictly positive. In particular neither of the two fixed
actual applications is collinear with the genuine leaf direction E.

Their two nonparallel normal lines meet on the positive horizontal ray,
at the exact point

\[
 q_B=\left(\varepsilon+\frac{ac}{s},0\right)
     =\left(\varepsilon+\frac{bc'}{s'},0\right).
\tag{13}
\]

No inside-B upper bound on this concurrence is asserted or needed.
Equation (13) does not change either original application.

## 4. Compatible fixed-singleton selection in the nonparallel case

Both contacts in (5) are strict B vertices. If an actual normal has no
side-axis owner at its other endpoint, it is a genuinely free point normal.
The physical intersections are singletons regardless of which endpoint
owns the other normal.

Write P,Q for the two distinct fixed B vertices, n,m for their actual
outward normals. The full three-force equations give the necessary identity

\[
 \det(E,n)\det(Q,m)-\det(E,m)\det(P,n)=0.
\tag{14}
\]

For a free n, with m fixed, this is \(\det(W,n)=0\), where

\[
 W=\det(Q,m)E-\det(E,m)P.
\tag{15}
\]

Here \(\det(E,m)\ne0\) by (5). If W vanished, P would be collinear
with E, contrary to a,b>0. Thus (14) is a nonzero linear condition on the
free n interval. If both directions are free, fix any permitted m first;
the same argument proves the condition is not identically zero on their
product domain.

Prelist all ordered physical genuine-leaf B assignments and these two
fixed singleton contacts before multiplier extraction. The physical leaf
fixes E. Matching opposite pairs at one junction does not identify the
normal parameters at the distinct P,Q. The finitely many nontrivial
conditions (14) can be avoided simultaneously with the existing strict,
nonradial and matched-junction choices. Physical uncrossing preserves every
surviving free direction and adds only actual shared-side forces; thinning
only removes atoms. No shared mean or neighbor circle weight is selected.

This is the fixed-singleton force/torque mechanism of
`RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md`, Sections 3--4,
with the nonzero coefficient proved directly by (5),(12),(15). Its
boundary-neighbor premise is not imported. Neither A nor C is required
to be boundary, unloaded, or degree two. Hence both actual normals in the
entire nonparallel case have side-axis owners at A,C.

## 5. Full parallel means when both neighbors are genuine S roots

For two West normals, full torque is

\[
 \mu y_A+\nu y_C=0,
\tag{16}
\]

where both actual means are on \(x=\varepsilon\), in the unchanged unit
interval \([-b,a]\). They have strictly opposite signs unless both are
zero. We exclude that last case only under the stated additional genuine
S-root premise on A,C.

If both means are zero, A and C both contain
\(P=(\varepsilon,0)\) and lie wholly in \(x\le\varepsilon\).
Neither can have P in a side interior: its left tangent half-plane would
overlap the other unit's interior. Their two inward right-angle sectors
at P must be disjoint inside the same left half-plane. They therefore
fill its upper and lower quadrants exactly, forcing the actual units to be

\[
 [\varepsilon-1,\varepsilon]\times[0,1],\qquad
 [\varepsilon-1,\varepsilon]\times[-1,0].
\tag{17}
\]

Neither can be a genuine S root. None of its own-axis support heights
equals d. Among its vertices, all squared norms except the far-left
upper/lower corner are strictly below \(d^2\); the remaining squared
norm exceeds \(d^2\) by exactly \(1-4\varepsilon>0\). Thus there is
no possible genuine radial S application \(de\), whether at an own side
or a strict vertex. This contradicts the actual real leaf of either root.

After exchanging A,C, the whole parallel alternative therefore has

\[
 P_A=(\varepsilon,t_A),\quad
 P_C=(\varepsilon,-t_C),\qquad
 t_A,t_C>0,\quad t_A+t_C\le1.
\tag{18}
\]

The original means, including their B-side endpoints, are retained.

## 6. Literal original uses and limits

For the three-leaf C4 A--B--C--D--A, the actual middle root B has true
degree three and two genuine near neighbors A,C. This theorem gives its
whole nonparallel/parallel division without an AC triangle or any equation
at D. The full outer A3/C3 stars remain for the next proof.

For the diamond with genuine leaves at both hubs and one tip B, the
decorated tip B again has true degree three and two genuine near hub
neighbors. This theorem keeps both full hub degrees four and their actual
mutual force. No degree-two or three equation is assigned to either hub.

The theorem closes no whole original attachment by itself. It changes no
normal after extraction, no physical mean, no load or mask, and no one of
the nine squares. No numerical pose or computational subdivision is a
premise.
