# Exact five-scalar compatibility and three-parameter reconstruction of the remaining one-share C6

Date: October 26, 2026.

**Status: accepted complete hand reduction after independent full-source
and physical-domain review.** See
REVIEW_C6_FIVE_SCALAR_COMPATIBILITY_ROOT_2026_10_26.md and the separate
REVIEW_C6_FIVE_SCALAR_COMPATIBILITY_BLOCK_2026_10_26.md.
This source identifies the exact dependence among the six actual channel
components. It does not exclude the remaining contact orbit, enumerate
the roots of its equations, or prove a completion-capacity bound.

The domain is the original all-unique, all-side-transmitter alternating
six-cycle with canonical corner word \(\chi=(1,1,0)\) and sole genuine
outgoing share \(S_0W_0\). The complete symmetry cover and physical
residue are in
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md. Retain all nine
actual squares, the common selected certificate, every original
positive force, the actual shared mean and its endpoint cases, the
physical circle masks, all three original transmitter sliders, every
singleton or genuinely shared contact restriction, and all three extra
squares. The radius range remains
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Individual zero circle weights are not replaced by positive weights.
No Lean compilation or CI was run. No numerical computation is a premise.

## 1. Conventions and three exact residual identities

The argument of this section also holds for the full adjacent-side
chart, with arbitrary original shared means. Indices are cyclic modulo
three. Let \(J(x,y)=(-y,x)\), and let
\(a\times b=a_xb_y-a_yb_x\). Use the original positive forces and
circle corners:
\[
 f_i=\mu_i n_i,\quad \mu_i>0,\quad |n_i|=1,\qquad
 F_i=f_{i-1}-f_i,\quad D_i=|F_i|>0,\quad z_i=RF_i/D_i.
\tag{2}
\]
The strict force turns in the retained domain ensure the displayed
\(D_i>0\). Let \(u_i\) be the directed inner side, \(v_i=-Ju_i\),
and write the actual ports as
\[
 p_i^-=z_i-(\chi_i-t_i^-)u_i-v_i,\qquad
 p_i^+=z_i+(t_i^+-\chi_i)u_i-v_i,
\]
\[
 0\le t_i^-<t_i^+\le1,\quad
 \ell_i=t_i^+-t_i^-,\quad
 K_i=(\chi_i-t_i^-)f_{i-1}+(t_i^+-\chi_i)f_i,
\]
\[
               g_i=K_i+JF_i,\qquad E_i=|g_i|>0,\qquad u_i=g_i/E_i.
\tag{3}
\]
The direction equality is the original torque and positive support
identity, as derived in SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md. In
particular it retains the actual shared application mean; it is not
an independently chosen preferred direction.

Define the three actual vector channel residuals, the closure residual,
and the scalar virial residual by
\[
 r_i=p_{i+1}^- -p_i^+-n_i,\qquad
 C=\sum_i(n_i+\ell_i u_i),
\]
\[
                    V=R\sum_iD_i-\sum_i\mu_i-\sum_iE_i.
\tag{4}
\]
For every tuple satisfying the local equations (2)--(3), even before
any channel equation has been imposed, there are the exact identities
\[
 \boxed{\quad \sum_i r_i=-C,\qquad
 \sum_i f_i\cdot r_i=V,\qquad
 \sum_i f_i\times r_i=0.\quad}
\tag{5}
\]

**Proof.** The first identity is a direct telescoping of the ports.
For the second, the local contribution is
\[
 f_{i-1}\cdot p_i^- -f_i\cdot p_i^+
 =F_i\cdot z_i-K_i\cdot u_i-F_i\cdot v_i
 =RD_i-E_i.
\tag{6}
\]
Here \(F_i\cdot v_i=(JF_i)\cdot u_i\). Summing (6) and
subtracting \(\sum_i f_i\cdot n_i=\sum_i\mu_i\) proves the
second identity in (5).

For the third, each original loaded torque is identically zero:
\[
 \begin{split}
 p_i^-\times f_{i-1}-p_i^+\times f_i
 &=z_i\times F_i-u_i\times K_i-v_i\times F_i\\
 &=-u_i\times(K_i+JF_i)=0.
 \end{split}
\tag{7}
\]
Indeed \(z_i\parallel F_i\),
\(v_i\times F_i=u_i\cdot F_i=u_i\times JF_i\), and
\(u_i\parallel g_i\). Telescoping the left side of (7), with
\(f_i\times n_i=0\), gives
\(\sum_i f_i\times r_i=0\), as asserted. This is an exact
local-torque dependence; no numerical rank inference is used.

## 2. All six channel components are equivalent to five scalars

Under (2)--(3), one has the equivalence
\[
 \boxed{\qquad r_0=r_1=r_2=0
       \quad\Longleftrightarrow\quad r_0=0,\ C=0,\ V=0.\qquad}
\tag{8}
\]
There are two scalar components in each of \(r_0=0\) and \(C=0\),
and one in \(V=0\).

The forward implication follows from (5). Conversely, \(r_0=C=0\)
gives \(r_2=-r_1\). The last two identities in (5) then become
\[
             F_2\cdot r_1=0,\qquad F_2\times r_1=0,
             \qquad F_2=f_1-f_2\ne0.
\tag{9}
\]
A vector perpendicular and parallel to the same nonzero planar vector
must vanish. More explicitly,
\((F_2\cdot r_1)^2+(F_2\times r_1)^2
=|F_2|^2|r_1|^2\), so \(r_1=0\), and then \(r_2=0\).

The same statement holds with any single channel in place of channel
0, by cyclic relabeling. Closure and virial alone still do not suffice.
This equivalence concerns the actual channel equations, and does not
replace circle containment, masks, contact types, pairwise nonoverlap,
or the nine-square completion conditions.

## 3. Original remaining-orbit coordinates

Normalize only by the original positive force \(\mu_0\). Put
\[
 \mu=(1,p,q),\quad p,q>0,\qquad
 c_i=-\cos\theta_i,\quad s_i=\sin\theta_i,\quad
 A_i=s_i-c_i,\quad h_i=s_i+c_i,
\]
\[
 \pi/2<\theta_i\le3\pi/4,\quad \sum_i\theta_i=2\pi,\qquad
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad n_2=(-c_0,-s_0).
\tag{10}
\]
The actual directions and lengths are
\[
 u_0=(0,-1),\quad v_0=(-1,0),\quad
 \ell_0=1-qA_0,\quad (t_0^-,t_0^+)=(0,\ell_0),
\]
\[
 u_1=(X,Y)=\frac{(1+ps_1,1+pc_1)}{E_1},\qquad
 E_1=\sqrt{2+p^2+2ph_1},
\]
\[
 u_2=\frac{q(-h_0,-A_0)+p(-s_1,-c_1)}{E_2},\qquad
 E_2=\sqrt{p^2+2q^2+2pqh_2},\qquad \ell_1=\ell_2=1.
\tag{11}
\]
Here \((t_i^-,t_i^+)=(0,1)\) for \(i=1,2\), and
\(v_i=-Ju_i\). The endpoints of the original shared mean are
included initially by \(0<\ell_0\le1\). The endpoint
\(\ell_0=1\) is contradicted by actual closure in Section 3.2 of
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md, giving
\(0<\ell_0<1\) for any actual remaining core. This endpoint has
not been relabeled as a singleton or silently dropped.

The exact residuals in (4) use
\[
 D_0=\sqrt{1+q^2+2qc_0},\quad
 D_1=\sqrt{1+p^2+2pc_1},\quad
 D_2=\sqrt{p^2+q^2+2pqc_2},
\]
\[
 V=R(D_0+D_1+D_2)-
           [2+p+q(1+h_0)+E_1+E_2].
\tag{12}
\]
All signs and the constant 2 in \(E_1^2\) are part of the exact
original normalization.

## 4. Solve the two channel-0 components in three parameters

Take \((R,p,c_1)\) as parameters, initially with
\[
 R\text{ in (1)},\qquad p>0,\qquad 0<c_1\le1/\sqrt2,\qquad
 s_1=\sqrt{1-c_1^2}>0.
\tag{13}
\]
Use \(D_1,E_1,X,Y\) from (11)--(12), and define
\[
 A=\frac{R(1+pc_1)}{D_1},\qquad
 B=\frac{Rp s_1}{D_1},\qquad z_1=(A,-B),
\]
\[
 a=2+X+Y-A,\qquad H=B-X+Y,\qquad
 b=\sqrt{R^2-a^2}>0,\qquad \ell=1+H-b,
\]
\[
              \kappa=\frac{\ell}{a-b},\qquad
              f_2=(1-\kappa a,-\kappa b).
\tag{14}
\]
Only parameters with the radical and all the admissibility conditions
in Section 5 are retained. In particular the original branch has
\(a>b>1/2\) and \(\ell>0\), so this division is legitimate.
Set
\[
 q=\sqrt{(\kappa a-1)^2+\kappa^2b^2},\qquad
 c_0=\frac{\kappa a-1}{q},\qquad
 s_0=\frac{\kappa b}{q},\qquad z_0=(-a,-b).
\tag{15}
\]

### 4.1. Every original physical core has this representation

Its positive force and corner formulas give
\[
 z_0=\frac{R(-1-qc_0,-qs_0)}{D_0}=(-a,-b),\qquad
 \kappa=D_0/R>0.
\tag{16}
\]
The actual unique-corner conditions at unit 0 are exactly
\(a>1/2\) and \(b>1/2\). Its ports are
\[
 p_0^-=(-a+1,-b+1),\qquad
 p_0^+=(-a+1,-b+1-\ell_0).
\tag{17}
\]
Unit 1 has
\[
             p_1^-=(A-X-Y,-B-Y+X).
\tag{18}
\]
The two components of its actual channel
\(p_1^- -p_0^+=(1,0)\) give exactly
\(a=2+X+Y-A\), \(H=B-X+Y=b-1+\ell_0\).
The negative vertical sign in (16), together with its original circle,
selects \(b=+\sqrt{R^2-a^2}\), and then
\(\ell=1+H-b=\ell_0\).

Finally the actual shared torque gives
\[
 \ell_0=1-q(s_0-c_0)
         =\kappa(a-b).
\tag{19}
\]
Since \(\ell_0,\kappa>0\), one has \(a>b\); therefore
\(a>R/\sqrt2>1\). Equations (14)--(15) now recover the
original \(\kappa,f_2,q,c_0,s_0\) exactly. There is no second
circle-height branch for an original physical core.

### 4.2. The reconstruction solves channel 0 and all local equations

Conversely, take any parameter tuple (13) satisfying all retained
conditions of Section 5, and construct (14)--(15). Then
\(F_0=f_2-f_0=\kappa(-a,-b)=\kappa z_0\),
\(D_0=\kappa R>0\), and hence
\(z_0=RF_0/D_0\), as required by the original circle-load equation.
Moreover
\[
 q(s_0-c_0)=1-\kappa(a-b)=1-\ell.
\tag{20}
\]
Thus the original shared torque and mean are exactly those in (11).
For a direct support check, its actual
\(K_0=f_2+(\ell-1)f_0\) gives
\[
 g_0=K_0+JF_0=(0,-\kappa(a+b)),\qquad
 E_0=\kappa(a+b)=1+qh_0>0,\qquad u_0=(0,-1).
\tag{21}
\]
Build unit 1 by (11) and its corner \((A,-B)\), and build unit
2 using its actual bit-zero formulas in (11). These are precisely
the local positive-support and torque equations (2)--(3).

The ports (17)--(18) simplify to
\[
 p_0^-=(-a+1,-b+1),\quad p_0^+=(-a+1,-H),\qquad
 p_1^-=(2-a,-H).
\tag{22}
\]
Consequently the actual vector channel 0 is identically solved.
By (8), the other two channels are then exactly equivalent to the
three remaining scalar equations
\[
 \boxed{\quad
 C_x(R,p,c_1)=0,\qquad C_y(R,p,c_1)=0,\qquad V(R,p,c_1)=0.
 \quad}
\tag{23}
\]
The functions are explicitly (4), (11)--(15); no additional unknown
force ratio, turn angle, or shared chord is introduced in (23).
Their simultaneous solutions are not asserted to be isolated, unique,
or all contained in any numerically observed box.

## 5. Exact admissibility and physical conditions remain

The reconstruction in Section 4 is a change of coordinates, not a
relaxation of the packing. In the original orbit its parameters obey
all of the following conditions, and conversely these conditions are
retained when (23) is used in place of the channel equations.

1. The original radius interval (1), \(p>0\),
   \(0<c_1\le1/\sqrt2\), the real positive radical \(b\),
   \(a>b>1/2\), \(0<\ell\le1\), and \(\kappa>0\).
   Full closure excludes \(\ell=1\) by the cited endpoint argument.
2. The reconstructed force satisfies \(q>0\),
   \(0<c_0\le1/\sqrt2\), \(s_0>0\), and the unchanged turn
   constraints for all three turns. Explicitly,
   \(\alpha_i=\theta_i-\pi/2\),
   \(\alpha_0=\arcsin c_0\),
   \(\alpha_1=\arcsin c_1\),
   \(\alpha_2=\pi/2-\alpha_0-\alpha_1\) must each lie in
   \((0,\pi/4]\). Then
   \(s_2=s_0c_1+c_0s_1\) and
   \(c_2=s_0s_1-c_0c_1\), consistently with (10).
3. Every reconstructed loaded square is the original
   \(S_i=b_i+[0,1]u_i+[0,1]v_i\), with
   \(b_i=z_i-\chi_i u_i-v_i\). Its sole physical circle corner
   is \(z_i\). In particular
   \(z_i\cdot v_i>1/2\) and
   \((2\chi_i-1)z_i\cdot u_i>1/2\); every original vertex is
   contained in the same circle. These physical masks hold
   independently of the individual selected load weights.
4. All original contact sets and their genuine shared or singleton
   types remain. The original means, including any physically allowed
   endpoint, must belong to those actual contact sets. The transmitter
   positions retain the whole original transverse intervals of
   SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md, including their original
   contact restrictions; none is moved to a preferred slider endpoint.
5. All nine squares remain in the common circle with pairwise
   interior-disjointness. All three extra squares, their physical
   boundary masks, and any zero individual circle weights remain.
   No equation in (23) creates or deletes a physical square.

The already proved necessary force bounds
\(p<27/10\), \(p/q<27/10\), \(q>20/81\) remain available;
they are consequences, not replacements, of the physical corner
conditions. A further useful exact consequence of (14)--(15) is
\[
 c_0>0\quad\Longleftrightarrow\quad
 \kappa a>1\quad\Longleftrightarrow\quad
                  H>b(1-1/a),
\tag{24}
\]
where the last equivalence follows by multiplying by the positive
\(a-b\): \(a(1+H-b)>a-b\). In particular \(H>0\), since
\(a>1\). This is the actual positive outward height of channel 0
in the coordinates (22).

## 6. Result and remaining task

For the complete remaining physical one-share orbit, the six individual
channel components have one exact local-torque dependence. One actual
channel, two closure components, and the original virial give exactly
the full channel equations. Solving channel 0 leaves the explicit
three-parameter system (23), with no loss of the original forces,
means, circle branch, or nine-square geometry.

SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md still gives at most one
central extra. SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md gives
an empty entire exterior pocket 1. All repeated occupancy of exterior
pockets 0 and 2 remains until independently excluded. This source
supplies a smaller exact system for deriving uniform geometric bounds;
it does not yet establish those bounds or close the completion gate.
