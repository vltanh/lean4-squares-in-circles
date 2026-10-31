# Exterior pocket 0 of the remaining mixed one-share C6 has capacity at most one

Date: October 26, 2026.

**Status: complete hand proof, accepted after root and separate independent
full-source and physical-scope reviews.** See
REVIEW_C6_REMAINING_CAP_0_CAPACITY_ONE_ROOT_2026_10_26.md and
REVIEW_C6_REMAINING_CAP_0_CAPACITY_ONE_C6_2026_10_26.md.
The theorem covers the entire remaining all-unique one-share orbit.
It uses the accepted whole-orbit radius bound, original channel 0,
and one component of the original closure. It needs none of the
additional coordinate-box hypotheses in
SIX_CYCLE_REMAINING_CAP_0_CONDITIONAL_CAPACITY_ONE.md.
No sampled root, angular partition, or computational certificate is
a premise.

Retain the complete original nine-square domain of
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md. Its canonical
corner word is \(\chi=(1,1,0)\), its sole genuinely shared contact
is the outgoing \(S_0W_0\) contact, and all three transmitters have
their original side-normal reserve one and original sliders. The
physical unique-circle-corner masks, positive forces, all original
means and endpoint cases, additional zero-weight contacts, and all
three extra squares remain unchanged.

**Theorem.** Every such actual exterior channel-0 pocket contains
at most one additional unit square. In particular the three
completion allocations with at least two extras in pocket 0 are
impossible. The other four allocations displayed in Section 7
are retained; this theorem does not close the remaining C6 gate.

## 1. Original physical coordinates and two strict local inequalities

The original radius window and the accepted physical join in
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md give
\[
              K:=79/40\le R<2.
\tag{1}
\]
Use exactly the normal form of
SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md.
Let \(J(x,y)=(-y,x)\), normalize by the positive original force
\(\mu_0\), and write
\[
 \mu=(1,p,q),\quad p,q>0,\qquad
 \alpha_i\in(0,\pi/4],\quad\sum_i\alpha_i=\pi/2,
\]
\[
 c_i=\sin\alpha_i,\quad s_i=\cos\alpha_i,\quad
 A_i=s_i-c_i,\quad r=1/\sqrt2,
\]
\[
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad
 n_2=(-c_0,-s_0).
\tag{2}
\]
The actual shared mean has
\[
 u_0=(0,-1),\qquad
 \ell=1-qA_0,\quad \delta=1-\ell=qA_0,\qquad
                         0<\ell<1.
\tag{3}
\]
The initially retained endpoint \(\ell=1\) was contradicted by
actual closure in the cited orbit cover, not silently discarded or
reclassified as a singleton. Thus \(0<\delta<1\) here.

Put
\[
 u_1=(X,Y)=\frac{(1+ps_1,1+pc_1)}
                  {\sqrt{2+p^2+2p(s_1+c_1)}},
\quad T=X+Y,\quad W=X-Y.
\tag{4}
\]
In particular
\[
 X\ge Y>0,\quad X^2+Y^2=1,\quad
 W\ge0,\quad T^2+W^2=2,\quad T\le\sqrt2.
\tag{5}
\]
The exact actual channel-0 coordinates are
\[
 \begin{split}
 S_0&=[-a,1-a]\times[-b,1-b],\\
 S_1&=(2-a,-H)+[0,1](X,Y)+[0,1](Y,-X),
 \end{split}
\]
\[
 a>b>1/2,\quad a^2+b^2=R^2,\quad
 H=b-\delta=b-1+\ell>0.
\tag{6}
\]
The positive actual height \(H\) is that supplied by the proper
force polygon and channel-cap theorem; the exterior pocket is on
the side \(y\le-H\). The two actual circle corners are
\[
 z_0=(-a,-b),\qquad
 z_1=(2-a+T,-H-W)=:(A,-B),\qquad |z_1|=R.
\tag{7}
\]
No selected mean or application point was moved to obtain (6)--(7).

Two strict local inequalities will be useful. First, the unchanged
shared torque and the original strict force quadrant give
\[
 \kappa=\frac{\ell}{a-b}>0,\qquad
 f_2=(1-\kappa a,-\kappa b)=q(-c_0,-s_0),
\]
so \(\kappa a>1\). Consequently
\[
                 \boxed{\ H>b(1-1/a).\ }
\tag{8}
\]
Indeed \(\ell>(a-b)/a=1-b/a\), and (8) follows from (6).
Also \(a>R/\sqrt2>1\), so its right side is positive.

Second, put \(F_1=f_0-f_1=\eta z_1\), where \(\eta>0\) is
the original circle-load coefficient. The original nonshared torque
has \(g_1=f_0+JF_1\) in the direction \(u_1\). It gives
\[
             \eta=\frac{Y}{AX-BY}>0.
\tag{9}
\]
The denominator is the actual positive own-coordinate
\(z_1\cdot u_1>1/2\). The strict first component
\((f_1)_x=-pc_1<0\) is \(1-\eta A<0\), so
\(Y(A+B)>AX\). On substituting (7), this is exactly
\[
                \boxed{\ YH>W(2-a+X).\ }
\tag{10}
\]
This includes \(W=0\); no division by \(W\) is made.

## 2. The whole actual channel has height greater than 21/50

We prove
\[
                         \boxed{H>21/50.}
\tag{11}
\]
Suppose to the contrary that \(0<H\le h:=21/50\), and put
\(d=2-a>0\), \(C=2+\sqrt2\).

### 2.1. A complete interval for the original coordinate a

Equations (5),(7),(10) give
\[
 \begin{split}
 R^2-[(d+\sqrt2)^2+H^2]
 &=2W\left(H-\frac{dW}{\sqrt2+T}\right)\ge0.
 \end{split}
\tag{12}
\]
For \(W>0\), (10) gives
\(H>W(d+X)/Y>dW/(\sqrt2+T)\); for \(W=0\), (12)
is equality. The quantities being compared are all positive.
It follows that
\[
                  a\ge L:=C-\sqrt{R^2-H^2}.
\tag{13}
\]
Since \(R<2\), one has \(L>\sqrt2\). Moreover
\[
 K^2-h^2-(1/2+\sqrt2)^2
 > K^2-h^2-9/4-99/70
 =\frac{16783}{280000}>0,
\tag{14}
\]
where \(\sqrt2<99/70\) follows by squaring. Thus
\(\sqrt{R^2-H^2}>1/2+\sqrt2\), and
\[
                            \sqrt2<L<3/2.
\tag{15}
\]

The actual point \(p_1^-=(d,-H)\) is the vertex of \(S_1\)
opposite \(z_1\). Their distance is \(\sqrt2\), so the reverse
triangle inequality gives
\[
 d^2+H^2\ge(R-\sqrt2)^2.
\]
In particular
\[
 d^2\ge(K-\sqrt2)^2-h^2
       >(K-99/70)^2-h^2
       =(7/20)^2+\frac{30381}{1960000}.
\tag{16}
\]
Here \(K-99/70=157/280>0\), so the radical replacement has the
stated direction. Since \(d>0\), (16) proves
\[
                            a<33/20=:U.
\tag{17}
\]
Thus the original coordinate lies in the entire interval
\([L,U]\subset(1,R)\). No disconnected or numerically inferred
parameter range is being used.

### 2.2. One unimodal function contradicts both possible interval ends

For \(1<x<R\), define
\[
               f_R(x)=\sqrt{R^2-x^2}\,(1-1/x).
\]
Its exact derivative is
\[
        f_R'(x)=\frac{R^2-x^3}{x^2\sqrt{R^2-x^2}}.
\tag{18}
\]
It first increases and then decreases. Hence its minimum on any
closed subinterval is attained at an endpoint. Inequality (8)
is precisely \(H>f_R(a)\).

At the upper endpoint, monotonicity in \(R\) and (1) give
\[
 \begin{split}
 f_R(U)^2-h^2
 &\ge [K^2-(33/20)^2](13/33)^2-(21/50)^2\\
 &=\frac{280141}{43560000}>0.
 \end{split}
\tag{19}
\]
Both factors in \(f_R(U)\) are positive, so \(f_R(U)>h\ge H\).

At the lower endpoint, the definition of \(L\) says
\(R^2=H^2+(C-L)^2\). Direct expansion therefore gives
\[
 f_R(L)^2-H^2
 =\frac{2L-1}{L^2}\,[\mathcal T(L)-H^2],
\qquad
 \mathcal T(L)=\frac{C(C-2L)(L-1)^2}{2L-1}.
\tag{20}
\]
Put \(x=L-1\), so \(\sqrt2-1\le x\le1/2\). The exact identity
\[
 \mathcal T(L)-\frac{\sqrt2}{8}
 =\frac{(1-2x)[8Cx^2-4\sqrt2 x-\sqrt2]}{8(1+2x)}
\tag{21}
\]
proves \(\mathcal T(L)\ge\sqrt2/8\). Indeed the quadratic in
brackets has derivative \(16Cx-4\sqrt2\ge12\sqrt2>0\),
and at \(x=\sqrt2-1\) its value is
\(8-5\sqrt2>0\), as follows from \(64>50\).

Finally \(\sqrt2>353/250\), whose squared reserve is
\(2-(353/250)^2=391/62500>0\). Thus
\[
 \mathcal T(L)-H^2
 \ge\frac{\sqrt2}{8}-h^2
 >\frac{353}{2000}-\frac{441}{2500}
 =\frac1{10000}>0.
\tag{22}
\]
Equations (20),(22) show \(f_R(L)>H\). Both endpoints of
\([L,U]\) therefore have \(f_R>H\), and (18) implies
\(f_R(a)>H\), contradicting (8). This proves (11) on the
entire original physical orbit.

## 3. Closure bounds the entire endpoint-center distance

Write the actual third side direction as \(u_2=(-M,-N)\).
The full direction-cone and closure statements of
SIX_CYCLE_REMAINING_ONE_SHARE_ANGLE_AND_FORCE_BOUNDS.md give
\[
 N\ge r(s_0-c_0),\qquad
 N=s_1-s_0-1+\delta+Y.
\tag{23}
\]
Consequently
\[
 \begin{split}
 \delta-\frac W2
 &=1+s_0-s_1-\frac{X+Y}{2}+N\\
 &\ge1-s_1+(1+r)s_0-r c_0-r>0.
 \end{split}
\tag{24}
\]
For the last strict inequality, the function
\((1+r)\cos\alpha-r\sin\alpha\) decreases on
\([0,\pi/4]\), and its endpoint value at \(\pi/4\) is \(r\).
Also \(s_1<1\), because the original \(\alpha_1>0\).
Thus (24) proves the whole-domain relation
\[
                              \delta>W/2.
\tag{25}
\]

The centers of the two actual units in (6) are
\[
 C_0=(1/2-a,1/2-b),\qquad
 C_1=(2-a+T/2,-H-W/2).
\]
Their difference is therefore
\[
 C_1-C_0=\left(\frac32+\frac T2,
                      \delta-\frac{1+W}{2}\right).
\tag{26}
\]
Equations (3),(25) put the second component strictly between
\(-1/2\) and \(1/2\). Since \(T\le\sqrt2\),
\[
 \boxed{\quad
 |C_1-C_0|^2<(3/2+1/\sqrt2)^2+1/4
                         =3+3/\sqrt2.
 \quad}
\tag{27}
\]
This uses the actual shared chord and closure, not a generic
distance bound between endpoint applications.

## 4. The actual outward center gap is less than 127 degrees

After reflecting the channel frame to put its outward side above
the line, the channel-cap endpoint theorem gives the actual center
angles
\[
              0\le\phi_1<\pi/2<\phi_0\le\pi,
              \qquad \gamma=\phi_0-\phi_1\in(0,\pi].
\tag{28}
\]
Thus \(\gamma\) is the actual outward consecutive-center gap,
not a choice of the other circular arc. Each endpoint square has
an actual corner on \(\partial D_R\), so
\[
                     |C_i|\ge R-1/\sqrt2\ge K-1/\sqrt2.
\tag{29}
\]
If \(\gamma\ge\arccos(-119/200)\), the cosine law gives
\[
 \begin{split}
 |C_1-C_0|^2
 &\ge |C_0|^2+|C_1|^2+(119/100)|C_0||C_1|\\
 &\ge(319/100)(K-1/\sqrt2)^2
                         >3+3/\sqrt2,
 \end{split}
\tag{30}
\]
contradicting (27). To check the final strict comparison entirely
with fixed rationals, expand its difference as
\[
 \frac{319}{100}\left(\frac{7041}{1600}
                          -\frac{79\sqrt2}{40}\right)
                         -3-\frac{3\sqrt2}{2}.
\]
Replacing \(\sqrt2\) by its strict upper bound \(99/70\)
gives the positive lower bound \(6957/1120000\).

For the convenient rational angle, use the elementary
\(\pi>25/8\) established in ANNULAR_CENTER_ARC_AT_23_25.md.
Set \(z=185/288<37\pi/180<\pi/2\). Monotonicity of sine and
its signed cubic Taylor bound give
\[
 \sin(37\pi/180)>\sin z>z-z^3/6
       =\frac{119}{200}+\frac{11412799}{3583180800}
       >\frac{119}{200}.
\tag{31}
\]
Taking cosine at \(\pi/2+37\pi/180\), and using its
strict decrease on \([0,\pi]\), proves
\[
 \boxed{\quad
   \gamma<\arccos(-119/200)<127\pi/180.
 \quad}
\tag{32}
\]
Neither a decimal angle nor a sampled trigonometric comparison
enters this proof.

## 5. Every whole pocket extra occupies a long connected inner arc

Let \(E\) be any extra in the actual exterior pocket 0. The physical
channel-cap theorem SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md puts the
whole unchanged square in
\[
                           D_R\cap\{y\le-H\}.
\tag{33}
\]
Its half-width in the vertical direction is at least \(1/2\).
By (11), its center therefore satisfies
\[
                    |c_E|\ge H+1/2>23/25.
\tag{34}
\]
Apply ANNULAR_CENTER_ARC_AT_23_25.md to the actual square, with
\(\rho=5/4\). Its whole open-interior intersection with
\(\{|x|=\rho\}\) is one connected open arc, of length strictly
greater than
\[
                              29\pi/120.
\tag{35}
\]
This is the proved full-square arc estimate for every independent
orientation, not an estimate based only on the square's inscribed
disk. In particular the extra need not touch the containing circle
or carry any positive circle weight.

## 6. The actual crosscut routes all such arcs into one short interval

For completeness, use the outward-positive frame of (28), in which
the unchanged channel applications are
\[
 P_0=(l,H),\quad P_1=(l+1,H),\quad
 S_0\subset\{x\le l\},\quad S_1\subset\{x\ge l+1\}.
\tag{36}
\]
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md identifies the actual pocket as
the bounded side of the occupied crosscut
\(z_0-P_0-P_1-z_1\) and its outward outer-circle arc. The entire
Jordan curve lies above the strictly positive height \(H\).

Each endpoint unit meets the \(\rho\) circle in a single closed
arc with its radial-center point in the relative interior. This
follows from the complete closed-intersection formulas in
ANNULAR_CENTER_ARC_AT_23_25.md, since its boundary-center norm
exceeds \(5/4\). Its radial-center point lies in the open unit;
therefore its horizontal coordinate is strictly below \(l\) for
unit 0 and strictly above \(l+1\) for unit 1. Monotonicity of
cosine on the upper semicircle now puts every intersection of the
middle segment \(P_0P_1\) with that semicircle between angles
\(\phi_1\) and \(\phi_0\). The other two crosscut pieces lie
inside the two closed endpoint squares.

An endpoint's closed arc, restricted to the upper semicircle,
remains one interval containing its center angle. To justify this
even if the full arc extends below the horizontal axis, every point
\(z\) in an endpoint square satisfies
\[
 C_i\cdot z\ge |C_i|^2-|C_i|/\sqrt2>0.
\tag{37}
\]
Thus its full arc lies in the open angular semicircle about its
center. With the center angles in the respective upper quadrants
of (28), its upper restriction is an interval. Neither endpoint
interval can pass across the other center angle, whose radial
point is inside the other open square.

Consider any inner-circle point in \(E^\circ\). By (33) in this
frame it lies above \(H\), and physical nonoverlap puts it outside
both closed endpoint squares. If its angle were below \(\phi_1\),
follow the upper semicircle toward angle zero. Because it lies below
the interval containing \(\phi_1\), and the other endpoint
interval cannot cross \(\phi_1\), this path avoids both endpoint
intervals. It also avoids the middle crosscut segment, which has
angles only between \(\phi_1,\phi_0\), and avoids the outer
circle arc since \(R>\rho\). The positive horizontal ray from
angle zero then reaches infinity below \(H\). This contradicts
the point's bounded pocket label. A point above \(\phi_0\) is
excluded in exactly the same way using the semicircle toward
\(\pi\) and the negative horizontal ray. If a relevant center
angle is 0 or \(\pi\), that exceptional-angle case is empty.

Therefore every inner-circle point in every pocket extra's open
interior lies between \(\phi_1\) and \(\phi_0\). By
CENTERED_INNER_ARC.md each endpoint square contains in its open
interior the entire closed centered arc of half-width \(\pi/9\).
Avoiding those two blocked arcs confines all the extra arcs to
the single interval
\[
                    (\phi_1+\pi/9,\ \phi_0-\pi/9),
\tag{38}
\]
of length at most \(\gamma-2\pi/9\). If this interval is empty,
there is no extra and the desired capacity statement already holds.
Otherwise (32) gives the strict bound
\[
             \gamma-2\pi/9
               <127\pi/180-40\pi/180=29\pi/60.
\tag{39}
\]

Two extras with disjoint open interiors would have disjoint open
inner-circle arcs. By (35) their combined length exceeds
\(29\pi/60\), contradicting their containment in the single
shorter interval (38). This proves that the entire actual pocket
has capacity at most one.

The compact-interior homotopy argument of the physical cap theorem
retains all these statements at shared junctions and original
application endpoints. Additional zero-weight contacts can subdivide
the pocket, but cannot move an extra's connected interior through
the occupied crosscut or into a different free inner-circle interval.
No sector containment of an extra or its center was assumed.

## 7. Exact consequence and remaining completion domain

Combine this theorem with the accepted empty pocket-1 theorem
SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md and the accepted
SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md. Write \(n_c\) for the number of
central extras and \(n_0,n_2\) for the numbers in exterior pockets
0 and 2. The three extras of the original nine-square packing
must now obey
\[
              n_c\le1,\qquad n_0\le1,\qquad
                    n_c+n_0+n_2=3.
\tag{40}
\]
The exact remaining allocation list is

| Central extras \(n_c\) | Pocket-0 extras \(n_0\) | Pocket-2 extras \(n_2\) |
| --- | --- | --- |
| 0 | 0 | 3 |
| 0 | 1 | 2 |
| 1 | 0 | 2 |
| 1 | 1 | 1 |

Only the previous allocations \((n_c,n_0,n_2)=(0,3,0),(0,2,1),
(1,2,0)\) have been eliminated here. Repeated pocket-2 occupancy,
the simultaneous one-central/one-in-each-cap possibility, and every
original physical square and zero circle weight remain. The theorem
adds no certificate packet, moves no square or mean, and uses no
Lean compilation or CI.
