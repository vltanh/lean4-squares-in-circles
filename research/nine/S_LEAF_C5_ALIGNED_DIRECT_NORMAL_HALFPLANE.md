# Both cycle forces at an aligned S-leaf C5 root point away from the leaf

Date: October 26, 2026.

**Status: complete necessary half-plane theorem, accepted after independent
root review in REVIEW_S_C5_ALIGNED_DIRECT_HALFPLANE_ROOT_2026_10_26.md.**
This retains the original selected direct-contact normal.
It changes no point-normal convention and does not close the remaining
S-leaf completion family.

Keep the original component A--B--V--C--U--A with a genuine S leaf L
at A. The original labels are A=0, B=1, V=2, C=3, U=4. Only B,C
are loaded in the block. U,V remain actual unloaded degree-two
transmitters; A retains degree three and B,C degree two. All nine
physical units, both individual radial corner weights whenever
applicable, every original mean and the three extras remain.

In the original radius window, put
\[
 79/40\le R\le\sqrt{1105}/16,\quad
 d=\sqrt{R^2-1/4}-1,\quad \delta=d-1,
\]
\[
 L=[d,d+1]\times[-1/2,1/2],\qquad
 A=[\delta,d]\times[-b,a],\qquad a,b\ge0,\quad a+b=1.
\tag{1}
\]
This covers the whole aligned root, including both slider endpoints.
The tilted root remains outside the scope.

Write n for the actual A-to-C channel normal through U, and m for
the actual direct A-to-B normal. The accepted
S_LEAF_C5_ALIGNED_CHANNEL_DIRECTION.md gives
\[
 n_x<0,\quad w_U=1,\quad d\ge1,\quad
       0\le\delta<1/60,\quad h_A(n)\le\delta.
\tag{2}
\]
SAME_NORMAL_DIRECT_AND_SIDE_CHANNEL_EXCLUSION.md excludes parallel
root cycle forces. Hence n_y is nonzero: otherwise full root balance
would also make m horizontal. Reflect the whole packing so n_y>0;
then m_y<0 by its original positive force equation.

**Theorem.** The original direct normal satisfies \(m_x\le0\).
The equality \(m_x=0\) is retained as a physical residual case.

## 1. A direct normal toward the leaf forces a narrow root slider

Suppose \(m_x>0\), and write
\[
 n=(-c_0,s_0),\quad m=(c,-t),\qquad
 c_0,s_0,c,t>0,\quad c_0^2+s_0^2=c^2+t^2=1.
\tag{3}
\]
The unchanged ports and full torque equation give
\[
 p_{AU}=(\delta,a),\quad p_{AB}=(d,-b),\quad q_A=(q,0),
\qquad q=\delta+a c_0/s_0=d-bc/t.
\tag{4}
\]
Section 2 of D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md proves
q>0 for these same actual reserves and external resultants. Its
algebra needs only the nonnegative root proper lengths a/s_0,b/t:
both reserve-positive connections are strict, and the direct
coefficient is strict because the leaf and B resultant directions
differ. Its one-parallel-loaded-body alternative retains both
actual transverse means and also permits a zero root proper length.
Thus no original endpoint was discarded.

Equation (4) gives \(\delta\le q\le d\). Set
\[
 k=q-\delta=a c_0/s_0,\qquad L_0=a/s_0,\qquad 0\le k\le1.
\]
The support inequality \(a s_0\le\delta(1+c_0)\), multiplied by
1-c_0 and divided by positive s_0, gives \(L_0-k\le\delta\).
Consequently
\[
 a^2=L_0^2-k^2\le\delta(2k+\delta)
     \le2\delta+\delta^2=d^2-1
     <121/3600<1/20.
\tag{5}
\]
In particular \(a<1/4,\ b>3/4\). At delta=0, (5) and (4)
would already give q=0, a contradiction.

The incoming root direction -m=(-c,t) has positive dot product
with n. Its determinant with n is positive by
lambda e_x+mu n+nu m=0, with all magnitudes positive. The actual
turns and common moment therefore satisfy
\[
 0<\theta_A<\pi/2,\quad
 \theta_A+\theta_B+\theta_C=2\pi,\qquad
 {\cal H}=\mu q s_0>0
\tag{6}
\]
in cycle order A--C--B--A. A parallel loaded pair has its true
turn pi, exactly as in the cited D source.

## 2. The complete physical-radial B alternative is impossible

Put \(r_0^2=d^2+1/4\), the inner-vertex norm squared of a radial
S unit. The original direct application satisfies
\[
 |p_{BA}|^2=d^2+b^2>r_0^2,\qquad
                          m\cdot p_{BA}=dc+bt>0.
\tag{7}
\]
If B were radial, every point of its inner radial face would have
norm at most r_0, so that entire face, including both inner
vertices, is excluded. An outer circle vertex is unshareable.
At a minimum of B in direction m, its outer radial face requires
m dot p=-(d+1), and a tangential face requires m dot p=-1/2.
Both contradict (7). This covers strict vertex normals, both
radial axes and every original mean. B is therefore physical unique.

Also \(|p_{BA}|\ge d\ge1>R-\sqrt2\). The complete local argument
in Section 4 of the D source excludes a parallel unique B and
coincident B ports: their common non-circle vertex would be the
positive radial concurrence, hence the opposite radial-D vertex of
norm R-sqrt(2). Its full own-frame calculation consequently gives
\[
 \theta_B\le3\pi/4,\qquad
 \theta_B>\pi/2\ \Longrightarrow\ |p_{BV}-p_{BA}|\le1.
\tag{8}
\]
This retains B-owned axes, genuine shared means and the true direct
contact with A; A has not been assigned transmitter degree two.

If C were unique too, its two true transmitter neighbors would give
theta_C<=3pi/4, contradicting (6),(8). Thus only radial C remains.

## 3. Radial C must use its actual inner axis toward A

Its unchanged incoming application is \(p_{CU}=p_{AU}+n\). Hence
\[
 \begin{split}
 |p_{CU}|^2
 &=\delta^2+a^2+1+2h_A(n)\\
 &<1/3600+1/20+1+1/30
   =3901/3600<5/4\le r_0^2.
 \end{split}
\tag{9}
\]
At a radial endpoint of a reserve-one channel, outer vertices are
unshareable and the outer axis is too far out for another contained
unit. A tangential axis puts the entire next unit beyond projection
3/2 and thus a point beyond 5/2>R. These are the complete support
alternatives in Section 6 of the D source; they do not need A to
be loaded. Equation (9) excludes strict inner vertices. Therefore
\[
 e=n=(-c_0,s_0),\quad f=Je=(-s_0,-c_0),\quad
 C=[d,d+1]e+[-1/2,1/2]f,
\]
\[
              h_A(n)=\delta,\qquad p_{CU}=de-af.
\tag{10}
\]
Indeed the equality \(a s_0=\delta(1+c_0)\) gives
delta s_0=a(1-c_0), and then f dot p_AU=-a. If a=0,
that equality makes delta=0, already excluded after (5).
Thus the actual transverse coordinate -a is negative.
No equality of C's individual corner weights was used.

## 4. Both original B--V--C reserves contradict the actual ports

For \(w_V=1\), B is physically boundary-touching, so the complete
radial side-channel support theorem gives
\[
 p_{CV}=de+f/2,\quad g_{CB}=-\alpha e+\beta f,\quad
 \alpha,\beta>0,\quad\alpha^2+\beta^2=1.
\tag{11}
\]
The plus sign follows from the positive common moment: its determinant
is d beta+alpha/2>0; the minus alternative has negative determinant.
The original far port is
\[
                    p_{BV}=(d-\alpha)e+(1/2+\beta)f.
\]
Since d>=1 and alpha<1,
\[
            (p_{BV})_x=-(d-\alpha)c_0-(1/2+\beta)s_0<0.
\]
Its other B port has x=d>=1, so their distance is strictly greater
than one. C's two forces are nonparallel here. Thus theta_C<pi,
and (6) gives theta_B>pi/2, contradicting (8).

For \(w_V=\sqrt2\), original diagonal avoidance makes the C-to-B
normal a C side axis. Outer and tangential axes are excluded by
containment, leaving -e. B has own axis e and maximum e-coordinate
d-sqrt(2). Its unchanged normal toward A is -m=(-c,t), and
e dot(-m)=c_0 c+s_0 t>0. Its A application also maximizes e.
Therefore
\[
                      e\cdot(p_{CU}-p_{BA})=\sqrt2.
\tag{12}
\]
But (4),(9)'s port identity give
\[
 p_{CU}-p_{BA}=(-1,1)+e,\qquad
 e\cdot(p_{CU}-p_{BA})=1+c_0+s_0>2>\sqrt2,
\]
a contradiction. Both V widths and all physical B/C masks are
exhausted under m_x>0, proving the theorem.

## 5. Full residual and exact scope

The aligned family now has
\[
 n_x<0,\ n_y>0,\qquad m_x\le0,\ m_y<0.
\tag{13}
\]
When m_x<0, both actual root ports are the endpoints
(delta,a),(delta,-b) of A's full west side. When m_x=0,
the direct port is its original bottom-side mean, whose whole
interval remains. Neither residual is excluded here.

The original S gate still requires its complete three-extra capacity
argument, and the tilted root remains open as well. No numerical
diagnostic is a premise of this theorem. No new normal, force
deletion, replacement packing, Lean compilation or CI is used.
