# A D leaf excludes the complete C5 load13 attachment

Date: October 26, 2026.

**Status: complete hand core exclusion, accepted after root and separate
independent full-source and original-domain reviews.** See
REVIEW_D_LEAF_C5_SEPARATED_LOADS_ROOT_2026_10_26.md and
REVIEW_D_LEAF_C5_SEPARATED_LOADS_CERTIFICATE_REDUCTION_2026_10_26.md.
No numerical sign packet is used.
The original S-leaf alternative is not claimed here.

Work with the complete selected physical certificate and all nine
original unit squares in

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad \delta=d-1<\frac1{60}.
\tag{1}
\]

The exact positive component is the cycle

    A--B--V--C--U--A

with one genuine D leaf L at A. The block loads are exactly B,C;
U,V are the two true unloaded degree-two bodies. Thus A retains its
true degree three, and B,C retain their true degree two. In the
original C5 labels these are

    A=0, B=1, V=2, C=3, U=4.

Every physical B/C circle mask, every individual radial corner weight,
all actual side means and their endpoints, both transmitter-width
alternatives, and all three additional squares remain present.

**Theorem.** This entire physical D-leaf family is impossible as a
positive six-body core. In particular it has no nine-square completion.

## 1. The actual root channel forces a high radius and a narrow direction

Normalize the actual D leaf direction east. Its genuine clear root is

\[
 A=[-s,\rho]\times[-b,a],\qquad
 \rho=R-\sqrt2,\quad s=1-\rho,\quad
 a,b>0,\quad a+b=1.
\tag{2}
\]

The actual leaf application is \((\rho,0)\), and its outward root
force is \(\lambda e_x\), \(\lambda>0\). The full side-interior
root slider is retained in \(a,b\).

The channel A--U--C has an actual outward normal n, support
\(h=h_A(n)\), and reserve \(w_U\in\{1,\sqrt2\}\). Since the
origin is in the OPEN interior of A, \(h>0\). Its actual endpoint
half-planes and the sharp contained-unit center bound give

\[
 C\subseteq\{x:n\cdot x\ge h+w_U\},\qquad
 h+w_U+\frac12\le n\cdot c_C\le |c_C|\le d+\frac12.
\tag{3}
\]

As \(d<61/60<\sqrt2\), this forces

\[
 w_U=1,\qquad 0<h\le\delta,\qquad d>1.
\tag{4}
\]

Consequently \(R^2>17/4\), and in particular

\[
 \frac35<\rho<\frac34,\qquad
 \frac14<s<\sqrt2-1<\frac12.
\tag{5}
\]

For the lower bound, \(R>\sqrt{17}/2>41/20\) and
\(\sqrt2<29/20\). The upper bound follows, for example, from
\(R<25/12\) and \(\sqrt2>7/5\). The bound on s uses \(R>2\).
Every replacement is strict throughout the contrary domain.

The horizontal support contribution of (2) is at least
\(|n_x|/4\), while the vertical contribution is nonnegative.
Therefore

\[
 |n_x|<\frac1{15},\qquad |n_y|>\frac{14}{15}.
\tag{6}
\]

Reflect the whole configuration horizontally so that \(n_y>0\).
Write m for the actual outward unit normal from A directly to B,
and \(\mu,\nu>0\) for the root forces in directions n,m. The
complete root balance is

\[
 \lambda e_x+\mu n+\nu m=0.
\tag{7}
\]

Thus \(m_y<0\), and the two root cycle forces are nonparallel.
Indeed parallelism would make their nonzero sum parallel to n,
contrary to (7) and \(n_y\ne0\).

## 2. The genuine root concurrence has positive radial sign

The two root cycle force lines meet at \(q_A=(q,0)\). Their
intersection is on the horizontal line by the full root torque
equation and its actual horizontal leaf force. The upper and lower
root supports in (2) give the exact proper-port lengths

\[
 p_{AU}-q_A=\frac{a}{n_y}n,\qquad
 p_{AB}-q_A=\frac{b}{-m_y}m.
\tag{8}
\]

Both coefficients are positive. No assumption about the sign of q
has entered (8). We now prove

\[
                              q>0.
\tag{9}
\]

This needs the actual leaf force as an external resultant at A,
not a false circle load on A. Put

    F_A=lambda e_x, F_B=the original B circle resultant,
    F_C=the original C circle resultant.

These are nonzero and sum to zero by whole-component force balance.
They are noncollinear: the complete three-load prerequisite gives
distinct radial resultant directions for the three actual loaded
bodies L,B,C. All three external origin moments are zero.

At each nonparallel B or C, Lemma 1.1 of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md applies at its true degree two.
Its actual concurrence is a positive multiple of its own original
circle resultant, and both actual ports are on nonnegative outward
normal rays from it. This lemma permits both physical circle masks
and does not require a boundary neighbor.

### 2.1. Both loaded pairs are nonparallel

Use (8) at A and the genuine proper-port relations at B,C.
The exact unloaded channels then give

    q_C-q_A=ell_AC f_AC,
    q_B-q_C=ell_CB f_CB,
    q_A-q_B=ell_BA f_BA,

with positive coefficients ell. The two reserve-positive channels
make their coefficients strictly positive. The direct AB coefficient
cannot vanish either: that would identify q_A and q_B, whereas q_B
is a nonzero positive multiple of F_B and q_A is a real multiple of
the independent F_A.

The full equations are

    F_A=f_BA-f_AC, F_C=f_AC-f_CB, F_B=f_CB-f_BA.

The exact coefficient comparison in
RADIAL_TRIANGLE_CONCURRENCE.md, Section 2, now applies algebraically.
For completeness, writing
\(\ell=\ell_{AC}+\ell_{CB}+\ell_{BA}\), it gives the coefficient
of \(F_A\) in \(q_A\) as

\[
                  \frac{\ell_{AC}\ell_{BA}}{\ell}>0.
\tag{10}
\]

The original reserve lengths are included in these ell coefficients.
No physical triangle contact or fictitious A circle load is used.
This proves (9) in this case.

### 2.2. One loaded pair is parallel

At most one of B,C can have parallel forces: if both did, all three
cycle force directions would be collinear, contradicting the already
nonparallel root pair.

Let K be the parallel loaded body, and I=A,J the other loaded body.
The local parallel-load classification in
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md, Section 1, says that both
outward K normals point in the same direction \(-e\), opposite its
circle resultant. No outward \(+e\) support is possible: it exposes
an unshareable circle corner or the too-far outer radial face. This
local conclusion needs no whole-cycle premise.

Use coordinates along e and its perpendicular. Let \(y_I,y_J\)
be the transverse coordinates of K's actual applications toward I,J,
and let their positive magnitudes be \(\alpha,\beta\). Full K torque
gives

\[
                         \alpha y_I+\beta y_J=0.
\tag{11}
\]

The real channels and proper ports preserve transverse coordinate,
so the transverse coordinates of \(q_I,q_J\) are \(y_I,y_J\).
Since \(q_J\) is a positive multiple of the actual \(F_J\), and
\(F_J\) is not parallel to e, \(y_J\ne0\). Thus (11) makes
\(y_I,y_J\) strictly opposite in sign.

On the remaining I--J connection, proper ports and the unchanged
reserve give \(q_J-q_I=L f\) for a positive L and the actual
force f directed from I to J. Positivity follows also from their
different transverse coordinates. The complete endpoint equations are

    F_I+alpha e+f=0, F_J+beta e-f=0.

Their transverse components show that \(F_I\) has the same nonzero
transverse sign as \(q_I\): both are opposite to the sign of
\(f_\perp\), which is the sign of \(y_J-y_I\). Since \(q_I\)
is already a real multiple of \(F_I\), that multiple is positive.
This again proves (9).

This argument keeps both original application means at the parallel
body. It does not assign that body an artificial concurrence.

## 3. Exact root ports and positive cycle turns

If \(n_x<0\), the upper root application is \((-s,a)\).
Equations (6),(8) would give

\[
 q=-s+a\frac{|n_x|}{n_y}
                 <-\frac14+\frac1{14}<0,
\]

contrary to (9). Thus \(n_x\ge0\). Equation (7) now gives
\(m_x<0\), so write

\[
 m=(-c,-t),\qquad c,t>0,\quad c^2+t^2=1.
\tag{12}
\]

The actual direct application and root-coordinate identities are

\[
 p_{AB}=(-s,-b),\qquad q=-s+b\frac ct>0,\qquad q\le\rho.
\tag{13}
\]

If \(n_x>0\), the actual upper application is \((\rho,a)\);
if \(n_x=0\), it is the unchanged top-side mean \((q,a)\).
Its full support bound gives

\[
 a n_y\le h\le\delta,\qquad
                   a<\frac1{56},\quad b>\frac{55}{56}.
\tag{14}
\]

Two useful genuine-point norm comparisons are therefore

\[
 |p_{AB}|>\rho,\qquad
 |p_{AB}|^2=s^2+b^2<\frac54
                        <d^2+\frac14=:r_0^2.
\tag{15}
\]

Orient the actual cycle as A--U--C--V--B--A. Its common positive
origin moment is

\[
                    {\cal H}=\mu\det(q_A,n)=\mu q n_y>0.
\tag{16}
\]

Let \(\theta_A,\theta_C,\theta_B\) denote the successive positive
turns of the three directed channel-force directions. At A the
incoming direction is \(-m=(c,t)\), and the outgoing one is n.
Their determinant is positive by (7), while their dot product is
\(c n_x+t n_y>0\). Hence

\[
                          0<\theta_A<\frac\pi2.
\tag{17}
\]

At a nonparallel loaded body its proper positive radial concurrence
and (16), together with its full force equation, give a strictly
positive turn less than pi, exactly as in the local determinant
calculation of SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. At a parallel
loaded body both outward normals have the same sign, so its directed
turn is pi. Consequently the three positive turns, each at most pi
and with (17) strict, make one complete circuit:

\[
                 \theta_A+\theta_B+\theta_C=2\pi.
\tag{18}
\]

This statement remains valid in the one-parallel-body case. It is an
identity among the three original force directions, not an assumption
that every concurrence is inside its physical square.

## 4. The complete unique-corner local facts needed here

At C both actual neighbors are true unloaded transmitters, so the
full local unique-corner calculation in
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md, Section 1, applies:

\[
 C\hbox{ physically unique}\quad\Longrightarrow\quad
                            \theta_C\le3\pi/4.
\tag{19}
\]

This is its local calculation only; no C6 premise or diagonal-count
premise is used.

The same conclusions hold at B, with one direct neighbor A, after
checking the only extra issue: distinctness of B's actual ports.
If B were physical unique and parallel, the complete local parallel
classification would make it radial D, with both applications the
radial inner vertex and origin moment zero, contrary to (16).
Thus its concurrence is proper and nonparallel.

If its two applications coincided in a side interior of B, their
normals would be parallel. If they coincided at a B vertex, their
intersection q_B would be that vertex. A non-circle vertex on the
positive ray of B's unique circle corner can only be the opposite
radial-D vertex, at norm \(R-\sqrt2=\rho\). This contradicts
\(|p_{AB}|>\rho\) in (15). Hence B's two actual ports are distinct.

Here is why the remainder of the original local proof then has no
neighbor-degree requirement. In positive own axes put B's unique
corner at \((a_0,b_0)\), with \(a_0,b_0>1/2\), and
write \(q_B=\tau(a_0,b_0)\) inside B, \(0<\tau\le1\). Set

    X=1-(1-tau)a_0, Y=1-(1-tau)b_0, 0<=X,Y<=1.

The positive moment permits only the incoming outer-right or inner-bottom
axis and the outgoing outer-top or inner-left axis. An outer-axis case
has turn at most pi/2 by the component signs of the actual force
balance. Two axes give turn at most pi/2. In a single inner-axis case,
the only vertex choice with turn above pi/2 is the other vertex on
that same inner side. Its exact normal-line calculation gives turn
at most 3pi/4, including the original side mean and endpoint.

With neither normal a B side axis, the distinct applications are
vertices. A single zero proper length would make the other normal
a B side axis, so both proper lengths are positive. The complete
ordered vertex list from the positive moment is

    lower-right to upper-left;
    lower-left to upper-left, with a_0>b_0;
    lower-right to lower-left, with b_0>a_0.

The first pair has nonnegative scalar product of its directed
normal vectors, so turn at most pi/2. For each of the other two,
the scalar product plus determinant of the unnormalized directed
vectors is exactly

\[
                         X(1-X)+Y(1-Y)\ge0.
\tag{20}
\]

Its determinant is positive, giving turn at most 3pi/4. These last
two pairs lie on one inner side of B. This is the complete local
support cover, and uses no force equation at A.

We have therefore proved, with all original mean endpoints,

\[
 \begin{split}
 B\hbox{ physically unique}&\Longrightarrow\theta_B\le3\pi/4,\\
 B\hbox{ physically unique and }\theta_B>\pi/2
       &\Longrightarrow |p_{BV}-p_{BA}|\le1.
 \end{split}
\tag{21}
\]

In particular B and C cannot BOTH be physical unique: (17),(19),(21)
would make the sum in (18) strictly less than \(2\pi\).

## 5. A physical radial B has a fixed inner-axis contact with A

This short fact will be used in either remaining physical mask.
A physical radial unit, in its actual radial frame e,f, is

\[
             [d,d+1]e+[-1/2,1/2]f,\qquad f=Je.
\tag{22}
\]

Every boundary point outside the relative interior of its inner
radial face has norm at least \(r_0=\sqrt{d^2+1/4}\): on a
tangential side the minimum is its inner vertex, and its outer side
is farther still. If B is radial, (15) consequently puts its real
contact \(p_{BA}\) in the strict interior of that inner face.
Its actual outward normal toward A is \(-e\). Thus

\[
 e=m=(-c,-t),\qquad f=(t,-c),\qquad
                  d=s c+b t.
\tag{23}
\]

If the B--V--C channel has reserve one, its radial B port is one of
the two strict inner vertices. Indeed the geometric support cover of
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, Section 1, needs only
the actual reserve-one channel and a physical boundary far endpoint.
Its inner-axis case would end too close to zero to belong to C; the
outer and tangent cases exceed the containing circle. Therefore in
this side-channel case both B applications lie on its inner face, so

\[
                  B\hbox{ radial},\ w_V=1
                    \quad\Longrightarrow\quad
                         |p_{BV}-p_{BA}|\le1.
\tag{24}
\]

No equality of the two actual B circle weights is imposed.

## 6. The entire physical-radial C case is impossible

We first normalize C's actual radial frame as in (22). For its
channel toward A, the outer face or a positive outer component is
impossible by circle containment or the unshareable circle corners.
A tangential axis would put A beyond height \(1/2+1=3/2\),
and A's width at least one would then exceed \(R<5/2\).
Thus the complete C-to-A support choices are its inner radial face
with its inner-axis normal, or a strict inner vertex.

### 6.1. The actual A-to-C normal must be vertical

Suppose \(n_x>0\), so \(p_{AU}=(\rho,a)\).
If C uses its inner-axis normal, \(n=e\) and its actual far point is
\(d e+yf\), \(|y|\le1/2\). The root application would be
\(\delta e+yf\), with squared norm at most
\(\delta^2+1/4<901/3600<9/25\), contradicting
\(|p_{AU}|\ge\rho>3/5\).

If instead C uses a strict inner vertex, its application has squared
norm \(r_0^2\). But the exact reserve-one displacement gives

\[
 |p_{AU}+n|^2=|p_{AU}|^2+1+2h
         >1+\rho^2>\frac{34}{25}
         >\frac{4621}{3600}>r_0^2.
\tag{25}
\]

The middle rational reserve is \(11/144\). Both choices contradict
the original port norm. Hence \(n_x=0\), and the real ports are

\[
                    p_{AU}=(q,a),\qquad
                    p_{CU}=(q,a+1),\qquad q>0.
\tag{26}
\]

Write C's radial axis as \(e=(u,v)\), \(f=(-v,u)\).
If its A interface is inner-axis, then \(u=0,v=1\),
\(a=\delta\), and \(p_{CU}=d e+y_Af\) with \(y_A=-q<0\).
If that interface is a strict inner vertex, its outward normal is
\(-e_y\). Hence \(v>0\), and its transverse sign is the opposite
of u. The positive first coordinate q of (26) then forces \(u>0\)
and

\[
                       p_{CU}=d e-\frac12 f.
\]

In this strict case \(a+1=dv-u/2>1\), giving \(v>1/d>60/61\).
Both alternatives can be recorded together as

\[
 u\ge0,\quad v>60/61,\quad
 p_{CU}=d e+y_Af,\quad y_A<0.
\tag{27}
\]

### 6.2. A side-normal B--C channel forces impossible port separation at B

Suppose \(w_V=1\). Since B is physically boundary, the full radial
support cover makes the C-to-B channel normal and port

\[
 g=-\alpha e+\beta f,\qquad
 p_{CV}=d e+\frac12 f,\qquad
 \alpha,\beta>0,\quad\alpha^2+\beta^2=1.
\tag{28}
\]

The plus sign is forced by the unchanged common moment (16):
the minus-inner-vertex alternative has negative
\(\det(p_{CV},g)\), whereas the plus alternative has
\(d\beta+\alpha/2>0\). This also retains the inner-axis A mean
when it is an endpoint of a genuine shared interval.

Equations (27)--(28) give

    (p_CV)_y >= (p_CU)_y = a+1.

Moreover \(g_y=-\alpha v+\beta u>-1\); equality would require
\(g=-e_y\), which is incompatible with \(\beta>0,u\ge0\).
The actual far application on B is \(p_{BV}=p_{CV}+g\), so

\[
                         (p_{BV})_y>a.
\tag{29}
\]

Its other actual application is \(p_{BA}=(-s,a-1)\).
Thus the two B ports are more than one unit apart.

If B is radial this contradicts (24). If B is unique, the C forces
in (26),(28) are nonparallel, hence \(\theta_C<\pi\).
Together with (17)--(18), this gives \(\theta_B>\pi/2\),
and (21) again says its actual port separation is at most one.
Both physical B masks are excluded.

### 6.3. A diagonal B--C channel contradicts an exact support coordinate

Suppose \(w_V=\sqrt2\). The compatible diagonal-transmitter
classification makes the actual C normal a C side axis. Its outer
radial axis is impossible, and a tangent axis would put B beyond
projection \(1/2+\sqrt2\), whose additional width one exceeds R.
Only the inner axis remains:

    C-to-B normal = -e, p_CV=d e+y f.

The actual diagonal endpoint at B lies in a B side interior, so B's
own axes are e,f and its maximum e-coordinate is \(d-\sqrt2\).
Its normal toward A is \(-m=(c,t)\), with c,t>0. By (27) this
normal has positive e-component. Its original A application must
therefore also have e-coordinate \(d-\sqrt2\).

Since \(e\cdot p_{CU}=d\), the real port difference would obey

\[
 e\cdot(p_{CU}-p_{BA})=\sqrt2.
\tag{30}
\]

But (26) and (13) give \(p_{CU}-p_{BA}=(q+s,2)\), so

\[
 e\cdot(p_{CU}-p_{BA})=(q+s)u+2v
                              >120/61>\sqrt2,
\]

contradicting (30). This proof allows either physical B mask and all
original diagonal endpoint means.

The physical-radial C case is completely excluded.

## 7. The remaining unique C / radial B mask is also impossible

By Section 4, the only physical mask left would have C unique and B
radial. Equation (23) applies. First it forces

\[
                                t>c.
\tag{31}
\]

Indeed (14),(5) give \(b>s\) and \(s+b<\sqrt2\).
If \(c\ge t\), then

\[
 \begin{split}
 d=s c+b t
  &=\frac{s+b}{2}(c+t)+\frac{s-b}{2}(c-t)\\
  &\le\frac{s+b}{\sqrt2}<1,
 \end{split}
\]

contrary to (4).

If \(n_x>0\), its actual root application is \((\rho,a)\), so

    q+s=1-a n_x/n_y > 1-a=b

by (6). Equation (13) would give \(c/t=(q+s)/b>1\),
contradicting (31). Hence again \(n_x=0\), and (26) holds for
the original A-to-C channel.

### 7.1. The side-channel center gap is too large

If \(w_V=1\), B's actual center is
\((d+1/2)m\), whose vertical coordinate is

    -(d+1/2)t < -3/(2 sqrt(2)).

The whole C lies in \(y\ge a+1\), by its actual root channel,
so its center has vertical coordinate at least \(a+3/2>3/2\).
Thus the center distance between B and C is strictly greater than

\[
                    \frac32+\frac3{2\sqrt2}>1+\sqrt2.
\tag{32}
\]

The strict difference on the right is
\((1-1/\sqrt2)/2>0\). But their unchanged reserve-one applications
are distance one apart, and each application's distance from its
own unit center is at most \(1/\sqrt2\). The triangle inequality
gives \(|c_B-c_C|\le1+\sqrt2\), contradicting (32).

### 7.2. The diagonal channel puts the C port below height one

If \(w_V=\sqrt2\), the same complete radial-axis support argument
as in Section 6.3 makes B's actual channel normal toward C equal
to \(-e\), where

    e=m=(-c,-t), f=(t,-c), c,t>0.

Write its original diagonal application as \(d e+y f\),
\(|y|\le1/2\). The far C application is

\[
                       p_{CV}=(d-\sqrt2)e+y f.
\tag{33}
\]

C owns the diagonal endpoint axis, so its axes are e,f and its
maximum e-coordinate is \(d-\sqrt2\). Its actual normal toward
U and A is \(-e_y\), whose two own components are t,c>0.
Consequently \(p_{CU}\) is the vertex maximizing BOTH e and f.
As \(f_y=-c<0\), it has vertical coordinate no larger than that
of the actual same-e-face point (33). Hence

\[
 \begin{split}
 (p_{CU})_y
  &\le (p_{CV})_y
   =(\sqrt2-d)t-cy\\
  &\le(\sqrt2-d)t+c/2
   <\sqrt2-\frac12<1.
 \end{split}
\tag{34}
\]

Here \(d>1\), \(t,c\le1\), and \(\sqrt2<3/2\).
But its actual root channel in (26) gives
\((p_{CU})_y=a+1>1\). This is the final contradiction.

## 8. Exact original gate, physical scope and retained limits

The two width alternatives \(w_V=1,\sqrt2\) are exhausted.
The complete physical B/C mask cover consists of unique/unique,
either ordered unique/radial mask, and radial/radial. Section 4
excludes unique/unique; Section 6 excludes every mask with C radial;
Section 7 excludes the last ordered mixed mask. Parallel loaded
forces were retained in the concurrence and turn reductions, and
no radial concurrence was assumed bounded or inside its body.

This supplies the entire existing obligation

    M6.B5L.C5.L13.D

with its original root-preserving reflection, full D root slider,
positive force ratios, every physical circle mask and individual
corner-weight endpoint, every original shared-side mean, all extra
physical contacts and all three actual completion squares.

The cycle roles are never created by deleting a force. A keeps its
true leaf force and degree three; U,V keep their true unloaded
degree-two equations; B,C keep their genuine positive degree two.
The proper-port algebra preserves both physical transmitters rather
than substituting segments for occupied bodies.

The companion original S-leaf gate M6.B5L.C5.L13.S remains outside
this source. No whole C5 rooted type or larger coarse cell is declared
closed. No shared ledger was changed, and no Lean compilation, CI,
numerical pose premise or computational sign certificate is used.
