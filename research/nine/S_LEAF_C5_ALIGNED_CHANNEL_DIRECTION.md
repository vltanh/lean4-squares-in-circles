# The real channel at an aligned S-leaf C5 load13 root points strictly away from the leaf

Date: October 26, 2026.

**Status: complete whole-domain necessary-direction theorem, accepted
after independent root review in
REVIEW_SAME_NORMAL_AND_S_C5_DIRECTION_ROOT_2026_10_26.md.**
This is a structural restriction, not a
closure of the remaining nonparallel S-leaf family.

Retain the exact positive component

    A--B--V--C--U--A, with a genuine S leaf L at A,

in the original radius window, with block loads exactly B,C. U,V
are true unloaded degree-two transmitters; A has its true degree
three; B,C have their true degree two. All nine squares, physical
circle masks, original force magnitudes and every actual mean remain.

Normalize the genuine leaf east. This theorem assumes the complete
ALIGNED root domain

\[
 L=[d,d+1]\times[-1/2,1/2],\qquad
 A=[\delta,d]\times[-b,a],\qquad
 \delta=d-1,\quad a,b\ge0,\quad a+b=1.
\tag{1}
\]

Both endpoint root sliders a=0 and b=0 are included. The physical
tilted-root family remains outside this source.

**Theorem.** The actual outward channel normal n from A through U
to C satisfies

\[
                                  n_x<0.
\tag{2}
\]

Together with SAME_NORMAL_DIRECT_AND_SIDE_CHANNEL_EXCLUSION.md,
the two root cycle forces are nonparallel as well. Neither assertion
discards a force or replaces an actual mean.

## 1. Exact radius, width and root-concurrence prerequisites

The actual A--U--C channel has reserve one and \(d\ge1\).
For \(d<1\), A contains the origin, so its channel support is
nonnegative. The sharp center bound at C would give
\(h+w_U\le d<1\), impossible. For \(d\ge1\), the actual root
point \((\delta,0)\) gives \(h\ge-\delta\), so
\(w_U\le d+\delta<31/30<\sqrt2\). Thus \(w_U=1\).
The unchanged support inequalities consequently give

\[
       0\le\delta<1/60,\qquad h=h_A(n)\le\delta.
\tag{3}
\]

Suppose contrary to (2) that \(n_x\ge0\). It cannot be horizontal:
east support d is greater than delta. Reflect the whole packing so
\(n_y>0\). Write the full root equation as

\[
 \lambda e_x+\mu n+\nu m=0,\qquad
             \lambda,\mu,\nu>0.
\tag{4}
\]

Then \(m_x<0,m_y<0\); put \(m=(-c,-t)\), \(c,t>0\),
\(c^2+t^2=1\). The root cycle pair is nonparallel. Its intersection
is \(q_A=(q,0)\), and its two exact proper-port coefficients are
\(a/n_y\ge0\) and \(b/t\ge0\).

The positive-radial-sign proof in Section 2 of
D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md applies to these same
actual reserves and external resultants. Its coefficient argument
needs nonnegative root proper lengths, not strict positivity: the
two reserve-positive connections are strict, and the direct AB
coefficient is strict because the actual leaf and B resultant
directions differ. Its one-parallel-loaded-body argument also keeps
both original transverse means and allows a zero root proper length.
Thus

\[
                                q>0.
\tag{5}
\]

This uses the original external resultant \(F_A=F_L\), not a
fictitious A circle force.

The support inequality in (3) is now
\(d n_x+a n_y\le\delta\). It gives

\[
 n_x<1/60,\quad n_y>14/15,\quad
       a<1/56,\quad b>55/56.
\tag{6}
\]

The actual direct root port and intersection identity are

\[
 p_{AB}=(\delta,-b),\qquad
                   q=\delta+b c/t>\delta.
\tag{7}
\]

The common moment, in cycle order A--C--B--A, is positive:
\({\cal H}=\mu q n_y>0\). The incoming root direction \(-m\)
and outgoing n have positive determinant by (4) and positive
scalar product. Therefore

\[
          0<\theta_A<\pi/2,\qquad
                \theta_A+\theta_B+\theta_C=2\pi,
\tag{8}
\]

with a parallel loaded body, if present, assigned its actual
directed-force turn pi. The proof is exactly the three-direction
argument of the cited D source; no bounded radial concurrence is used.

## 2. B must be physical unique, with its complete local turn cover

Put \(r_0^2=d^2+1/4\), the squared norm of a physical radial
unit's inner vertices. Equations (6)--(7) give

\[
 |p_{AB}|>55/56>R-\sqrt2,\qquad
 |p_{AB}|^2\le\delta^2+1<901/900<5/4\le r_0^2.
\tag{9}
\]

If B were physical radial, the small norm in (9) would put its
actual A application in the relative interior of its inner face.
Its radial direction would be \(e=m=(-c,-t)\), so that

\[
                     d=e\cdot p_{BA}=-c\delta+bt<1\le d.
\]

Here t<1 because c>0, and b<=1. This contradiction remains strict
at the critical endpoint d=1 and every original slider endpoint.
Thus B is physical unique.

The large norm in (9) excludes coincident B ports exactly as in
Section 4 of the D source: a nonparallel unique concurrence equal
to a non-circle vertex would be the opposite radial-D vertex, of
norm \(R-\sqrt2\). The complete own-axis local proof therefore gives

\[
        \theta_B\le3\pi/4,\qquad
        \theta_B>\pi/2\ \Longrightarrow\
                        |p_{BV}-p_{BA}|\le1.
\tag{10}
\]

It retains the actual direct contact with A, all B-owned or shared
axes, and every original endpoint mean. C has two true transmitter
neighbors, so if C were also physical unique its full local bound
would be \(\theta_C\le3\pi/4\). That would contradict (8).
Consequently only the physical-radial C mask needs to be excluded.

## 3. A radial C forces the original A--U--C normal to be vertical

Write C in its actual radial frame

    C=[d,d+1]e+[-1/2,1/2]f, f=Je.

For its channel toward A, its outer radial face and outer vertices
are impossible by containment and unshareability. A tangential axis
would put the whole A beyond projection 3/2, so its width at least
one would exceed R. The only remaining choices are its inner-axis
face or a strict inner vertex.

If \(n_x>0\), the root application is \(p_{AU}=(d,a)\).
An inner-axis C application would put
\(p_{AU}=\delta e+yf\), \(|y|\le1/2\), whose norm is less
than one, contrary to \(|p_{AU}|\ge d\ge1\).
For a strict inner C vertex, the actual far application would give

\[
 r_0^2=|p_{AU}+n|^2
       =|p_{AU}|^2+1+2h\ge d^2+1>d^2+1/4,
\]

also impossible. Thus \(n_x=0\), and the actual ports are

\[
                   p_{AU}=(q,a),\qquad p_{CU}=(q,a+1).
\tag{11}
\]

Exactly as in Section 6.1 of the D source, C's frame can now be
written

\[
 e=(u,v),\quad f=(-v,u),\quad
 u\ge0,\quad v>60/61,\quad
 p_{CU}=d e+y_Af,\quad y_A<0.
\tag{12}
\]

For an inner-axis C contact, e is vertical and \(y_A=-q<0\).
For a strict inner vertex, q>0 forces u>0 and \(y_A=-1/2\);
then \(a+1=dv-u/2\ge1\) gives \(v>1/d>60/61\).
The cases a=0 and delta=0 are included in these strict comparisons.

## 4. Both actual B--V--C widths are impossible

If \(w_V=1\), its physical boundary endpoint B makes C's port
the strict plus inner vertex:

    p_CV=d e+f/2, C-to-B normal g=-alpha e+beta f,
    alpha,beta>0, alpha^2+beta^2=1.

The plus sign follows from the positive common moment in (8).
Equations (12) give \((p_{CV})_y\ge a+1\), and \(g_y>-1\).
Hence the real B application \(p_{BV}=p_{CV}+g\) has height
strictly greater than a. Its other port in (7) has height a-1.
The two B ports are more than one unit apart.

The C forces are nonparallel in this side case, so
\(\theta_C<\pi\); (8) gives \(\theta_B>\pi/2\). This contradicts
the complete unique-B chord bound in (10).

If \(w_V=\sqrt2\), diagonal avoidance makes the actual C-to-B
normal a C side axis. Outer and tangent axes are impossible by
the same width/containment argument, leaving only \(-e\).
B owns the diagonal endpoint axis and has maximum e-coordinate
\(d-\sqrt2\). Since its actual normal toward A is \((c,t)\),
with c,t>0, its A application also maximizes e by (12). Thus

\[
 e\cdot(p_{CU}-p_{BA})=\sqrt2.
\]

But (11),(7) give

\[
 e\cdot(p_{CU}-p_{BA})
                 =(q-\delta)u+2v>120/61>\sqrt2.
\]

This is the final contradiction. Both original transmitter-width
alternatives and every B/C physical mask have been covered.

## 5. Scope

Every contrary aligned-root channel with \(n_x\ge0\) is excluded
throughout the complete radius and slider domain. Thus the actual
normal must satisfy (2). The separate radius-free same-normal theorem
also excludes the whole parallel root-pair alternative, whether A
is aligned or tilted.

The S-leaf C5 load13 family is not closed by these two necessary
restrictions. In particular an aligned root with strictly leftward,
nonparallel channel remains, as does the entire tilted nonparallel
root family. No original gate or computational sign count is changed
by this source, and no selected normal or physical mean was replaced.
No Lean compilation or CI was used.
