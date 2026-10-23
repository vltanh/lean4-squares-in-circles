# A seven-loaded physical stress below the proposed nine-square radius

**Status: exact counterexample to a component-only radius bound.** There
is a physical packing of seven unit squares in the declared research
window whose positive contact graph is a seven-cycle, whose seven
bodies all carry positive circle load, and whose physical contact
forces satisfy both force and torque balance. Its radius satisfies

\[
 \frac{79}{40}<R<\frac{103}{50},\qquad
 R^2<\frac{17}{4}<Q=\frac{1105}{256}.
\]

An eighth, arbitrary origin-centered unit square fits strictly inside
this ring. This is not a nine-square counterexample and makes no claim
of local or global optimality. It shows that a proof of the nine-square
bound cannot obtain that bound from the existence of a three-or-more-
loaded physical stress component alone. The geometry of its completion
by the remaining squares, or an additional necessary condition of
minimality, is indispensable.

All contacts and all multipliers below are explicit. In particular, the
example does not assume that an abstract balanced force diagram can be
realized by squares.

## 1. The seven poses

Set

\[
 \delta=\frac{\pi}{7},\qquad s=\sin\delta,\qquad c=\cos\delta,
\]
\[
 k=\frac{1+\sin 2\delta+\cos 2\delta}{4s}
   =\frac{c(c+s)}{2s},\qquad d=\frac{c-s}{2}.
\]

Here \(k,d>0\). Choose \(t\in(-\pi/2,0)\) by

\[
 \tan t=-\frac d k,\qquad
 \rho=\sqrt{k^2+d^2},\qquad \psi=\delta+t.
\]

Then

\[
 \rho\cos t=k,\qquad \rho\sin t=-d.
 \tag{1}
\]

Moreover

\[
 0<\frac d k
   =\frac{s(c-s)}{c(c+s)}
   <\frac{s}{c}=\tan\delta,
\]

so \(-\delta<t<0\) and \(0<\psi<\delta<\pi/4\).

For \(e_\alpha=(\cos\alpha,\sin\alpha)\), and for indices \(j\) modulo
seven, define

\[
 \theta_j=2j\delta,\qquad
 C_j=\rho e_{\theta_j},\qquad
 u_j=e_{\theta_j+\psi},\qquad v_j=Ju_j,
\]
\[
 S_j=C_j+[-1/2,1/2]u_j+[-1/2,1/2]v_j.
 \tag{2}
\]

Thus each \(S_j\) is a unit square, and successive squares and centers
are rotations of their predecessors through \(2\pi/7\).

## 2. The containing circle and its unique corner on each square

In the own frame \(u_j,v_j\), the center \(C_j\) has coordinates

\[
 (\rho\cos\psi,-\rho\sin\psi),
\]

whose first coordinate is strictly positive and second strictly
negative. Consequently the unique farthest corner of \(S_j\) is

\[
 z_j=C_j+\tfrac12u_j-\tfrac12v_j.
 \tag{3}
\]

Indeed, for a corner offset \(a\), its squared norm is
\(\rho^2+1/2+2C_j\cdot a\), and the stated signs uniquely maximize the
last term.

Resolve \(z_j\) in the frame with first direction \(e_{\theta_j+t}\).
Its transverse coordinate is

\[
 -\rho\sin t+\tfrac12(\sin\delta-\cos\delta)=d-d=0,
\]

and its first coordinate is

\[
 \rho\cos t+\tfrac12(c+s)
 =k+\tfrac12(c+s)
 =\frac{(c+s)^2}{2s}
 =c+\frac1{2s}.
\]

Therefore, with

\[
 \boxed{R=c+\frac1{2s}},
\qquad
 z_j=R e_{\theta_j+t}.
 \tag{4}
\]

Every square lies in the closed disk of radius \(R\), and exactly one
of its corners lies on the circle.

## 3. The actual contact graph is the seven-cycle

Orient the prospective edge \(j\to j+1\), and choose its normal

\[
 n_j=v_j.
\]

Since \(0<2\delta<\pi/2\), the support half-widths in this direction
are

\[
 h_j(n_j)=\tfrac12,\qquad
 h_{j+1}(n_j)=\tfrac12(\sin2\delta+\cos2\delta).
\]

On the other hand,

\[
 n_j\cdot(C_{j+1}-C_j)
 =2\rho s\cos(\delta-\psi)
 =2ks
 =\tfrac12(1+\sin2\delta+\cos2\delta).
 \tag{5}
\]

Thus the corresponding support lines coincide, and \(S_j,S_{j+1}\)
have disjoint interiors. Their actual common point is

\[
 p_j=C_{j+1}-\tfrac12u_{j+1}-\tfrac12v_{j+1}.
 \tag{6}
\]

In the frame of square \(j\), direct substitution of (1) gives

\[
 p_j=C_j+\xi u_j+\tfrac12v_j,\qquad
 \xi=\sin2\delta-\tfrac12.
 \tag{7}
\]

For completeness, the center difference in that frame has coordinates
\(2sd,2sk\). Adding the corner offset in (6) gives

\[
 2sd+\tfrac12(\sin2\delta-\cos2\delta)
   =\sin2\delta-\tfrac12
\]

in the \(u_j\) direction, and \(1/2\) in the \(v_j\) direction.
Because \(\pi/8<\delta<\pi/6\), we have \(0<\xi<1/2\).
Hence \(p_j\) is a corner of \(S_{j+1}\) in the relative interior
of a side of \(S_j\). It is the unique contact point: the support
minimum of \(S_{j+1}\) in direction \(n_j\) is unique, since

\[
 n_j\cdot u_{j+1}=\sin2\delta>0,\qquad
 n_j\cdot v_{j+1}=\cos2\delta>0.
\]

These are legitimate physical side–vertex contacts of the type in
PHYSICAL_CONTACT_STRESS.md, Section 2.1. Their normals are not merely
abstract forces or fixed separating directions chosen at noncontacts.

Every nonneighbor pair has cyclic index distance two or three. Its
center distance is at least \(2\rho\sin2\delta\). Since \(\rho>k\),
\(\delta<\pi/6\), and \(c+s>1\),

\[
 2\rho\sin2\delta
 >2k\sin2\delta
 =2c^2(c+s)
 >\frac32>\sqrt2.
 \tag{8}
\]

The circumradius of a unit square is \(1/\sqrt2\); hence the closed
squares of every nonneighbor pair are strictly disjoint. This proves
that the full physical contact graph, not just a chosen subgraph, is
exactly \(C_7\).

## 4. Positive force and torque balance

Put the same contact multiplier \(\mu>0\) at every contact (6), with
normal \(n_j\) on edge \(j\to j+1\). Put one circle multiplier

\[
 \lambda_j=\frac{\mu s}{R}>0
 \tag{9}
\]

at the unique circle corner \(z_j\) of each square.

The contact-force sum on square \(j\) is

\[
 \mu(n_j-n_{j-1})
 =-2\mu s\,e_{\theta_j+t},
\]

whereas its circle-force term is

\[
 2\lambda_j z_j
 =2\mu s\,e_{\theta_j+t}.
\]

Their sum is zero. This uses exactly the sign convention of the
gradient equations in PHYSICAL_CONTACT_STRESS.md.

The pair \((p_j,n_j)\) is obtained from \((p_{j-1},n_{j-1})\) by a
rotation through \(2\delta\), so

\[
 \det(p_j,n_j)=\det(p_{j-1},n_{j-1}).
\]

The total contact torque about the origin on square \(j\) is therefore

\[
 \mu\det(p_j,n_j)-\mu\det(p_{j-1},n_{j-1})=0.
\]

The circle-force torque is zero because that force acts at \(z_j\)
parallel to \(z_j\). Force balance then makes the torque about the
square center zero as well. Both angular and translation stationarity
hold.

Taking

\[
 \mu=\frac{R}{7s},\qquad \lambda_j=\frac17
\]

normalizes the circle multipliers to sum to one. Thus this is a
connected positive physical stress component with seven positive
contact atoms and seven positive circle atoms. It satisfies the
existing atom bound without requiring extra atoms.

## 5. Exact isolation of the radius inside the research window

The following rational comparisons avoid relying on a numerical
evaluation of (4). Let

\[
 f(x)=8x^3-4x^2-4x+1.
\]

The identity \(\cos3\delta=-\cos4\delta\) gives
\((c+1)f(c)=0\), hence \(f(c)=0\).
Since \(c>\cos(\pi/6)=\sqrt3/2>4/5\), and \(f\) is strictly
increasing on \([4/5,1]\), the exact values

\[
 f(9/10)=-1/125<0,\qquad
 f(901/1000)=32201/125000000>0
\]

imply

\[
 \frac9{10}<c<\frac{901}{1000}.
\]

Using \(s^2=1-c^2\), this in turn gives

\[
 \frac{433}{1000}<s<\frac{11}{25}.
\]

Indeed \(1-(901/1000)^2>(433/1000)^2\), while
\(1-(9/10)^2<(11/25)^2\). Substitution into (4) now yields

\[
 R>\frac9{10}+\frac{25}{22}
   =\frac{112}{55}>\frac{79}{40},
\]
\[
 R<\frac{901}{1000}+\frac{500}{433}
   =\frac{890133}{433000}<\frac{103}{50}.
\]

Finally,

\[
 R^2<\frac{10609}{2500}<\frac{17}{4}
   =\frac{1088}{256}<\frac{1105}{256}=Q.
 \tag{10}
\]

Thus the example lies strictly inside the interval to which the
existing cyclic necessary conditions apply.

## 6. An eighth square fits, with arbitrary orientation at the origin

The nearest support line of square \(j\) in its \(u_j\) direction has
coordinate

\[
 C_j\cdot u_j-\tfrac12
 =\rho\cos\psi-\tfrac12
 =\frac{c}{2s}-s^2.
 \tag{11}
\]

The rational bounds above give

\[
 \frac{c}{2s}-s^2
 >\frac{45}{44}-\frac{121}{625}
 =\frac{22801}{27500}>\frac45>\frac1{\sqrt2}.
\]

Every ring square therefore lies strictly outside the closed central
disk of radius \(4/5\), separated from that disk by its inner \(u_j\)
supporting line. Every unit square centered at zero lies in the disk of
radius \(1/\sqrt2\). Consequently any such square, at any orientation,
can be added without contacting any ring square.

Giving the central square zero circle and contact multipliers extends
the same normalized physical stress to this eight-square packing.

## 7. This exact ring admits at most one additional unit square

For this particular ring the completion problem is also elementary.
Every unit square contains the closed disk of radius \(1/2\) about its
center. Consequently centers of two squares with disjoint interiors
are at distance at least one. Also, the center \(X\) of any square
contained in the outer disk satisfies

\[
 |X|+\tfrac12\le R,\qquad |X|<\frac85.
 \tag{12}
\]

We claim that the seven open disks of radius one about the ring centers
\(C_j\) cover the annulus

\[
                  \tfrac12\le |X|<\tfrac85.
 \tag{13}
\]

First the rational bounds in Section 5 give \(k>1\), \(k<7/5\),
and \(0<d<1/4\). For the upper bound on \(k\), for example,

\[
 k<\frac{901\cdot1341}{866000}<\frac75.
\]

Thus

\[
 1<\rho,\qquad
 \rho^2=k^2+d^2
 <\frac{49}{25}+\frac1{16}
 =\frac{809}{400}
 <\left(\frac{57}{40}\right)^2.
 \tag{14}
\]

For any \(X\ne0\), one of the seven radial directions
\(e_{\theta_j}\) is within angle \(\delta\) of \(X\). Put \(r=|X|\).
Since \(c>9/10\),

\[
 |X-C_j|^2
 \le r^2+\rho^2-2r\rho c
 <F(r,\rho),\qquad
 F(r,\rho)=r^2+\rho^2-\frac95r\rho.
\]

The polynomial \(F\) is convex in each variable separately. Its maximum
on the rectangle

\[
 [1/2,8/5]\times[1,57/40]
\]

is therefore attained at one of the four corners. Its values there are

\[
 \frac7{20},\quad \frac{1597}{1600},\quad
 \frac{17}{25},\quad \frac{3893}{8000},
\]

all strictly below one. This proves the covering claim (13).

An added square center cannot be in that annulus, since it must be at
distance at least one from every ring center. By (12), it must therefore
satisfy \(|X|<1/2\). Two added square centers would then be at distance
strictly less than one from each other, again impossible.

Thus this exact ring has completion capacity one, and the eight-square
packing in Section 6 is maximal with the seven ring poses fixed. This
argument allows completely arbitrary positions and orientations for
the added squares; it is not restricted to an origin-centered completion.

## 8. Consequence for the proof strategy

The all-loaded cyclic case cannot be discharged by asserting that a
positive three-or-more-loaded component must already have radius at
least \(\sqrt Q\). The counterexample satisfies the physical common-point
requirement, force balance, torque balance, positivity, normalization,
the seven-loaded cap, distinct resultant directions, and the strict
acute condition at every loaded contact.

A valid nine-square argument must control the remaining physical squares
for the full family of admissible components. Section 7 settles that
completion for this one explicit ring. It does not establish a general
seven-loaded completion theorem, because the center covering used there
depends on the seven regularly spaced centers and their particular
radius.
