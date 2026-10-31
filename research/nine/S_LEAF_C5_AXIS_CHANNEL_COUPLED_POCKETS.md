# In the actual S-leaf side-axis branch, central and B-V-C extras cannot coexist

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_UNIT_STAIR_AND_S_C5_COUPLED_C6_2026_10_26.md. It preserves every original
mean and slider. It does not close the whole S-leaf C5 load13 gate.

Keep exactly the original positive component
\[
                         A-B-V-C-U-A
\]
with a genuine S leaf L at A, block loads B,C, true degrees
\(\deg A=3,\ \deg B=\deg C=\deg U=\deg V=2\), and all three
additional physical unit squares. Keep the original positive forces,
actual contact normals and means, both individual physical radial
weights at C, all physical masks at B, and every transmitter slider.

Use the accepted tilted-root chart in
S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md and
S_LEAF_C5_TILTED_DIRECT_AND_CHANNEL_HALFPLANES.md:
\[
 \begin{gathered}
 d=\sqrt{R^2-\tfrac14}-1,\quad \delta=d-1,\quad
 0<\delta<1/60,\\
 A=(d,0)+[0,1]f_1+[0,1]f_2,\qquad
 f_1=(-a,-b),\ f_2=(-b,a),\\
 a^2+b^2=1,\quad a>59/61,\quad 0<b<16/61.
 \end{gathered}
\tag{1}
\]
The present whole feature branch is that the **original** A-to-C
channel normal is the root side axis
\[
                              n=f_1.
\tag{2}
\]
This is \(x=1,t=0\) in those sources. No new normal is selected.
Its entire original mean interval is
\[
 p_{AU}=(d,0)+f_1+Yf_2,\qquad 0\le Y<db.
\tag{3}
\]
Both endpoints, when actually permitted, are retained with their
unchanged contact labels.

**Theorem.** If any original extra unit lies in the actual exterior
B-V-C pocket, then the actual central C5 pocket is empty. Equivalently,
with the original physical allocation counts,
\[
                         n_{\rm central}\,n_{BC}=0.
\tag{4}
\]
This covers both physical B masks and all original U,V sliders.

## 1. Exact common frame, including the full root mean

Put \(f=f_2\). The accepted far-endpoint theorem gives
\[
 C=[d,d+1]n+[-1/2,1/2]f,\quad
 h_A(n)=\delta,\quad w_U=w_V=1.
\]
Since \(h_A(n)=1-da\), the original support equation is
\[
                             da=1-\delta.
\tag{5}
\]
Set
\[
                     T=db-Y>0,\qquad \ell=\frac12+T.
\tag{6}
\]
The actual applications are
\[
 p_{AU}=\delta n-Tf,\quad p_{CU}=dn-Tf,\quad
 p_{CV}=dn+\frac12f,
\]
\[
 g=-\alpha n+\beta f,\qquad
 \alpha,\beta>0,\quad \alpha^2+\beta^2=1,\qquad
 p_{BV}=p_{CV}+g.
\tag{7}
\]
The actual direct root application remains
\[
                   p_{AB}=(d,0)+Zf_1+f_2,\qquad 0\le Z\le1.
\tag{8}
\]
This includes a direct side-axis mean and its endpoints, as well as
the strict root-corner alternative.

Translate coordinates by the actual p_AU, without changing any
physical geometry. In these n,f coordinates the root square is
\[
                        A'=[-1,0]\times[-Y,1-Y].
\tag{9}
\]
The five actual contact vertices become
\[
 (0,0),\quad (1,0),\quad (1,\ell),\quad
 (1-\alpha,\ell+\beta),\quad (Z-1,1-Y).
\tag{10}
\]
Put \(L_0=1-Y\). The original radius and tilt bounds imply
\[
 db<\frac4{15},\qquad
 L_0-\ell=\frac12-db>\frac7{30}>0,\qquad
                          0<\ell<L_0\le1.
\tag{11}
\]
Thus every original mean in (3) satisfies the same strict height
ordering. No subinterval or selected mean is being substituted.

## 2. An occupied B-V-C pocket forces a steep cap normal

The complete physical pocket theorem
S_LEAF_C5_RADIAL_BC_POCKET_CAPACITY.md proves that every whole
extra in this actual pocket is contained in
\[
                  \{z:N\cdot z\ge H\},\qquad
 N=\beta n+\alpha f,\quad H=d\beta+\alpha/2.
\tag{12}
\]
It has already verified the genuine leaf's position and the
center/contact homotopy, so this is the original exterior pocket,
not an assumed center sector.

If any unit square is contained in \(D_R\cap\{N\cdot z\ge H\}\),
then \(H\le d\). Indeed, its center c has
\(|c|\ge N\cdot c\ge H+1/2\). For its actual orthonormal axes
u,v the farthest-corner formula gives
\[
 R^2\ge|c|^2+\frac12+|c\cdot u|+|c\cdot v|
      \ge|c|^2+\frac12+|c|
      \ge(H+1)^2+\frac14.
\tag{13}
\]
Here H is positive, so the squared comparison is monotone.
This proves the claimed \(H\le\sqrt{R^2-1/4}-1=d\).

Combining (12)--(13),
\[
 \beta\le1-\frac{\alpha}{2d}.
\]
The right side is positive. Squaring and using
\(\alpha^2+\beta^2=1,\ \alpha>0\) gives
\[
 \alpha\ge\frac{4d}{4d^2+1}
       >\frac{3660}{4621}>\frac34>\beta.
\tag{14}
\]
For the strict comparison, \(4d/(4d^2+1)\) decreases for
\(d>1/2\), and \(d<61/60\). Its value at \(61/60\) is
\(3660/4621\), whose excess above \(3/4\) is
\(777/18484>0\). Finally \(\alpha>3/4\) and unit length imply
\(\beta<\sqrt7/4<3/4\).

Thus an occupied BC pocket supplies the whole cap-normal condition
\(\alpha\ge\beta>0\) of UNIT_STAIR_POCKET_EXCLUSION.md.

## 3. Every whole central extra lies in the required stair pocket

The occupied center/contact C5 loop is homotopic, inside the
original closed cycle bodies, to its actual contact polygon (10).
The winding localization from CONTACT_RING_HOLE_AREA.md applies:
every point of a central extra's open interior is in the winding-one
region of that polygon, hence in its convex hull.
Closure puts the whole extra in every closed half-plane containing
the contact polygon.

In particular, (10) gives
\[
                         -1\le X\le1,\qquad Y_{\rm coord}\ge0.
\tag{15}
\]
The accepted S-leaf BC-pocket proof also places the entire free
central region on the inward side of the actual return line.
After the translation used in (9)--(10), this is exactly
\[
                 \beta X+\alpha Y_{\rm coord}
                           \le\beta+\alpha\ell.
\tag{16}
\]
Equivalently, its line passes through \((1,\ell)\) and
\((1-\alpha,\ell+\beta)\). Its derivation uses the original
positive connection coefficients and full genuine-leaf force;
no properness at a fictitious circle load on A is inserted here.

Every central extra is physically interior-disjoint from the
actual root (9). Equations (11), (14)--(16) now meet every
hypothesis of UNIT_STAIR_POCKET_EXCLUSION.md, with its L equal
to \(L_0=1-Y\). The theorem excludes that whole extra.
This proves (4).

The winding and closed-half-plane argument includes original
shared-side endpoints. Additional physical contacts with zero
selected force can subdivide the free regions but cannot enlarge
them or move an extra's open interior across the original closed
occupied cycle.

## 4. Exact consequence and remaining scope

This result is a coupled allocation restriction, not a new
six-body contradiction. It excludes every original allocation
having at least one central extra and at least one BC-pocket
extra in the complete actual side-axis branch (2).

If B is physically radial, the earlier BC theorem already makes
that pocket empty, so the new statement overlaps that accepted
case without producing an additional gate closure. If B is unique,
it removes the full central-plus-BC allocation at once, uniformly
over all original means, sliders, force ratios, and other extras.
The two leaf-side exterior pockets retain their existing obligations.

The strict root-corner A-to-C channel alternatives are not
silently converted to the side-axis branch. The unrestricted
S-leaf C5 load13 gate remains open. No finite sign certificate,
angle grid, Lean compilation, CI, or post-extraction normal
selection is a premise.
