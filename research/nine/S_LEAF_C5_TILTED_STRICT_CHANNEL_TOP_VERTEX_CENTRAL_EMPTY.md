# The tilted strict-channel top-vertex family has no central extra

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_TOP_VERTEX_FEATURE_THREE_CUT_CENTRAL_C6_RECOVERY_2026_10_26.md.
This file does not reuse an earlier PASS for the lost manuscript.

Keep the original component A--B--V--C--U--A with genuine S leaf L,
the true degree-three root A, both original loaded degrees, every
positive force, actual normal, mean and transmitter slider, both
physical B masks and every individual radial weight, and all nine
physical unit squares. The present feature is the original
root-side normal m=f2 and strict channel t>0, with the actual direct
normal strict at B. No restriction on its original direct mean Z
is imposed.

Use the complete unchanged normal form in
S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md,
S_LEAF_C5_TILTED_DIRECT_AND_CHANNEL_HALFPLANES.md and the full
all-mean feature reduction
S_LEAF_C5_TILTED_STRICT_CHANNEL_TOP_VERTEX_FEATURE_REDUCTION.md.

## 1. Actual chart and the linked bounds

In the reflected root frame, write
\[
\begin{gathered}
d=1+\delta,\quad 0<\delta<1/60,\quad D=da,\quad h=db,\quad H=1-h,\\
A=[D-1,D]\times[-H,h],\quad
F=p_{AB}=(q,-H),\quad q=D-Z,\\
n=(-x,t),\quad f=(-t,-x),\quad x,t>0,\quad x^2+t^2=1,\\
p_{AU}=(D-1,h),\quad p_{CU}=p_{AU}+n=dn-Tf,\quad
Q=p_{CV}=dn+f/2,\\
G=p_{BV}=Q+g=F+w,\quad
g=(u,-v),\quad e=(k,-l),\quad w=(-l,-k).
\end{gathered}
\tag{1}
\]
The full feature theorem gives
\[
\begin{gathered}
u,v,k,l>0,\quad u^2+v^2=k^2+l^2=1,\quad ul>vk,\\
g=-\alpha n+\beta f,\quad \alpha,\beta>0,\quad
q>1/2,\quad x>19/20,\quad t<3/10,\\
H>37/50,\quad D<61/60,\quad 0<T<13/50,\quad 0<Z<1.
\end{gathered}
\tag{2}
\]
The physical B mask is either its unique actual corner \(F+e\),
or its actual radial right face with both corners \(F+e,F+e+w\).
In both masks the comparison with the second actual corner gives
\[
ql-Hk\ge1/2.
\tag{3}
\]
The first case has a strict comparison; the radial case needs only
the weak one. No individual radial weight has been omitted.

Put
\[
\lambda=1-Z=q-D+1,\qquad \ell=T+1/2,\qquad \eta=l-\lambda.
\]
Then \(0<\lambda<1\), \(0<\ell<19/25\). Since \(l<1\),
(2)--(3) give
\[
\lambda>\frac{29}{60}+\frac{37}{50}k.
\tag{4}
\]

## 2. The actual contact polygon and its three cuts

Apply the rigid coordinate change
\[
X=D-1-x_{\rm old},\qquad Y=y_{\rm old}+H.
\]
The actual root becomes \([-1,0]\times[0,1]\). Its five actual
contact vertices, in their unchanged cycle order, are
\[
(0,1),\quad (x,1+t),\quad
(x+\ell t,1+t-\ell x),\quad(\eta,-k),\quad(-\lambda,0).
\tag{5}
\]
The two actual unit channels and the unchanged return side yield
exactly
\[
u=x+\ell t-\eta,\qquad
v=1+t-\ell x+k,\qquad
\alpha=xu+tv,\qquad\beta=xv-tu>0.
\tag{6}
\]
The channel reserve remains one; (6) is not an independently
relaxed selection of contact vertices.

The actual occupied center/contact cycle is homotopic inside its
original closed bodies to the polygon (5), using each actual
interface mean. The winding localization of
CONTACT_RING_HOLE_AREA.md puts every point of the open interior
of a central extra in its bounded winding region and therefore in
its convex hull. Closure places the whole extra in every closed
half-plane containing (5).

In particular the five vertices lie in
\[
X\ge-\lambda,\qquad -k\le Y\le1+t.
\tag{7}
\]
For the horizontal bound at G, use \(\eta=l-\lambda>-\lambda\).
All other coordinate bounds follow immediately from (5) and
\(1+t-\ell x>6/25+t>0\).

There are three further containing half-planes:
\[
\begin{split}
-tX+x(Y-1)&\le0,\\
xX+tY&\le1+t,\\
vX-uY&\le v\eta+uk.
\end{split}
\tag{8}
\]
For completeness each sign can be checked on the actual polygon.
The first is equality on the first channel. Its value drops by
\(\ell\) at Q and by \(\beta\) on Q to G. At F its value is
\(t\lambda-x<0\).
The second is equality at the second and third vertices; its value
drops by \(\alpha\) at G, while the first and fifth vertices also
satisfy it strictly.
The last is equality at Q and G. Moving from Q to the second
vertex drops its value by \(\ell\alpha\); moving onward to the
first vertex drops it by \(\beta\). At F its value is below the
bound by \(vl+uk>0\).
These are actual supporting cuts and do not depend on a selected
extra orientation.

## 3. Whole central-pocket exclusion

Every hypothesized whole central extra is interior-disjoint from
the original root. Equations (2), (4), and (6)--(8) meet every
hypothesis of UNIT_CORNER_ADJACENT_VERTEX_THREE_CUT_EXCLUSION.md.
That theorem excludes it. Hence
\[
n_{\rm central}=0
\]
throughout the entire original strict-channel top-vertex family,
for all its actual direct means and both physical right-circle
masks.

All original positive connection coefficients, force equations,
radial corner weights and U,V sliders remain. Extra contacts with
zero selected force can subdivide the free regions but cannot
enlarge the bounded winding region or cross its occupied cycle.
The statement excludes a whole central unit; it does not presume
one extra per pocket and makes no claim about either exterior
pocket or the final S-leaf gate.
