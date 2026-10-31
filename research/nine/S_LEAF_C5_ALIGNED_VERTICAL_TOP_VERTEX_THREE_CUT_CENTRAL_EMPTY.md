# The complete aligned vertical top-vertex central region is empty

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_ALIGNED_VERTICAL_FEATURE_AND_CENTRAL_CERTIFICATE_REDUCTION_RECOVERY_2026_10_26.md. The lost area-envelope and degree-eight polynomial manuscript is
not a dependency. This proof uses the current whole-unit three-cut theorem.

Keep the entire original aligned vertical S-leaf C5 family and every physical
square, force, actual normal, mean, corner weight and transmitter slider.
Apply S_LEAF_C5_ALIGNED_VERTICAL_FULL_FEATURE_AND_Q_BOUND.md to the actual
strict-top-vertex rows of B, including both its physical right-circle masks.
It gives, in its unchanged notation,
\[
\begin{gathered}
0<\delta<1/60,\quad d=1+\delta,\quad
A=[\delta,d]\times[-b,a],\quad a+b=1,\\
0<a<11/60,\quad b>49/60,\quad
\frac12<q<\frac34,\quad a=qs,\quad\delta=q(1-c),\\
n=(-c,s),\quad f=(-s,-c),\quad c>29/30,\quad0<s<3/10,\\
F=(q,-b),\quad e=(k,-l),\quad w=(-l,-k),\quad
k,l>0,\quad k^2+l^2=1,\\
ql-bk\ge1/2,\quad
Q=dn+f/2,\quad G=F+w=Q+g,\\
g=(u,-v)=-\alpha n+\beta f,\quad
u,v,\alpha,\beta>0,\quad u^2+v^2=1,\quad ul>vk.
\end{gathered}
\tag{1}
\]
The weak comparison in the physical radial B row is sufficient.

Use the one rigid coordinate change
\[
X=\delta-x_{\rm old},\qquad Y=y_{\rm old}+b,
\]
which sends the actual root to \([-1,0]\times[0,1]\).
Set
\[
\lambda=q-\delta,\qquad \ell=a+1/2,\qquad\eta=l-\lambda.
\]
Then
\[
0<\lambda<1,\quad0<\ell<41/60<19/25,\qquad
\lambda>\frac{29}{60}+\frac{37}{50}k.
\tag{2}
\]
Indeed \(l<1\) and \(ql-bk\ge1/2\) give \(q>1/2+bk\).

The five actual contact points in cycle order are exactly
\[
(0,1),\quad(c,1+s),\quad
(c+\ell s,1+s-\ell c),\quad(\eta,-k),\quad(-\lambda,0).
\tag{3}
\]
For the third point use the original equality \(P+n=dn-af\);
the move from this true U--C mean to Q adds \((a+1/2)f\).
The actual channel gives
\[
u=c+\ell s-\eta,\qquad
v=1+s-\ell c+k,\qquad
\alpha=cu+sv,\quad\beta=cv-su>0.
\tag{4}
\]

The occupied contact-ring homotopy in CONTACT_RING_HOLE_AREA.md places
every whole central extra in the convex hull of (3). Its vertices lie in
\[
X\ge-\lambda,\quad-k\le Y\le1+s,
\]
and in the three actual supporting half-planes
\[
-sX+c(Y-1)\le0,\qquad cX+sY\le1+s,\qquad
vX-uY\le v\eta+uk.
\tag{5}
\]
Each sign follows directly by traversing the original contacts:
the first is equality on the U segment and then decreases by
\(\ell,\beta\); the second is equality on the C side and decreases
by \(\alpha\) on the return channel; the third is equality on that
channel and decreases by \(\ell\alpha,\beta\) on the preceding two
steps. The direct F also satisfies every bound. Thus no cut is
chosen according to the orientation of a tested extra.

Equations (1)--(5) are exactly the full hypotheses of
UNIT_CORNER_ADJACENT_VERTEX_THREE_CUT_EXCLUSION.md with
\(x=c,t=s\). That theorem excludes a whole unit of any orientation
disjoint from the actual root inside these cuts. Therefore
\[
\boxed{n_{\rm central}=0}
\]
throughout both original aligned vertical top-vertex rows.

The proof keeps the true contact polygon, both physical B masks and all
radial weight endpoints. Extra physical contacts can only subdivide its
bounded winding side. It does not assert exterior emptiness or a parent
closure. The sole q restriction used above was proved for each entire
original feature in the current full cover, not imposed on a numerical
configuration. No area coefficient packet is needed.

