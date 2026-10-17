# The explicit support formula for the nonaligned high/low regime

The geometric reduction in this note is proved exactly. A separate scalar
curvature/point-value argument is still needed to establish its proposed
lower bound on the stated interval.

Use \(Q,\mu,q,k,v,c,a_0\) and the low/high labels from
`LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md`. Write

\[
 R=\sqrt Q,\qquad \beta=9/50,\qquad
 c_L=-\mu a_0,\qquad c_H=\pi/4+(k-v)c.
\]

Consider a positive-sign high source \((a,-b)\), a positive-sign low
target \((A,-B)\), and the source \(+f\) separating axis. The
separation margin and cost are

\[
 M=A\sin\phi-B\cos\phi+b-1-h\ge0,
\]

\[
 C=\phi-\beta h+\ell_H(a,b)-\ell_L(A,B).
\]

For every \(\lambda\ge0\), subtract \(\lambda M\). Enlarge both
outer arcs to their full circles, whose centres are \((-1/2,-1/2)\)
and radii \(R\). The elementary circle support identity

\[
 \min_{(x+1/2)^2+(y+1/2)^2=Q}(p x+q y)
 =-\frac{p+q}{2}-R\sqrt{p^2+q^2}
\]

then gives the following lower bound for \(0\le\phi\le\pi/2\):

\[
\begin{split}
 C\ge F(\phi):={}&
 \phi-\frac\beta2\cos\phi
       +\left(\lambda-\frac\beta2\right)\sin\phi
       +\lambda+c_H-c_L+\frac{k-v+\mu+q+\beta}{2}\\
 &-R\left[
 \sqrt{k^2+(\lambda-v)^2}
 +\sqrt{\mu^2+q^2+\lambda^2
                +2\mu\lambda\sin\phi-2q\lambda\cos\phi}
 \right].
\end{split}
\tag{1}
\]

Here \(h=(\cos\phi+\sin\phi-1)/2\), and \(\lambda\) may be any
nonnegative function of \(\phi\). To check the algebra before combining
terms, the two support coefficient pairs are

\[
 (-k,v-\lambda),\qquad
 (-\mu-\lambda\sin\phi,\lambda\cos\phi-q).
\]

This bound uses no assumption that either stationary support point lies
on its type arc: enlarging to the entire circles is conservative.

For the central nonaligned interval, use the explicit affine multiplier

\[
 \lambda(\phi)=\frac{495453}{500000}-\frac7{25}\phi,
 \qquad \frac2{25}\le\phi\le\frac3{10}.
\tag{2}
\]

It is positive throughout the interval. The proposed scalar target is
\(F(\phi)>8833/10000\). A suitable proof route is a uniform
\(F''\ge1/20\) bound, together with the value and derivative at the
rational point \(\phi_0=17/100\), followed by

\[
 F(\phi)\ge F(\phi_0)
 -\frac{F'(\phi_0)^2}{2(1/20)}.
\]

The suggested curvature and point bounds are proof obligations here;
the numerical experiment that selected (2) is not used to discharge
them. A constant multiplier does not provide the same curvature, so
the derivative of the affine multiplier must be included throughout.
