# A two-variable pair bound reduced to circular support functions

This is an exact analytic reduction. It does not assert the existence of the
affine labels or one-variable envelopes needed to close the pair theorem.
The accompanying fitting experiments are discovery only.

## Coordinates and labels

Write the source centre in its own frame as \((a,-\sigma b)\), and the
target centre in its own frame as \((A,-\tau B)\), where
\(a,A>0\), \(0\leq b\leq a\), \(0\leq B\leq A\), and
\(\sigma,\tau\in\{-1,1\}\). Let

\[
\alpha=\sigma\arctan(b/a),\quad
\alpha'=\tau\arctan(B/A),\quad
\phi=\delta+\alpha'-\alpha.
\]

For each state type choose an affine label

\[
\ell_i(a,b)=c_i+p_i a+q_i b,
\qquad
\psi_i=\alpha-\sigma\ell_i(a,b).
\tag{1}
\]

The signed representatives at a type cut are chosen consistently at each
vertex of the ring. No continuity of different type labels at a cut is
required for telescoping.

Let

\[
h(\phi)=\frac{|\cos\phi|+|\sin\phi|-1}{2},\qquad W=1+h.
\]

The corrected pair cost is exactly

\[
C=\delta-\beta h+\psi_j-\psi_i
=\phi-\beta h+\sigma\ell_i(a,b)-\tau\ell_j(A,B).
\tag{2}
\]

In particular, the arctangents have disappeared from the cost. Only the
true relative frame angle \(\phi\) remains.

## The two source-axis formulas

The two forward source-axis separating margins are

\[
M_f=A\sin\phi-\tau B\cos\phi+\sigma b-W,
\]

\[
M_e=a-A\cos\phi-\tau B\sin\phi-W.
\tag{3}
\]

They correspond, respectively, to source \(+f\) and source \(-e\).
The other two forward target axes reduce to these by reversing the pair
and reflecting the plane: this sends
\((i,\sigma;j,\tau)\) to \((j,-\tau;i,-\sigma)\), preserves
\(\delta\) and the corrected cost for odd potentials, and sends target
\(+f\) to source \(+f\), target \(+e\) to source \(-e\).

Suppose one of the margins in (3) is nonnegative. For any \(\lambda\geq0\),
subtracting \(\lambda M\) from (2) gives a lower bound for \(C\) that
separates into an affine function of each square's own coordinates.

For a type domain \(D_i\), write its lower support function as

\[
L_i(x,y)=\min_{(a,b)\in D_i}(xa+yb).
\]

Then source \(+f\) separation implies

\[
\begin{split}
C\geq {}&\phi-\beta h+\lambda W+\sigma c_i-\tau c_j\\
&+L_i\bigl(\sigma p_i,\ \sigma(q_i-\lambda)\bigr)\\
&+L_j\bigl(-\tau p_j-\lambda\sin\phi,
\ \tau(\lambda\cos\phi-q_j)\bigr),
\end{split}
\tag{4}
\]

and source \(-e\) separation implies

\[
\begin{split}
C\geq {}&\phi-\beta h+\lambda W+\sigma c_i-\tau c_j\\
&+L_i\bigl(\sigma p_i-\lambda,\ \sigma q_i\bigr)\\
&+L_j\bigl(-\tau p_j+\lambda\cos\phi,
\ \tau(\lambda\sin\phi-q_j)\bigr).
\end{split}
\tag{5}
\]

These inequalities hold for every nonnegative multiplier, including a
multiplier chosen as an explicit function of \(\phi\). Thus proving
that the right sides exceed the required \(\Gamma_{ij}\) reduces the
pair theorem to one real variable. No minimization over the two square
angles remains.

## Exact outer support functions

On the outer boundary,

\[
(a+1/2)^2+(b+1/2)^2=Q.
\]

Writing \((a+1/2,b+1/2)=\sqrt Q(\cos v,\sin v)\), a type interval
in \(b/a\) is a closed interval \(v\in[v_0,v_1]\subset(0,\pi/4]\).
Its endpoints \((a_k,b_k)\) are obtained by the quadratic disk equation
at the rational tangent cuts. Hence

\[
L_i(x,y)=-\frac{x+y}{2}
+\sqrt Q\min_{v_0\leq v\leq v_1}(x\cos v+y\sin v).
\tag{6}
\]

There are only three possible formulas for the last minimum:

* the left endpoint \(x\cos v_0+y\sin v_0\);
* the right endpoint \(x\cos v_1+y\sin v_1\);
* \(-\sqrt{x^2+y^2}\), when \((x,y)\) points opposite to a ray whose
  angle lies in \([v_0,v_1]\).

The interior case requires \(x,y<0\), with the ratio \(y/x\) lying
between the endpoint slopes. Otherwise only the two endpoints occur.
This follows immediately by differentiating the single sinusoid in (6).
It is an exact finite formula, not an interval bound.

## Exact core support functions

The core side branch is

\[
a=\frac7{12},\qquad 0\leq b\leq\frac12.
\]

An affine function attains its minimum on any closed part of this segment
at an endpoint. The core corner branch is

\[
(a-1/2)^2+(b-1/2)^2=\frac1{144},\qquad a\geq b\geq\frac12.
\]

Writing \((a-1/2,b-1/2)=(\cos v,\sin v)/12\), one obtains, on any
closed corner subarc,

\[
L_i(x,y)=\frac{x+y}{2}
+\frac1{12}\min_{v_0\leq v\leq v_1}(x\cos v+y\sin v).
\tag{7}
\]

Again there are only the two endpoint formulas and the possible interior
formula \(-\sqrt{x^2+y^2}\). For a core type spanning both branches,
take the smaller of its side and corner minima.

## What this does and does not prove

Equations (4)--(7) are a hand reduction for any specified affine labels,
type intervals and nonnegative multiplier functions. They account for
interior stationary points of the support minimization explicitly.
They do not assume that all contacts occur at type endpoints.

To finish a certificate by this route, one must still provide the affine
label constants and multiplier choices, split the relative-frame angle
into its finitely many sign/support regimes, and prove the resulting
one-variable inequalities. Numerical positivity of a fitted label family
does not replace that final step.
