# Independent review of the complete low opposite-port exclusion

Date: October 26, 2026.

Reviewer: certificate_reduction.

**Verdict: PASS for the entire saved
SIX_CYCLE_ONE_RADIAL_LOW_OPPOSITE_PORT_EXCLUSION.md**, including
all A/M/O/T strict partner branches, the connected comparison curve,
the original low right-turn endpoint and every genuine T mean endpoint.

I reviewed the complete source, independently rederived all circle,
concurrence and derivative identities, and reconstructed the displayed
fixed rational reserves with Fraction. No sampled pose, numerical
root isolation or sign grid was used.

## 1. Original physical scope and the comparison curve

The actual low opposite S port belongs to exactly the two reflected
nonowner same-inner-side rows of the full low-turn cover. Its original
return is the adjacent vertex. The source retains the actual opposite
point, proper concurrence, strict opposite-vertex normal, all original
forces and means, and the full physical radial mask.

In the stated original own chart, the determinant
\[
 \det(P,G)=\frac{(1-t)(a-b)}{\sqrt{X^2+Y^2}}>0
\]
fixes the transverse sign in
\(a=1+wx+hy,\ b=1+wy-hx\).
I independently expanded these coordinates and obtained exactly
\[
 f=w(m+1)+hn-d=0,\qquad
 t=\frac n{h+n},\qquad
 \ell=\frac{hm-wn}{h+n}.
\]
The identities \(1-ta=\ell x,\ 1-tb=\ell y\) hold throughout
the entire constructed curve, not only at original poses.

On \(0\le n\le1,\ 0\le\gamma\le\pi/4\), the source proves
\(k,h>0\) and \(h-w>9/2000\). The three derivatives
\[
 f_n=h-wn/m>0,\quad
 f_\gamma=h(m+1)+kn>0,\quad
 f_d=-(m+1)\cos\gamma+n\sin\gamma-1<0
\]
have the stated signs, including the \(w<0\) branch.
The endpoint signs at gamma zero and \(\pi/4\) give one and only
one root for every \(n\in[0,1]\). The root is continuous on the
closed interval and differentiable inside with a strictly positive
implicit denominator.

The artificial comparison curve need not satisfy every unique-corner
inequality. The source proves the exact weaker conditions needed for
its calculus on the whole curve:
\(a>59/60,\ b\ge9/40>0,\ a>b,\ \ell>0,\ 0\le t<1\).
It does not claim a physical packing along that interpolation.
At the eta endpoints all displayed quantities and chosen angle branches
have finite continuous limits. This is a connected whole-domain
comparison, not a continuation across an unproved branch.

## 2. Independent derivation of both monotonicities

With \(m'=-n,n'=m\), differentiation of f gives
\[
 \gamma'=-\frac{hm-wn}{h(m+1)+kn}
         =-\frac{\ell}{1+\ell}.
\]
The second equality uses only \(k+w=1\). Hence
\((\gamma+\eta)'=1/(1+\ell)>0\).

I also directly differentiated the reconstructed circle coordinates:
\[
 (1+\ell)a'=1-b-\ell y=-(1-t)b,
\]
\[
 (1+\ell)b'=a-1+\ell x=(1-t)a.
\]
This verifies both signs and factors in the source's equation (18).
Differentiating \(t=n/(h+n)\) independently gives
\[
 t'=\frac{hm-nk\gamma'}{(h+n)^2}>0.
\]

For the nonowned adjacent return, the actual vector is
\(N=(ta-1,tb)=(-\ell x,tb)\). On the open eta interval it lies
strictly in the second quadrant, so its argument has the continuous
branch used in the proof. I independently obtained
\[
 \det(N,N')
 =\frac{t^2(1-t)R^2-t(1-t)a}{1+\ell}-t'b
\]
and therefore
\[
 (1+\ell)|N|^2(\theta-\gamma)'
 =-1+ta(1+t)-t^3R^2-(1+\ell)t'b.
\]
Putting \(u=ta<1\) and using \(R^2\ge a^2\) bounds this above by
\[
 -(1-u)(1-tu)-(1+\ell)t'b<0.
\]
Every denominator and remaining positive factor has already been
proved on the whole curve. Thus both \(\theta-\gamma\) and theta
decrease strictly.

At eta \(\pi/4\), the correct return-angle limit is \(3\pi/4\).
At eta \(\pi/2\), \(0<\ell<1\), so N is vertical positive and
theta is zero. The unique right-turn point and all three comparison
rows therefore follow. For a genuine T return the proof uses the
actual turn \(\pi-\eta\) and the separate increasing function
\(\gamma+\eta\); it never substitutes the nonowner O comparison
turn for that physical owned return.

## 3. Uniform endpoint bounds and exact signs

For \(\gamma_{\max}>23/50\), the decreasing d comparison and
the positive comparison w justify the multiplication by
\(1+\sqrt2<17/7\). The signed sine and cosine polynomials then give
the displayed negative value of f. Since \(f_\gamma>0\), this
bounds the actual continuous endpoint root in the required direction.

For \(\gamma_{\rm right}>33/100\), the source first proves that
every root with gamma at most \(33/100\) has \(n>9/25\).
The replacements of d, gamma and m all have the correct directions;
the comparison w is positive before m is enlarged.

I independently expanded the subsequent turn-sign numerator. With
\(m^2+n^2=2\), the replacements
\(d>187/200,\ h<81/100\) give exactly
\[
 2(m+1)E>P(n)+A(n)(m-1)
\]
with the two displayed polynomials. Before those replacements the
coefficient of d is \(2n>0\), and that of h is
\(-2\{n^2+x(m+1)\}<0\). Thus the lower-bound orientation is correct.

The monotonicity of A and P on \(9/25\le n\le1\), including the
strict lower bound on \(P'\), is valid on the complete interval.
Their endpoint values and \(0\le m-1<3/7\) give \(E>0\).
Since \(G\cdot N=y-\ell=E/(h+n)\), the actual comparison turn
is below a right angle. This completes the second endpoint bound
without an implicit numerical root.

Fresh exact arithmetic reproduced:

| Fixed comparison | Exact value |
| --- | --- |
| f endpoint at \(23/50\) | \(-31921699403869/15750000000000000\) |
| Strong d square reserve | \(64559/400000000\) |
| Enlarged m square reserve | \(16/15625\) |
| f test at \(n=9/25,\gamma=33/100\) | \(-404586506921509/200000000000000000\) |
| h upper polynomial | \(1293635307/1600000000\) |
| h reserve below \(81/100\) | \(2364693/1600000000\) |
| \(A(9/25)\) | \(-18/625\) |
| \(P(9/25)\) | \(873/62500\) |
| Complete E reserve | \(711/437500>0\) |
| Final angle-gap reserve | \(3/700>0\) |

I also reconstructed the endpoint existence reserves and the global
lower bound \(b\ge9/40\).

## 4. Exhaustive original strict-partner join

For the actual low endpoint,
\(\theta_L-\alpha<\pi/2-33/100\).
The actual adjacent A and genuine shared M partners both have
\(\beta>23/50\), using their separately reviewed local angle
theorems. The unique turn upper bound contradicts the low comparison
by the explicit gap \(79/100-\pi/4>3/700\).

An O partner lies on the same original-radius curve and uses its
actual nonowned adjacent return. Its upper comparison, added to
the low endpoint bound, contradicts the exact turn sum.

A T partner uses its actual return-owned angle \(\pi-\eta_T\).
The increasing \(\beta+\eta_T\) comparison contradicts the same
low endpoint bound and exact turn sum, including the original
\(t=0\) genuine endpoint mean.

These are all four strict partner types. The original low right-turn
case remains included through the weak first comparison row and
strict uniform gamma bound. No force, physical mask, owner label,
mean, slider or additional square was dropped.

The source therefore excludes the entire original low opposite-port
family. The remaining one-radial assembly still must join the full
feature cover with the separate low adjacent, single-mean, both-axis,
all-strict and weight-zero families. This review does not independently
tick that parent gate. No new computational packet, Lean compilation
or CI was used.

