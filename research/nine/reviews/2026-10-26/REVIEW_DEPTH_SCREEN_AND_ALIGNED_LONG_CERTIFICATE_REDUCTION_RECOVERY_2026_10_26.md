# Fresh independent review of the depth screen and aligned long-pocket replacement

Date: October 26, 2026.

Reviewer: certificate-reduction agent, independently from the C6 author.

**Verdict: PASS for the current complete texts**

- UNIT_TILTED_RADIAL_TERMINAL_DEPTH_SCREEN.md.
- S_LEAF_C5_ALIGNED_LONG_POCKET_DEPTH_SCREEN.md.

This is a new audit of the present replacement argument. It is not a
recreated historical review of the lost partial-translation source.

The reviewed source SHA256 values, before any later status-only header
change, are respectively:

- 12298f32eebf4f788f68da29083bb1011d50ae2ef9afba61ccab932582ac32be
- 75628330b662aace0634df3093751f8b1cc7178ca226a6d04077a83340381719

## 1. The complete all-orientation depth screen

I independently derived the actual inner vertices
\[
V_\pm=(D/c\mp s/2,\ \pm c/2)
\]
from the full linked terminal interval
\([D,D+1]n+[-1/2-Dv,1/2-Dv]f\). The cancellation of their
vertical coordinates depends on the actual shift Dv and is valid
throughout \(1\le D<c+s^2\).

For an interior intersection with the canonical terminal, I checked
both strict transverse strip bounds. The upper bound uses exactly
\[
(c-1)/2+v(D-c)
<(1-c)\{v(1+c)-1/2\}<0.
\]
The lower bound follows from
\(1/2+Dv-2s>1/2-v>0\).
The outer screen forces \(n\cdot p\le D\); this weak inequality is
enough because \(p_x>1,p_y>0\) make
\(p_x<D/c\) and \(p_y<(D-c)/s<s<c/4\).
The exact depth condition also gives \(V_{+x}<1\).
Thus all strict coordinate orders used in the separator proof hold,
including possible equality at \(n\cdot p=D\).

I checked every separator direction. A nonpositive n projection
contradicts the actual terminal point with the same transverse
coordinate or, for zero projection, a transverse endpoint.
The southwest, southeast and northwest possibilities are then
excluded by the actual vertices V+,V-. This leaves the terminal
radial normal n and the northeast side axes of the candidate unit.

For the n axis, I rederived the entire support formula and its two
branches. Their common lower bound is s², so the actual unit has
support strictly above \(c+s^2>D\).
For an arbitrary remaining E axis, the center estimate is exactly
\[
\max_E\omega\cdot z\ge M\cos\theta+\sin^2\theta,
\qquad M>1.
\]
The two terminal-vertex comparisons have their global minima at
\(\theta=\arctan v\). On the first branch the derivative in
\(\sin\theta\) is negative because \(s<c/4\); on the second,
the negative cosine coefficient and both nonnegative sine terms
make every term increase. Both endpoint values are
\(c+s^2-D>0\).

This is a complete separating-axis argument for whole squares,
including weak physical contacts and all orientations. No circle,
force, graph-degree or mean-selection premise has entered the
generic theorem.

## 2. Original aligned chart and physical routing

I rederived the retained equations
\[
P=(\delta,a),\quad
a^2=2\delta q-\delta^2,\quad
c=1-\delta/q,\quad s=a/q,
\]
including \(P+n=dn-af\). They retain the original reserve-one
channel, physical radial C and its genuine inner mean.

The theorem is conditional on the complete closed range
\(1/5\le q\le3/4\); it does not infer that range for an unreviewed
B feature. In that range \(a,r<1/6\), \(c>11/12\), and
\(0<v=\delta/a<1/4\) follow from the stated exact bounds.

I checked the entire occupied path. Its C part has n projection at
least d, the actual U segment interpolates from d to delta, and the
root chord remains at projection at most delta. The U part is west
of P and the root part east of P; the leaf portions are at x>=d.
These orders give the claimed noncrossing occupied crosscut.

The selected actual arc runs from gamma to pi-phi-gamma and is
the minor arc symmetric about j. The other terminal corners lie
outside that selected arc. Every actual vertical-direct B point
has negative y coordinate, whereas the selected arc has positive
y coordinate. Therefore the original long pocket is contained in
the stated bounded side, with any extra zero-force contacts only
subdividing it. The proof does not identify a center sector with a
whole-square pocket.

## 3. One translation, exact actual terminals and both whole ranges

I independently derived
\[
P=rj,\quad P_*=\lambda P,\quad
\lambda=\min(1,d/(2q)),\quad
D=d-\lambda\delta,\quad h=\lambda a.
\]
In particular \(2/3<\lambda\le1\), and both exact mean-vertex
heights in the source are nonnegative:
\[
j\cdot(P-P_*)=(1-\lambda)r,\qquad
j\cdot(p_0-P_*)=\delta(d-2q\lambda)/r.
\]
All other crosscut heights increase by the displayed positive
radial or transverse increments. The selected minor arc has
minimum j projection at an endpoint. Thus every whole translated
extra is in the same upper half-plane.

The translated terminal formulas follow from the exact projections
of P: both original radial projections equal delta and the inward
transverse shifts equal a. The strict outer-face screen applies at
the actual radius because its proof uses the exact center bound
\(d+1/2\) and the actual outer chord at d+1. The circle-vertex
unshareability argument is independent of the numerical radius.

For \(q\le d/2\), I checked \(D=1,h=a\le v\) and the whole-unit
upper-half-plane inclusion of the linked shift-v terminal in the
actual shift-h terminal. A point in the missing lower strip would
have \(y/c_0<2v-1/2-h<0\); this contradiction also handles the
actual lower-face equality. The generic depth screen therefore
applies without moving an extra.

For \(q\ge d/2\), I rederived
\[
D=d/(1+v^2),\qquad h=Dv,\qquad
v^2\ge2\delta/(3-2\delta).
\]
I expanded the crucial square identity independently, obtaining
\[
1+w_*-(1+\delta-w_*)^2
=\frac{\delta^2(11-4\delta-4\delta^2)}{(3-2\delta)^2}.
\]
Every factor has the asserted sign. Monotonicity in w then gives
the exact full-domain depth reserve \(D<c_0+s_0^2\).
Both arguments cover \(q=d/2\) with the original geometry unchanged.

## 4. Strict whole-region disk and repeated occupancy

I rederived the outer-endpoint norm
\((D+1)^2+(h-1/2)^2\).
For the first range its reserve below 17/4 is exactly \(a-a^2>0\).
For the second, the independent identity \(D^2+h^2=dD\) gives
\[
17/4-|z_L-P_*|^2
=h-(4-3\lambda)\delta-(1-\lambda)\delta^2.
\]
The displayed bound \(h^2>(13/20)\delta>36\delta^2\) is valid:
its first coefficient follows from \(2/3-1/60=13/20\),
and the second has uniform positive reserve at delta=1/60.
Thus h>6delta while the entire adverse part is below 3delta.

Because the translation is along the positive arc-bisector j,
the outer endpoints maximize translated norm on the entire selected
arc. Every other crosscut vertex is strictly within squared radius
17/4 by its explicit norm bound. The compact boundary and its
bounded side therefore lie in the same open convex disk.
This validates whole-square inclusion, not merely a vertex or
center test.

All hypothetical extras undergo the same rigid transformation.
The exact HALF_POCKET_TRIPLE_RIGIDITY.md conclusion applies to any
three, including repeated occupancy of this one region, and its
forced outer-circle vertices contradict the strict disk inclusion.

## 5. Scope and validation

The accepted conclusion is exactly \(n_{\rm long}\le2\) on the
stated original aligned q range. All nine physical squares, true
degrees, actual means, physical masks, radial weight endpoints and
transmitter sliders remain. The result is a new analytic replacement
for the missing partial-translation dependency; it does not close
the parent S gate or prove an unprovided q bound.

A fresh small Fraction/sparse-polynomial reconstruction independently
verified the cleared depth identity, complete endpoint-radius identity
and rational range comparisons. It is only an audit helper, not a
new proof packet or numerical premise. No sampled sign, new grid,
Lean compilation or CI was used. No correction to either current
source was needed.

