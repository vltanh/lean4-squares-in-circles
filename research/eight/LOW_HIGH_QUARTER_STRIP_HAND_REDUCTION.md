# The low/high quarter-aligned strip reduces by hand to exact alignment

This lemma treats the source `+f` separating axis, positive source and
target signs, and a true relative frame angle within `1/50` of `π/2`.
It is one continuous pair regime of the affine-marker proof. It does not
assert the remaining pair regimes or the global frame-concentration theorem.

Put

\[
Q=9789/2500,\qquad b_*=9/50,\qquad
c=\sqrt{Q/2}-1/2,\qquad a_0=\sqrt{Q-1/4}-1/2.
\]

For a low outer state write its center as \((a,-b)\), where

\[
a=\sqrt{Q-(b+1/2)^2}-1/2,\qquad 0\le b/a\le1/4.
\]

For a high outer state write its center as \((V,-U)\), where

\[
U=\sqrt{Q-(V+1/2)^2}-1/2,\qquad 3/7\le U/V\le1.
\]

Thus \(V\ge c\ge U\). Let \(\phi=\pi/2+e\), \(|e|\le1/50\), and define

\[
h(e)=(\cos e+|\sin e|-1)/2,
\]

\[
\ell_L=.403875(a-a_0)+1.089065b,
\]

\[
\ell_H=\pi/4-.569472(V-c)+.390886(U-c),
\qquad \ell_T=\pi/2-\ell_H.
\]

Every terminating decimal in this note denotes an exact rational number.
The separating-axis hypothesis and corrected pair cost are

\[
b+U\sin e+V\cos e\ge1+h(e),                    \tag{1}
\]

\[
C=e-b_*h(e)+\ell_L+\ell_T.                    \tag{2}
\]

**Lemma.** Every feasible point of (1) can be continuously deformed,
within these two type domains and while preserving (1), to a point with
\(e=0\) and equality in (1), with cost (2) nonincreasing. The cost
strictly decreases if (1) initially has slack or if \(e\ne0\). Therefore
any hand lower bound for the exactly quarter-aligned contact cost applies
to this entire strip. In particular, the separate aligned-endpoint lemma
giving cost \(>.8833\) gives that same bound throughout this strip.

## 1. Elementary bounds and reduction to contact

Squaring \(1.399\) and \(1.4\) gives

\[
.899<c<.9.
\]

Taylor's inequality and \(|\sin e|\le|e|\) give

\[
\cos e>.9998,\qquad |\sin e|\le.02,
\qquad 0\le h(e)\le.01.                       \tag{3}
\]

Here \(h\ge0\) follows from \(\cos x+\sin x\ge1\) for
\(0\le x\le\pi/4\). On either open half-strip,

\[
\begin{array}{c|c}
e<0& .4899<-h'(e)\le1/2\\
e>0& .4899<h'(e)\le1/2.
\end{array}                                    \tag{4}
\]

Both marker summands increase with their respective coordinates:

\[
\ell_L'=1.089065-.403875\frac{b+1/2}{a+1/2}>0,
\]

\[
\ell_T'=.569472+.390886r>0,
\qquad r=\frac{V+1/2}{U+1/2},\qquad 1\le r\le7/3.
\]

The left side of (1) increases with \(b\) and with \(V\), since

\[
D:=\cos e-r\sin e>.9998-(7/3)(.02)>0.
\]

Starting from a feasible point with slack, decrease \(b\) until first
contact or \(b=0\), and in the latter case decrease \(V\) until first
contact. Decreasing \(b\) preserves the low type; decreasing \(V\)
toward \(c\) preserves the high type. Contact must be reached, because
the lower corner \(b=0,V=U=c\) is infeasible:

\[
c(\sin e+\cos e)<.9(1.02)=.918<1\le1+h(e).
\]

During every nontrivial part of this reduction, the cost strictly decreases.
It remains to analyze the contact surface.

## 2. Uniform bounds on the entire contact surface

At contact, (3) and \(U\le c\le V\) imply

\[
b=1+h-U\sin e-V\cos e
<1.01+.9(.02)-.899(.9998)=.1291798<.13.         \tag{5}
\]

Also \(b\ge0\) gives

\[
V<\frac{1.028}{.9998}=\frac{5140}{4999}<1.03.
\]

The disk equation therefore gives

\[
(U+1/2)^2>Q-1.53^2=1.5747>1.25^2,
\]

and hence

\[
U>.75,\qquad 1\le r<\frac{153}{125}=1.224.    \tag{6}
\]

Similarly \((a+1/2)^2>Q-.63^2>(15/8)^2\), so

\[
a>11/8,\qquad b/a<.13/(11/8)<1/4,
\qquad U/V>75/103>3/7.                        \tag{7}
\]

Thus no upper type boundary can be encountered anywhere on this contact
surface. Its only possible lower-coordinate boundaries are \(b=0\)
and \(V=c\).

## 3. Moving the frame angle while holding the low state fixed

Hold \(b\) fixed, and use equality in (1) to continue \(V\) as a function
of \(e\). The positive denominator \(D\) just proved makes this a regular
implicit function. Differentiating gives

\[
\frac{dV}{de}=-\frac{N}{D},\qquad
N=U\cos e-V\sin e-h'(e).                      \tag{8}
\]

In both half-strips \(N>0\). For example, in the positive half-strip,

\[
N>.75(.9998)-1.03(.02)-.5=.22925>0;
\]

the negative half-strip has an even larger lower bound. Thus \(V\)
strictly decreases as \(e\) increases. Along this contact curve,

\[
\frac{dC}{de}=1-b_*h'(e)-\ell_T'\frac ND.      \tag{9}
\]

### Negative frame error

For \(-1/50\le e<0\), equations (3)--(6) give

\[
N>\frac{4959}{4000},\qquad
D<\frac{6403}{6250},\qquad
\ell_T'\ge .960358=\frac{480179}{500000}.
\]

For the first inequality one may discard the nonnegative term
\(-V\sin e\), and use \(.75(.9998)+.4899=4959/4000\).
The exact multiplication and division yield

\[
\ell_T'\frac ND>
\frac{125326719}{107840000}>\frac{29}{25}.
\]

The last strict reserve is \(232319/107840000\). Consequently (9) gives

\[
\frac{dC}{de}<1.09-1.16=-.07.                 \tag{10}
\]

Increasing \(e\) toward zero therefore decreases both \(V\) and the
cost, until reaching \(e=0\) or the boundary \(V=c\).

### Positive frame error

For \(0<e\le1/50\), equations (3)--(6) instead give

\[
N<\frac{4101}{10000},\qquad
D>\frac{24383}{25000},\qquad
\ell_T'<\frac{21}{20}.
\]

Indeed \(N<.9-.4899\), and the last inequality follows from

\[
.569472+.390886\frac{153}{125}
=\frac{65494779}{62500000}<\frac{21}{20}.
\]

Thus

\[
\ell_T'\frac ND<\frac{86121}{195064}<\frac{23}{50},
\]

and (9) yields

\[
\frac{dC}{de}>.91-.46=.45.                    \tag{11}
\]

Decreasing \(e\) toward zero decreases the cost. Along this motion
\(V\) increases, so the lower boundary \(V=c\) cannot obstruct it.
The uniform strict bounds (5)--(7) exclude every other type boundary;
the denominator remains uniformly positive. Therefore the implicit
contact curve continues all the way to \(e=0\).

## 4. Continuing along the high diagonal boundary

It remains to continue the negative-half-strip path if it reaches
\(V=c\) before \(e=0\). Fix \(U=V=c\), and set

\[
b(e)=1+h(e)-c(\sin e+\cos e).                 \tag{12}
\]

This preserves exact contact. For \(e<0\),

\[
b=\frac12+(\tfrac12-c)\cos e
       -(\tfrac12+c)\sin e\ge1-c>0,
\]

while (5) gives \(b<.13\). Hence this path stays in the strict low
type. Moreover

\[
b'=h'-c(\cos e-\sin e)<0.
\]

Using \((b+1/2)/(a+1/2)<.63/(15/8)=42/125\) gives

\[
\ell_L'>1.089065-.403875(42/125)
=.953363>19/20.
\]

Since \(\cos e-\sin e\ge1\), \(c>.89\), and \(-h'>.4899\),

\[
c(\cos e-\sin e)-h'>1.3799.
\]

The derivative of (2) along (12) therefore satisfies

\[
\frac{dC}{de}
=1-b_*h'-\ell_L'\{c(\cos e-\sin e)-h'\}
<1.09-\frac{19}{20}(1.3799)<0,
\]

because \((19/20)(1.3799)=262181/200000=1.310905\).
This last path reaches \(e=0\), \(V=c\), \(b=1-c\), again with
strictly decreasing cost. Together with the preceding cases this proves
the lemma.
