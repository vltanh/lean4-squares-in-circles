# The upward three-square cap from the matched orientation reserve

November 1, 2026 (America/Chicago; November 2 UTC). Reconstructed complete
hand derivation of the explicitly conditional transfer theorem. No scripts,
Lean, or CI. Any geometric caller must establish every premise below.

This is a short alternative proof of the upward separating-normal case.
It retains the orientation reserve in the ordinary matched vertical cap.

## 1. Statement

Put

\[
 Q=\frac{1105}{256},\quad r=\frac{\sqrt{1105}}{16},\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},
 \quad T=\frac{211}{4},\quad \mu=\frac{k}{b}=\frac{23}{24}.
\]

Let M,A,B be physical unit squares contained in the centered disk of
radius \(R\le r\). Suppose

\[
 y_A-y_M\ge h_A+h_M,\qquad y_A-h_A\ge\frac38.
 \tag{1}
\]

Suppose A,B have a physical separating normal pointing right and upward:

\[
 n=(p,s),\quad p>0,\ s>0,\quad p^2+s^2=1,
\]
\[
 p(x_B-x_A)+s(y_B-y_A)\ge H_A(n)+H_B(n). \tag{2}
\]

**Theorem.** These hypotheses imply the strict transfer cap

\[
 \boxed{a(-x_M-h_M)+b(1-x_B-h_B)<T.} \tag{3}
\]

In a packing containing an actual horizontal four-chain with left
endpoint M, its transverse budget \(|y_M|\le1/8\) gives the second
inequality in (1) automatically from the first, because \(h_M\ge1/2\).

## 2. The exact reserve in the matched vertical cap

Apply circle supports in directions \((-a,-k)\) to M and
\((-b,k)\) to A, and use the actual vertical separation in (1).
The same algebra as in the physical two-square cap gives

\[
 a(-x_M-h_M)+b(-x_A-h_A)
 \le T-\Delta_M-\Delta_A, \tag{4}
\]

where

\[
 \Delta_M=(a+k)h_M+H_M((-a,-k))-(a+k)\ge0,
\]
\[
 \Delta_A=(b+k)h_A+H_A((-b,k))-(b+k)\ge0.
\]

The nonnegativity follows from
\((u+v)h+H((\pm u,\pm v))\ge u+v\) for \(u,v\ge0\).
The constant in (4) is exact because

\[
 \sqrt{a^2+k^2}=23r,\quad
 \sqrt{b^2+k^2}=9r,
\]
\[
 r(23r+9r)-(a+b+2k)=T.
\]

Write \(D=\Delta_A/b\). We next quantify this reserve without
assuming A's orientation sign.

## 3. A uniform orientation reserve

Let \(\alpha\ge\beta\ge0\) be the absolute physical side-axis
components of A, with \(\alpha^2+\beta^2=1\). Put

\[
 h=\frac{\alpha+\beta}{2},\qquad
 j=\frac{\alpha-\beta}{2},\qquad c=\frac1{\sqrt2}.
\]

The four vertex offsets have absolute coordinate magnitudes h,j.
For the direction \((-1,\mu)\), with \(1\ge\mu\), an outward
vertex gives

\[
 H_A((-1,\mu))\ge j+\mu h.
\]

Consequently

\[
 D\ge(1+\mu)(\alpha-1)+\mu\beta=:D_0. \tag{5}
\]

We claim

\[
 \boxed{D\ge\frac\beta\alpha(c-\beta),} \tag{6}
\]

strictly when \(\beta>0\). At \(\beta=0\), A is aligned and
both sides of (6) are zero.

For \(\beta>0\), using \(1-\alpha=\beta^2/(1+\alpha)\),

\[
 D_0-\frac\beta\alpha(c-\beta)
 =\frac\beta\alpha
  \left(\mu\alpha-c+
        \frac{\beta(1-\mu\alpha)}{1+\alpha}\right). \tag{7}
\]

If \(\alpha\ge3/4\), then
\(\mu\alpha\ge23/32>1/\sqrt2=c\), so the bracket is positive.
If \(\alpha\le3/4\), then \(\beta>1/2\), and

\[
 \frac{\beta(1-\mu\alpha)}{1+\alpha}
 >\frac12\frac{9/32}{7/4}=\frac9{112},
\]
\[
 \mu\alpha-c\ge-(1-\mu)c>-\frac1{24}.
\]

The bracket exceeds \(9/112-1/24=13/336>0\). This proves (6).

## 4. The reserve pays for every upward oblique separation

Set

\[
 \kappa=r-\frac{11}{8}<\frac{45}{64}<\frac1{\sqrt2}=c.
 \tag{8}
\]

Here \(r<133/64\), while \(45/64<1/\sqrt2\) follows by
squaring \(2025<2048\).

For every \(\tau>0\), we prove

\[
 \Psi(\tau):=
 H_A((1,\tau))-h+\tau(h-\kappa)+D>0. \tag{9}
\]

First suppose \(\beta>0\). For \(0\le\tau\le1\), the two
possible orientation signs of A give the uniform support lower bound

\[
 H_A((1,\tau))\ge\max(h-j\tau,j+h\tau).
\]

The first term comes from the vertex with positive x-offset h and
y-offset of magnitude j. The second is the smaller outward-quadrant
support when \(\tau\le1\). The terms cross at
\(\tau_0=\beta/\alpha\). Thus on \([0,\tau_0]\),

\[
 \Psi\ge D+\tau(\beta-\kappa).
\]

Its minimum on that interval is at an endpoint. At zero it is positive
by (6); at \(\tau_0\) it is strictly greater than

\[
 \frac\beta\alpha(c-\beta)
 +\frac\beta\alpha(\beta-\kappa)
 =\frac\beta\alpha(c-\kappa)>0.
\]

On \([\tau_0,1]\),

\[
 \Psi\ge D-\beta+\tau(2h-\kappa).
\]

This increases because \(2h\ge1>\kappa\), so its minimum is
the same positive value at \(\tau_0\).

For \(\tau\ge1\), the smaller outward-quadrant support is
\(h+j\tau\). Hence

\[
 \Psi\ge D+\tau(h+j-\kappa)
 =D+\tau(\alpha-\kappa)>0,
\]

since \(\alpha\ge c>\kappa\).

Finally, if \(\beta=0\), then \(h=j=1/2\), \(D=0\), and
\(H_A((1,\tau))=(1+\tau)/2\). Thus
\(\Psi=\tau(1-\kappa)>0\). This proves (9) in every orientation.

## 5. Applying the physical separator

Let \(d=x_B-x_A\) and \(\tau=s/p>0\). Since B is contained,
\(y_B+h_B\le r\). From (1),

\[
 y_B-y_A\le r-\frac38-h_A-h_B
 =1+\kappa-h_A-h_B.
\]

Combine this upper bound with the physical separator (2), and use

\[
 H_B(n)+(p+s)h_B\ge p+s.
\]

The result is

\[
 \begin{aligned}
 p(d+h_B)
 &\ge H_A(n)+s h_A-s(1+\kappa)
       +H_B(n)+(p+s)h_B\\
 &\ge p+H_A(n)+s(h_A-\kappa).
 \end{aligned}
\]

After dividing by p and applying (9),

\[
 d+h_B\ge1+H_A((1,\tau))+\tau(h_A-\kappa)
 >1+h_A-D.
\]

Equivalently,

\[
 b(1-d-h_B+h_A)<\Delta_A. \tag{10}
\]

Add this to the matched cap (4):

\[
 \begin{aligned}
 a(-x_M-h_M)+b(1-x_B-h_B)
 &=[a(-x_M-h_M)+b(-x_A-h_A)]\\
 &\quad+b(1-d-h_B+h_A)\\
 &<T-\Delta_M\le T.
 \end{aligned}
\]

This is the strict transfer cap (3). Every inequality uses actual square
containment, the displayed physical separator, or an explicit orientation
support bound. No common frame for the physical square sides is assumed.
