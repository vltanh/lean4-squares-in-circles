# Uniform side and corner restrictions on two enclosed units

**Status: complete hand implications; independent full hand audit passed.**
Suppose a finite physical ring of interior-disjoint unit squares encloses
one or more further unit squares, all interior-disjoint from that ring.
Assume that every boundary-square center has norm strictly less than

\[
M=\frac{91}{60}.
\]

The C7 circle window supplies this center bound. No positive stress or
common orientation is assumed in this manuscript. Put

\[
k=\frac{(M-1/2)^2}{2}=\frac{3721}{7200},\qquad
e=k-\frac12=\frac{121}{7200},\qquad
d=\sqrt{\frac52}-M.
\]

We prove three whole-orientation restrictions:

1. Every own coordinate of an enclosed unit's center has absolute value
   strictly less than \(k\).
2. Every vertex of every enclosed unit has norm strictly greater than
   \(d\).
3. If two enclosed units are interior-disjoint, their relative frame angle
   \(\theta\in[0,\pi/4]\) satisfies \(\cos\theta>6/7\).

These restrictions do not by themselves prove C7 completion. The
remaining nearly parallel two-square configurations still require a
whole geometric or stress argument.

## 1. Quantitative side restriction

Use the notation and orientation-uniform radial-tail proof of
`CENTER_COVER_PIERCING.md`, Sections 1--4. If an enclosed unit \(T\)
has an own center coordinate of magnitude at least \(k\), rotate and
reflect to put its center at \((r,0)\), with frame vectors
\((u,-v),(v,u)\), where

\[
u\ge v\ge0,\quad u^2+v^2=1,\qquad r\ge k/u.
\]

An outer square \(S\) meets the outward radial tail of \(T\). A physical
separator from \(T\) to \(S\) has positive first coordinate, and we
write it as \(n=(a,\pm b)\), with \(a>0,b\ge0,a^2+b^2=1\).
As in the cited proof, set

\[
F=ra+H_T(n),\qquad n\cdot C_S\ge F+H_S(n).
\]

### 1.1. Shallow separators

For \(a\ge b\), the positive support expression is concave between
successive frame alignments as a function of the signed normal angle.
At the own-axis breakpoint it is at least \(k+1/2\). At either
forty-five-degree endpoint it is at least

\[
\frac{k/u+u}{\sqrt2}\ge\sqrt{2k}=M-1/2.
\]

Also \(k+1/2\ge\sqrt{2k}\), since the squared difference is
\((k-1/2)^2\). Hence every shallow separator gives
\(F\ge M-1/2\), and then \(|C_S|\ge F+H_S(n)\ge M\),
contradicting the strict center bound.

### 1.2. Steep separators

Here the original radial-tail proof already applies, because
\(r\ge k/u>1/(2u)\). It gives

\[
|C_S|^2\ge(L(a)-h)^2+h^2,\qquad
\frac12\le h\le\frac1{\sqrt2},
\]

where

\[
L(a)=a+\frac1{2a}+\frac1{2\sqrt{1-a^2}},
\qquad 0<a\le1/\sqrt2.
\]

We sharpen only the elementary lower bound on this same function. Write
\(b=\sqrt{1-a^2}\). Then

\[
L''(a)=\frac1{a^3}+\frac1{2b^3}+\frac{3a^2}{2b^5}>5.
\]

Indeed, for \(a\le1/2\) the first term is at least eight. For
\(1/2\le a\le1/\sqrt2\), the sum of the first two terms decreases
with \(a\) and is at least \(3\sqrt2\). The last term is at least
\(4/(3\sqrt3)\). The exact comparisons

\[
3\sqrt2>106/25,\qquad 4/(3\sqrt3)>19/25
\]

give the strict bound five. At \(a_0=3/5\),

\[
L(a_0)=247/120,\qquad L'(a_0)=227/1152<1/5.
\]

The quadratic lower bound from \(L''>5\), followed by completing the
square, therefore yields

\[
L(a)\ge\frac{247}{120}-\frac{L'(a_0)^2}{10}
>\frac{247}{120}-\frac1{250}
=\frac{6163}{3000}>\frac{197}{96}.
\]

Meanwhile

\[
\frac1{\sqrt2}<\frac{17}{24},\qquad
\sqrt{M^2-1/2}=\frac{\sqrt{6481}}{60}<\frac{43}{32},
\]

so their sum is less than \(197/96\). The function
\((L-h)^2+h^2\) decreases over \(1/2\le h\le1/\sqrt2\).
Consequently \(|C_S|^2>M^2\), again a contradiction.

Every own center coordinate of \(T\) is therefore strictly between
\(-k\) and \(k\), as claimed.

## 2. The sharp corner-tail lemma

**Lemma.** Let \(T=[0,1]^2\). If a unit square \(S\), interior-disjoint
from \(T\), meets the diagonal tail \(\{(t,t):t\ge1\}\), then
\(|C_S|\ge\sqrt{5/2}\).

Take a square-owned SAT separator directed from \(T\) to \(S\).
If it is owned by \(T\), it must be \(e_x\) or \(e_y\), since a
point of the indicated tail belongs to \(S\). In the first case, writing
\(h=H_S(e_x)=H_S(e_y)\in[1/2,1/\sqrt2]\), separation and tail
membership give

\[
C_x\ge1+h,\qquad C_y\ge1-h,
\]

so \(|C_S|^2\ge(1+h)^2+(1-h)^2\ge5/2\). The second case is its
reflection.

Otherwise the separator is an own normal of \(S\). Its coordinate sum
is positive: its support on \(T\) is nonnegative, while a point of the
positive diagonal tail belongs to \(S\), so its normal projection is
at least the support value of \(S\)'s inner face. A zero coordinate sum
would have strictly positive support on \(T\) and is impossible too.
Up to interchanging the
two coordinates there are two cases.

First take \(n=(a,b)\), \(a\ge b\ge0\). Put
\(c=a+b\), \(f=a-b\), and \(m=(-b,a)\). The own-axis bounds are

\[
n\cdot C_S\ge c+1/2,\qquad m\cdot C_S\ge f-1/2.
\]

If \(f\ge1/2\), their squared sum is

\[
(c+1/2)^2+(f-1/2)^2=5/2+c-f\ge5/2.
\]

If \(f<1/2\), then \(c^2=2-f^2>7/4\), so the first coordinate
alone has square greater than \(5/2\).

Second take \(n=(a,-b)\), with \(a>b\ge0\), and \(m=(b,a)\).
Separation gives \(n\cdot C_S\ge a+1/2\). If \((t,t)\in S\),
its own normal coordinate also satisfies

\[
t(a-b)\ge n\cdot C_S-1/2\ge a,
\]

so \(t\ge a/(a-b)\). Therefore

\[
m\cdot C_S\ge\frac{a(a+b)}{a-b}-\frac12\ge\frac12+b.
\]

The last inequality follows upon multiplying by \(a-b>0\): its
difference is \(1-a+b\ge0\). Hence

\[
|C_S|^2\ge(a+1/2)^2+(b+1/2)^2
=3/2+a+b\ge5/2.
\]

This exhausts all own-normal signs. Equality is possible, for example
for \(S=[1,2]\times[0,1]\), whose center is \((3/2,1/2)\).

Now let \(p\) be any vertex of an enclosed unit, and use its two inward
edge axes to translate and rotate it to \([0,1]^2\). Following the
outward center diagonal eventually meets a boundary square, because the
unit is in a bounded complementary region. The lemma gives

\[
|C_S-p|\ge\sqrt{5/2}.
\]

But \(|C_S|<M\), so \(|p|\le d\) would contradict the triangle
inequality. Thus every enclosed vertex satisfies \(|p|>d\).

## 3. Every enclosed pair has nearly parallel frames

Let two enclosed units be interior-disjoint. Choose a SAT normal owned
by one of them, call it \(T\), and direct it from the other unit \(U\)
to \(T\). Write this normal as \(n\). Section 1 gives

\[
\min_{x\in T}n\cdot x<k-1/2=e.
\]

Choose the signs and order of \(U\)'s own axes so that the components
of \(n\) are \((c,s)=(\cos\theta,\sin\theta)\), with
\(0\le\theta\le\pi/4\). Let \(p\) be the supporting corner of
\(U\) in this direction, and write its own coordinates as \(p_1,p_2\).
The own-center bound and separation give

\[
p_1>-e,\qquad p_2>-e,\qquad cp_1+sp_2<e.
\]

If \(s>0\), this is a triangle whose closure has vertices

\[
(-e,-e),\quad
\left(\frac{e(1+s)}c,-e\right),\quad
\left(-e,\frac{e(1+c)}s\right).
\]

The maximum norm on that triangle occurs at a vertex, and is the last
one's norm, namely

\[
|p|\le\frac{e}{\sin(\theta/2)}.
\]

If \(c\le6/7\), then \(\sin(\theta/2)\ge1/\sqrt{14}\), giving

\[
|p|\le e\sqrt{14}<\frac{19}{300}<d.
\]

The first strict comparison reduces after squaring to
\(204974<207936\). For the second, use
\(\sqrt{5/2}>79/50\) and \(79/50-91/60=19/300\).
This contradicts Section 2. Therefore \(\cos\theta>6/7\).

The conclusion retains all positions and all independently oriented
enclosed squares. It is a necessary pair restriction, not an alignment
normalization or the missing capacity theorem.
