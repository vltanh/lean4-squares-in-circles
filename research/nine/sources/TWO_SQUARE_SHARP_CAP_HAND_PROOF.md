# Exact two-square directional cap: a short hand proof

This note is a hand proof. No numerical search, enumeration, arithmetic script,
Lean invocation or CI result is used as a premise.

Let

\[
 Q=\frac{1105}{256},\qquad
 \rho=\frac{\sqrt{1041}-8}{16},\qquad
 d=\rho-\frac12,\qquad
 k=\sqrt{d^2+\frac14},\qquad
 H=\frac{\rho d}{k}.
\]

Thus

\[
 Q=\rho^2+\rho+\frac12
   =d^2+2d+\frac54,
 \qquad k^2=d^2+\frac14.
\]

We have \(3/2<\rho<91/60\), hence \(d>1\), \(d<k<6/5\), and
\(\rho-k<1/2\). Also \(H>k\): this is equivalent to
\(\rho d>k^2\), or \(d/2>1/4\).

## The common-point theorem

For every unit direction \(e\), every unit square \(S\subseteq B(0,\sqrt Q)\)
whose center \(c\) satisfies \(e\cdot c\ge H\) contains the point \(p=ke\).
If \(e\cdot c>H\), then \(p\) belongs to the interior of \(S\).

### 1. Reduction to one scalar boundary expression

Take an orthonormal square frame \(u,v\), and write

\[
 \alpha=c\cdot u,\quad \beta=c\cdot v,\quad
 a=e\cdot u,\quad b=e\cdot v.
\]

Containment of the square gives exactly

\[
 (|\alpha|+\tfrac12)^2+(|\beta|+\tfrac12)^2\le Q. \tag{1}
\]

In particular \(|c|\le\rho\), since the left side is at least
\(|c|^2+|c|+1/2\). Assume \(e\cdot c\ge H>k\); otherwise there is
nothing to prove. Then \(r=|c|\ge H>k\).

If \(p\) fails to belong to the square interior, one of its four side
inequalities fails strictly or is an equality. Reverse the relevant frame
axis and call it \(u\), so

\[
 \alpha-ka\ge\tfrac12,
 \qquad a\le a_0:=\frac{\alpha-1/2}{k}. \tag{2}
\]

Reverse \(v\) if necessary so \(\beta\ge0\). For an upper bound on
\(e\cdot c\), one may take \(b=\sqrt{1-a^2}\). The unconstrained maximum of
\(\alpha a+\beta\sqrt{1-a^2}\) is at \(a=\alpha/r\), and

\[
 \frac\alpha r-a_0
 =\frac{1/2-\alpha(1-k/r)}{k}>0, \tag{3}
\]

because \(1-k/r>0\), \(\alpha\le r\), and \(r-k\le\rho-k<1/2\).
Therefore its maximum under (2) is attained at \(a=a_0\). If \(a_0<-1\)
there is no feasible direction; \(a_0<1\) follows from \(\alpha\le\rho<k+1/2\).
Put

\[
 s=\sqrt{k^2-(\alpha-1/2)^2}.
\]

The upper bound is

\[
 k(e\cdot c)\le
 \alpha(\alpha-\tfrac12)
 +\left(\sqrt{Q-(|\alpha|+1/2)^2}-\tfrac12\right)s. \tag{4}
\]

For a strict inequality in (2), the bound is strict. The case \(\beta=0\)
causes no exception: (2) is then a nontrivial restriction on a linear function,
with its unconstrained maximum still lying on the excluded side by (3).

### 2. The case \(\alpha\ge0\): one factored identity

Put

\[
 t=\alpha-\tfrac12\in[-\tfrac12,d],\qquad
 U=d-t=\rho-\alpha\in[0,\rho],\qquad z=s-\tfrac12\ge0.
\]

Then

\[
 s^2=d^2+\tfrac14-t^2=U(2d-U)+\tfrac14,
 \qquad Q-(\alpha+\tfrac12)^2=s^2+2U.
\]

The desired upper bound in (4), \(k(e\cdot c)\le\rho d\), is equivalent to

\[
 s\sqrt{s^2+2U}\le s^2+\frac{U+z}{2}. \tag{5}
\]

Both sides are nonnegative. Their squared difference factors as

\[
 \left(s^2+\frac{U+z}{2}\right)^2-s^2(s^2+2U)
 =\frac14(U-z-1)(U-z-4z^2). \tag{6}
\]

Each factor on the right is nonpositive. First, \(U\le z+1=s+1/2\), since

\[
 s^2-(U-\tfrac12)^2=2U(\rho-U)\ge0
\]

(and the conclusion is immediate when \(U<1/2\)). For the second factor,
the following two intervals cover the whole range:

| Range | Elementary bound | Consequence |
|---|---|---|
| \(0\le U\le d-1/2\) | \(s^2-(U+1/2)^2=2U(d-1/2-U)\ge0\) | \(z\ge U\), hence \(z+4z^2\ge U\) |
| \(d-1/2\le U\le d+1/2\) | \(s^2-d^2=1/4-(U-d)^2\ge0\) | \(z\ge d-1/2\), hence \(z+4z^2\ge4d^2-3d+1/2\ge d+1/2\ge U\) |

The penultimate inequality is exactly \(4d(d-1)\ge0\). Thus (6) is
nonnegative, proving (5) and (4)'s upper bound.

Since \(d>1\), equality in (5) can occur only at \(U=0\) or
\(U=\rho\), namely \(\alpha=\rho\) or \(\alpha=0\). Indeed the second
factor in (6) is strictly negative for \(U>0\), while the first can vanish
only at \(U=\rho\).

### 3. The case \(\alpha<0\): reflection reduces to the previous case

Write \(\alpha=-x\) with \(x>0\). Feasibility of (2) gives
\(x+1/2\le k\). Let

\[
 s_- =\sqrt{k^2-(x+1/2)^2},\quad
 s_+ =\sqrt{k^2-(x-1/2)^2},\quad
 B=\sqrt{Q-(x+1/2)^2}-\tfrac12.
\]

Here \(s_+>s_-\), and

\[
 B\ge\sqrt{Q-k^2}-\tfrac12
  =\sqrt{2\rho}-\tfrac12
  >\frac65>k\ge s_+.
\]

The strict middle bound follows from \(\rho>3/2\) and
\(3>(17/10)^2\). The right side of (4) for \(\alpha=-x\), minus that
for \(\alpha=x\), is

\[
 x+B(s_--s_+)
 =x\left(1-\frac{2B}{s_-+s_+}\right)<0.
\]

The nonnegative case therefore gives a strictly stronger bound here.

### 4. Conclusion and boundary cases

If \(p\) fails to belong to the square interior, (4) gives
\(e\cdot c\le H\). If \(p\) is outside the closed square, (2) is strict
and gives \(e\cdot c<H\). Consequently \(e\cdot c\ge H\) forces
\(p\in S\), and \(e\cdot c>H\) forces \(p\in\operatorname{int}S\).
All weak side contacts and all zero coordinates have been retained.

## Sharp two-square corollary

For any two interior-disjoint unit squares \(S_1,S_2\subseteq B(0,\sqrt Q)\)
and any unit direction \(e\),

\[
 \boxed{\min(e\cdot c_1,e\cdot c_2)\le H<\frac{109}{80}<\frac{137}{100}.}
\]

If both center projections exceeded \(H\), the common point \(ke\) would
belong to both interiors. More strongly, if both projections are at least
\(H\), neither square can contain \(ke\) in its interior: the other closed
square has interior points arbitrarily near that point, producing an overlap.
Hence both projections equal \(H\), and equality in the proof forces the
two reflected radial-side-normal squares described below.

To check the displayed rational bound without decimal arithmetic, the function
\(r(r-1/2)/\sqrt{(r-1/2)^2+1/4}\) is strictly increasing for \(r>1/2\)
(both positive factors \(r\) and \((r-1/2)/\sqrt{(r-1/2)^2+1/4}\) increase).
Thus \(\rho<91/60\) gives

\[
 H<\frac{5551}{60\sqrt{4621}}<\frac{109}{80},
\]

where the second comparison follows by squaring from

\[
 9\cdot4621\cdot11881-16\cdot5551^2=1,101,293>0.
\]

The bound \(\rho<91/60\) itself follows from
\((91/60)^2+91/60+1/2-Q=31/57600>0\).

### Exact attainers for the two-square cap

Take \(e=(0,1)\). Set

\[
 r_+=\left(\frac1{2k},\frac d k\right),\qquad
 t_+=\left(\frac d k,-\frac1{2k}\right),\qquad
 c_+=\rho r_+.
\]

Let \(S_+=c_++[-1/2,1/2]r_++[-1/2,1/2]t_+\), and let \(S_-\) be its
reflection in the vertical axis. These are unit squares with center heights
\(H\). Their maximum squared vertex norm is
\(\rho^2+\rho+1/2=Q\). The leftmost point of \(S_+\) is

\[
 c_+-\tfrac12r_+-\tfrac12t_+=(0,k).
\]

Thus \(S_+\subseteq\{x\ge0\}\), \(S_-\subseteq\{x\le0\}\), and their
intersection is exactly \(\{(0,k)\}\). The bound \(H\) is sharp.

The equality conditions in Sections 1--3 show that, up to interchanging the
squares and reflection across the line \(\mathbb Re\), this is the unique
pair attaining \(\min(e\cdot c_1,e\cdot c_2)=H\).

## Global consequences that need no common square frame

For any packing of \(n\) units in the closed \(Q\)-disk:

1. **Every center segment meets the central \(H\)-disk.** If the point
   \(p_0\in[c_i,c_j]\) closest to the origin had \(|p_0|>H\), the elementary
   closest-point inequality \((c_i-p_0)\cdot p_0\ge0\) and its counterpart
   for \(c_j\), with \(e=p_0/|p_0|\), would give both projections greater
   than \(H\), contradicting the two-square theorem.

2. **A universal occupied-arc inequality.** Put \(r_i=|c_i|\). For \(r_i>H\),
   the arc \(\{ke:e\cdot c_i>H\}\) on the circle of radius \(k\) has
   angular length \(2\arccos(H/r_i)\) and lies inside the interior of square
   \(i\). These open arcs are pairwise disjoint, so

   \[
   \sum_{i:r_i>H}\arccos(H/r_i)\le\pi.
   \]

3. If \(m\ge3\) centers all have radius at least \(r>H\), then the previous
   inequality gives \(m\arccos(H/r)\le\pi\), or
   \(r\le H\sec(\pi/m)\).

These conclusions use the original centers and every physical square;
they require no contact graph, load condition or orientation normalization.

### A boundary corner strictly exposes its square's center

Let \(R=\sqrt Q\), and suppose a corner of square \(S_i\) lies at \(Re\)
for a unit direction \(e\). This corner maximizes the projection onto \(e\)
over the disk and therefore over the square, so

\[
 e\cdot c_i=R-h_{S_i-c_i}(e)\ge R-\frac1{\sqrt2}>H.
\]

The common-point theorem puts \(ke\) in the interior of \(S_i\). Every
other square \(S_j\) must therefore have \(e\cdot c_j<H\): otherwise it
would contain \(ke\), and its interior points sufficiently near that point
would overlap the interior of \(S_i\). In particular

\[
 e\cdot(c_i-c_j)>R-\frac1{\sqrt2}-H>\frac1{400}.
\]

For the final rational comparison, \(R>83/40\), \(1/\sqrt2<71/100\), and
\(H<109/80\), so their difference is greater than
\(83/40-71/100-109/80=1/400\). Thus the center of every square touching
the actual \(Q\)-circle is uniquely exposed along each of its corner-contact
directions, with the displayed uniform separation from all other centers.

## Scope

This replaces the handoff's conditional \(137/100\) directional two-square
cap with a stronger, exact sharp theorem and an elementary two-interval proof.
It applies uniformly to every pair, every orientation, every direction, and
the complete closed \(Q\)-disk domain. It supplies no assertion that all nine
centers admit a particular strip, row or two-direction decomposition. The
global nine-square lower bound and its missing exhaustive caller remain open.
