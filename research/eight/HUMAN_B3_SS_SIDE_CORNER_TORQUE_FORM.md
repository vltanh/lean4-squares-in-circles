# Exact force-and-torque normal form for the two surviving radial SS branching triangles

**Structural research, 2026-10-13.** This is a hand
equilibrium normal form built from the preceding
[HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md]
(HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md).
That dichotomy uses the separately certified global
coarse bound \(R_8^2>19/5\); the derivation below is
otherwise exact force/torque algebra for true
square contact points.

## Theorem (one free C contact coordinate is eliminated)

Assume the smallest k7/B3 positive core
\(C-X-Y-C\) plus SS radial side bridge \(C-Z\),
and the contact-minimal all-frame conclusions
of HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md.

Choose axes \(n=(1,0)\) along the radial
leaf, \(t=Jn=(0,1)\).
Let
\[
\rho=\sqrt{R^2-\tfrac14},\quad
b=\rho-1,\quad k=1-b=2-\rho,\quad
p_C=(b-\tfrac12,d),\quad |d|<\tfrac12.
\]
The whole bridge leaf has true circle side
normal n, contact midpoint \((b,0)\), and
is parallel to C.

**Positive sign mode \(d>0\).** Relabel the two
triangle squares so that X contacts the true
top-left C corner and Y contacts the genuine
bottom C side:
\[
\begin{aligned}
z_X&=-k n+(d+\tfrac12)t,\\
m_X&=-c\,n+s\,t,\qquad c>0,\ s>0,\ c^2+s^2=1,\\
z_Y&=\xi n+(d-\tfrac12)t,\qquad
m_Y=-t,\\
z_Z&=b n,\qquad m_Z=n.
\end{aligned}
\]
All these are actual positive-stress
combined contact points and genuine
unit pair-separating normals, directed
outward from C.

Then physical **force and torque balance
at the circle-free C** imply the exact equations
\[
\boxed{
\lambda_Z=\lambda_X c,\quad
\lambda_Y=\lambda_X s,\quad
\xi=-k+\frac cs(d+\tfrac12).
}                                                \tag{1}
\]
The true bottom support segment of C requires
\(\xi\in[-k,b]\), therefore
\[
\boxed{
0<\frac cs(d+\tfrac12)\le1,\quad
\frac cs<2,\quad s>\frac1{\sqrt5}.
}                                                \tag{2}
\]
The first strict inequality follows from c,s>0
and d+1/2>0; the strict \(c/s<2\) follows
from \(d+1/2>1/2\). Equivalently the positive
corner-normal's transverse component is
**bounded below structurally**:
\(s>1/\sqrt5\).

Moreover, because \(m_X\) has both nonzero
components relative to C, its true C support
is a **single corner**, so the genuine SAT
separator must be a **true side normal
of the rotated square X**.
Thus one of X's two orthogonal frame
directions is **exactly \(m_X\)**,
while Y's frame remains free
(subject to all its true contacts).

**Reflected sign mode \(d<0\).**
After reflecting across the radial n axis and
exchanging the upper/lower triangle labels,
the identical equations hold with
\(d\) replaced by \(-d>0\),
the corner contact at the bottom-left
C corner, and the other positive normal
equal to \(+t\).

There is no \(d=0\) case in the separately
proved SS side-corner dichotomy.

## Proof

The true central SS bridge is radial at
\(z_Z=b n\), with outward C-normal +n.
The dichotomy theorem for d>0 fixes
the other two genuine C contact normals
to \(m_Y=-t\) and \(m_X=-c n+s t\),
with both c and s strictly positive.
The actual C contact faces then force
\(z_X\) to be its top-left corner and
\(z_Y\) to lie on the bottom side
with \(-k\le\xi\le b\).

Since C carries no disk-circle forces,
the three positive outward contact normal
vectors balance:
\[
\lambda_X(-c n+s t)
   -\lambda_Y t+\lambda_Z n=0.
\]
The independent n and t components yield
\(\lambda_Z=\lambda_X c\) and
\(\lambda_Y=\lambda_X s\).

The radial Z contact has zero origin moment:
\(z_Z\times m_Z=0\).
With \(n\times t=1\), the other two moments are
\[
\begin{aligned}
z_X\times m_X
&= (-k n+(d+\tfrac12)t)
      \times(-c n+s t)
 =-ks+c(d+\tfrac12),\\
z_Y\times m_Y
&=(\xi n+(d-\tfrac12)t)\times(-t)
=-\xi.
\end{aligned}
\]
Torque balance with positive weights gives
\[
\lambda_X[-ks+c(d+\tfrac12)]
  -\lambda_Y\xi=0.
\]
Substitute \(\lambda_Y=\lambda_Xs>0\),
divide by \(\lambda_Xs\), and obtain
\[
\xi=-k+\frac cs(d+\tfrac12).
\]

The genuine C bottom side has n-coordinate
interval \([b-1,b]=[-k,1-k]\).
Hence \(-k\le\xi\le b\)
implies \(0\le(c/s)(d+1/2)\le1\),
with the left inequality strict by
the positive factors. Because d>0,
\(d+1/2>1/2\), giving \(c/s<2\).
Use \(c^2+s^2=1\):
\(c<2s\) implies \(1=c^2+s^2<5s^2\),
so \(s>1/\sqrt5\).

Finally, a normal with both nonzero n/t
components exposes a genuine **C corner**,
not one of C's side segments.
The square--square separating-axis theorem
requires the positive pair normal to be
an actual side normal of at least one
of the two squares, so it must be a
true side normal of X. This locks one
X frame direction.

Reflection t↦−t exchanges d>0 with d<0,
top/bottom corners and X/Y, while preserving
all force/torque and disk constraints.
This proves the reflected case. QED.

## Structural use and limitations

Together with the prior dichotomy, the entire
still-open radial **SS minimal B3 core**
has only **two reflection-related true-contact
incidences**, with a fixed radial Z frame,
a fixed corner-owned X frame direction
and **one exact algebraic equation** for
the Y central contact coordinate.

This does not fix Y's frame, the actual X--Y
positive contact normal, zero-weight actual
contacts or the four spectator squares.
A sharp entire-case radius obstruction
\(R\ge\widehat R\) is still missing.
Do not silently remove the separate
GLOBAL_LOWER_BOUND.md exact computational
certificate dependency of the original
SS side-corner dichotomy.

The CS and SD radial bridge interfaces,
larger B3 positive components, true equality
outer ring A, B2 m4..6, X and lower-k roots
are all unclosed.
