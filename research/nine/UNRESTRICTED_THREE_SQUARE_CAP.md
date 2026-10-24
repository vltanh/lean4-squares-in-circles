# n=9: sharp three-square cap rigidity without common separating axes

**Status:** complete hand derivation for the stated cap, including equality.
This is a new terminal theorem for independently oriented, physically
nonoverlapping squares. It does **not** assume disjoint coordinate
projections, a shared square orientation, or a common separating frame.
The unrestricted nine-square optimal-radius theorem is not established here.

Originally drafted against source `a6b37a74769908a64cef5835550f0ec04191eb98` and reconciled with later radial bridge commit `028a63b4fc963eb78d776a7f42ff3606e651e816`. Imported into the draft GitHub research branch on 2026-10-23. **Independent full audit, Lean build, and CI were not run.** Its accompanying exact regression script and report are in the local proof package; finite checks do not replace the hand derivation.

## 1. Exact statement

Put

\[
 Q=\frac{1105}{256},\qquad R=\sqrt Q,\qquad
 s=\frac7{16},\qquad z=\frac54,\qquad C=\frac32.
\]

Let \(D_Q=\{(x,y):x^2+y^2\le Q\}\) and let
\(L=[-C,C]\times\{z\}\), a horizontal segment of length three.

**Theorem 1 (one-square clipped-section inequality).** Every closed unit
square \(S\subset D_Q\cap\{y\ge s\}\), in any orientation, satisfies

\[
                   \operatorname{length}(S\cap L)\ge1.       \tag{1}
\]

The intersection is a nondegenerate horizontal section of the square,
not a segment contained in a horizontal boundary side. If the square
is not axis-parallel to the displayed coordinates, the inequality is
**strict**.

**Theorem 2 (three-square cap rigidity).** If three closed unit squares
with pairwise disjoint open interiors are contained in
\(D_Q\cap\{y\ge7/16\}\), then all three are axis-parallel. After ordering
by horizontal position, their centers are exactly

\[
 (-1,15/16),\qquad(0,\eta),\qquad(1,15/16),
 \qquad
 \frac{15}{16}\le\eta\le\frac{\sqrt{1041}}{16}-\frac12.      \tag{2}
\]

Conversely every choice in (2) gives such a cap packing. In particular,
if the three squares lie in the smaller disk \(D_q\), \(0\le q\le Q\),
then \(q=Q\). Four squares cannot fit in this cap.

The proof is a single horizontal-section estimate, not a position or
angle grid. Its algebra includes one monotone cubic and exact endpoint
comparisons. A finite sampling script accompanies it only as a regression
check, not as a premise.

## 2. Common one-square coordinates and elementary bounds

Quarter-turning the frame describing a square does not change the square.
Its side axes can therefore be written in one of the two forms

\[
 (a,b),(-b,a)\quad\text{or}\quad(a,-b),(b,a),
 \qquad a\ge b\ge0,\quad a^2+b^2=1.
\]

Write the center as \((x,y)\), and set

\[
 h=\frac{a+b}{2},\qquad t=\frac{a-b}{2},\qquad
 w=a+b,\qquad d=w-1,\qquad \delta=z-y.
\]

The horizontal and vertical projection halfwidths both equal \(h\).
The cap and the square's top vertex give

\[
                   s+h\le y\le R-h.                        \tag{3}
\]

The exact constants obey

\[
 R<25/12<17/8,\qquad z-s=13/16<5/6,
 \qquad C^2+(s+1)^2=Q.
\]

Hence

\[
                         |\delta|<5/6-h<h.                  \tag{4}
\]

Thus the line \(y=z\) passes strictly between the square's bottom and
top supporting lines. When \(b>0\), its full horizontal section has
length

\[
 W=\min\left\{\frac1a,\frac{h-|\delta|}{ab}\right\}.         \tag{5}
\]

This follows by intersecting the four side inequalities, or by splitting
at \(|\delta|=(a-b)/2\). Both expressions in (5) are strictly greater
than one. Indeed, \(a<1\), while

\[
 w-ab=w-\frac{w^2-1}{2}\ge\sqrt2-\frac12>\frac56
 \quad(1\le w\le\sqrt2),
\]

so (4) gives \(h-|\delta|>2h-5/6=w-5/6>ab\).

It remains to prove that clipping this section to \([-C,C]\) does not
reduce its length to one or less. Let \(\ell,r\) be the full section's
left and right endpoints. We will show, for \(b>0\),

\[
                        \ell<C-1=\frac12,
 \qquad                 r>1-C=-\frac12.                    \tag{6}
\]

Together with \(r-\ell>1\), these inequalities imply
\(\min(r,C)-\max(\ell,-C)>1\): if neither endpoint is clipped use
\(r-\ell>1\); if one is clipped use (6); if both are clipped the
length is three. Reflection in the vertical axis exchanges the two
orientation forms and the left/right endpoints. It suffices to prove
the bound for \(\ell\) in each form.

For \(0\le Y\le R\), put \(g(Y)=\sqrt{R^2-Y^2}\). Let

\[
                  Y_0=s+1=23/16,\qquad K=Y_0/C=23/24.
\]

The concavity of the circle's right boundary gives

\[
 g(Y_0+d)\le C-Kd,\qquad
 g(Y_0-(1-a))\le C+K(1-a).                                  \tag{7}
\]

Whenever \(Y_0+d\le R\), the exact difference of squares also gives

\[
 D:=C-g(Y_0+d)
   =\frac{2Y_0d+d^2}{C+g(Y_0+d)}
   \ge Kd+\frac{d^2}{3}.                                   \tag{8}
\]

All uses of (7)–(8) below involve the height lower bound of an actual
vertex in the disk, so the radicals are defined.

## 3. Positive tilt: both possible left edges

Take \(u=(a,b),v=(-b,a)\), with \(b>0\). Directly solving the side
inequalities at height \(z\) gives

\[
 \ell=\max(\ell_1,\ell_2),\qquad
 \ell_1=x-\frac{1/2+b\delta}{a},\qquad
 \ell_2=x+\frac{a\delta-1/2}{b}.                            \tag{9}
\]

The actual top vertex is \(P=(x+t,y+h)\), with
\(P_y\ge s+w=Y_0+d\).

### 3.1 The first edge is always safe

We have

\[
                  a\ell_1=aP_x+bP_y-1-bz.
\]

For \(P\in D_Q\) with \(P_y\ge s+w\), the maximum of
\(aP_x+bP_y\) is attained at \(P_y=s+w\). In fact

\[
 s+w-Rb=s+a-(R-1)b\ge s+(2-R)b>0,
\]

using \(R<17/8\), \(b\le1\), and \(s=7/16\).
The unrestricted circle support height is \(Rb\); above this height,
\(a g(Y)+bY\) is decreasing. Therefore (7) yields

\[
 a\ell_1\le aC-aKd+b(w-13/16)-1.                            \tag{10}
\]

The needed inequality follows from the following short algebraic bound:

\[
 b(w-3/4)<1-a+\frac34a(w-1).                                \tag{11}
\]

To verify it, let \(E\) be the right side minus the left side. Then

\[
 4E=b(3-a)-7a(1-a)
     =\frac b{1+a}\bigl(3+2a-a^2-7ab\bigr)>0.
\]

Indeed \(a\ge1/\sqrt2>1/2\) implies \(2a-a^2\ge3/4\),
and \(ab\le1/2\), so the last bracket is at least \(1/4\).
Since \(K\ge3/4\) and \(13/16\ge3/4\), (11) is stronger than
what (10) requires. It proves \(\ell_1<C-1\).

### 3.2 The second edge is safe whenever active

The inequality \(\ell_2\ge\ell_1\) is equivalent to \(\delta\ge t\).
In that case (3) gives

\[
              a=h+t\le z-s=13/16.                          \tag{12}
\]

Also

\[
 b\ell_2=bP_x-aP_y+az
          \le b g(s+w)-a(w-13/16),
\]

because \(b g(Y)-aY\) decreases for positive \(Y\). Hence

\[
 C-\ell_2\ge D+\frac ab(w-13/16)
        \ge K(w-1)+\frac{(w-1)^2}{3}+w-13/16=:H(w).         \tag{13}
\]

On the arc \(a\ge b\ge0\), \(a^2+b^2=1\), the sum \(a+b\)
is decreasing as \(a\) increases. Thus (12) implies

\[
 w\ge w_0:=\frac{13+\sqrt{87}}{16}.
\]

The polynomial \(H\) is increasing for \(w\ge1\). Exact substitution
in (13) gives

\[
 H(w_0)-1=\frac{44\sqrt{87}-405}{384}>0,
\]

since \(44^2\cdot87=168432>164025=405^2\). Thus the active second
edge also satisfies \(\ell_2<C-1\). If it is inactive, the first
edge already gives the bound for \(\ell\). This proves (6) for
positive tilt.

## 4. Negative tilt: both left edges

Take \(u=(a,-b),v=(b,a)\), with \(b>0\). Then

\[
 \ell=\max(m_1,m_2),\qquad
 m_1=x+\frac{b\delta-1/2}{a},\qquad
 m_2=x+\frac{-a\delta-1/2}{b}.                             \tag{14}
\]

### 4.1 First edge: one monotone cubic

Use the actual rightmost vertex \(P=(x+h,y+t)\), whose height is
at least \(s+a\). The identity

\[
 a m_1=aP_x-bP_y+bz-1
\]

and monotonicity of \(a g(Y)-bY\) give

\[
 a m_1\le a g(s+a)+b(13/16-a)-1.
\]

By the second tangent bound in (7),

\[
 a(m_1-(C-1))\le b\left[\frac{13}{16}-F(a)\right],
 \qquad
 F(a)=a+\frac b{1+a}(1-Ka).                                \tag{15}
\]

Here is a purely algebraic proof that \(F(a)>13/16\). Put
\(k=b/(1+a)\). Then

\[
 0\le k\le\sqrt2-1<5/12,\qquad
 a=\frac{1-k^2}{1+k^2},
\]

and direct expansion gives

\[
 F(a)-\frac{13}{16}
   =\frac{9+2k-87k^2+94k^3}{48(1+k^2)}.                    \tag{16}
\]

The polynomial \(k^2(87-94k)\) is increasing on \([0,5/12]\),
its derivative being \(6k(29-47k)\ge0\). Consequently the numerator
in (16) is at least

\[
 9-(5/12)^2\bigl(87-94(5/12)\bigr)=\frac{601}{864}>0.
\]

No table or root isolation is used. Equation (15) now gives
\(m_1<C-1\).

### 4.2 Second edge: circle support

Use the actual top vertex \(P=(x-t,y+h)\). Then

\[
 b m_2=bP_x+aP_y-az-1\le R-az-1.
\]

The function \(a\mapsto za+\tfrac12\sqrt{1-a^2}\) is concave on
\([1/\sqrt2,1]\). Its minimum is therefore at an endpoint:

\[
 za+\frac b2\ge
 \min\left\{\frac54,\frac7{4\sqrt2}\right\}
 =\frac7{4\sqrt2}>\frac98>R-1.
\]

It follows that \(b m_2<b/2\), so \(m_2<C-1\). This finishes
(6) for negative tilt. Reflecting the entire argument in the vertical
axis gives the right-endpoint inequality in (6).

## 5. Axis-aligned case and cap equality

If \(b=0\), the square is axis-aligned, its center satisfies
\(y\ge s+1/2=15/16\), and its farthest corner gives

\[
 (|x|+1/2)^2+(y+1/2)^2\le Q
 \quad\Longrightarrow\quad |x|+1/2\le C.
\]

Its horizontal slice at \(z\) is therefore a unit interval entirely
inside \([-C,C]\). Equations (3)–(4) show that this line is not a
horizontal side of the square. This proves Theorem 1, including strict
rotation penalty and the interior-section assertion.

For three physically interior-disjoint squares, their sections along
\(y=z\) have disjoint open interiors: each nonendpoint section point is
interior to its square. Their clipped lengths sum to at most three.
Theorem 1 makes each length at least one. Thus every length is one,
none of the squares is rotated, and the three unit intervals tile
\([-3/2,3/2]\). Their center x-coordinates are \(-1,0,1\).
For either extreme square,

\[
 Q\ge(3/2)^2+(y+1/2)^2,
 \qquad y\ge15/16,
\]

so \(y=15/16\). The center square has exactly the height range (2).
This proves necessity, and horizontal unit separation proves the
converse. The outer corners force any stipulated centered disk to
have \(q\ge Q\). Four squares would contribute length at least four
to a segment of length three and are impossible. QED.

## 6. A global necessary condition below the candidate radius

**Corollary 3 (every-direction central-strip occupancy).** Suppose nine
independently oriented unit squares with disjoint open interiors fit
in \(D_q\) for \(q<Q\). In **every** orthonormal coordinate frame:

- at most two squares lie entirely in \(y\ge7/16\);
- at most two lie entirely in \(y\le-7/16\);
- hence at least **five** meet the open strip \(-7/16<y<7/16\).

This is rotation-invariant and requires no common pairwise separator.
Among the squares meeting the strip, their vertical open projection
intervals cannot contain a disjoint chain of three. Indeed, such a
middle interval has length at least one, but would lie between two
strip-interior points less than \(7/8\) apart. Thus their interval
order has height at most two.

**Do not infer** that its antichains are horizontally separable: the
squares may use oblique physical separators. The corollary is an
unrestricted necessary condition, not yet an impossibility proof.

## 7. An exact limit of the cap route: some record-radius packings have no triple cap

One must **not** infer that every record-radius nine-square packing
contains three squares in one of the sharp caps. The following nine
axis-aligned unit squares are a counterexample to that extra assertion:

\[
\begin{array}{c|c}
\text{centers}&\text{number}\\\hline
(\pm3/2,1/16)&2\\
(\pm1/2,1/5)&2\\
(\pm1,-15/16)&2\\
(0,-4/5)&1\\
(\pm3/5,5/4)&2.
\end{array}                                                   \tag{17}
\]

The seven lower squares have disjoint interiors: their two horizontal
chains have unit gaps, the middle lower square is exactly one unit below
the two middle upper squares, and the other cross pairs are separated in
at least one coordinate. The top two are horizontally separated by
\(6/5\) and have bottom height \(3/4>7/10\), the highest point of the
lower seven. Their farthest-corner squared norm is

\[
 (11/10)^2+(7/4)^2=\frac{1709}{400}
                      =Q-\frac{281}{6400}<Q.
\]

The four outer anchors attain Q; all other corners have squared norm
at most Q. Thus (17) is a genuine nine-square packing in the record disk.

In each original axis direction exactly **two** whole squares lie beyond
the offset \(7/16\): the two top squares, the two lower outer squares,
or the appropriate two right/left outer squares. No other orientation
can have three: Theorem 2 would force those three squares to align with
that cap's horizontal/vertical frame, but all squares in (17) have the
original orientation. Only the four already checked axis normals are
possible.

This counterexample does not refute the candidate lower bound. It shows
that a global *equality classification* cannot be replaced by the bare
claim “every packing has a sharp triple cap.” The cap theorem and the
central-strip corollary are exact tools, not an unproved normalization.

## 8. Scope

The cap floor, circle radius and test segment are linked exactly as
above. This manuscript does not assert a universal slice-replacement
inequality for every circular cap; that broader assertion is not used.
The remaining nine-square global obligation is to force a sharp cap or
another terminal structure, or combine the every-direction strip
restriction with the physical contact-stress network. No such global
coverage implication is claimed here.