# A physical seven-square ring defeats the unrestricted diameter extraction

**Status: complete exact negative control; independent full hand audit passed.**
The following tempting implication is false:

> A physical ring of at most seven unit squares enclosing two arbitrary
> interior-disjoint unit squares has boundary-center diameter at least three.

This does not refute the C7 completion target. The example does not meet
the containing-circle hypotheses or the established common annulus for
circle-touching boundary centers. It proves that those hypotheses, or
additional positive-stress information, cannot be discarded from the
diameter-extraction route.

Put \(s=1/\sqrt2\), and write

\[
e=\frac54-s,\qquad h=\frac14+s,\qquad b=\frac32+2s.
\]

An *aligned* unit at \((x,y)\) is
\([x-1/2,x+1/2]\times[y-1/2,y+1/2]\).
A *diagonal* unit at \((x,y)\) is
\(\{(X,Y):|X-x|+|Y-y|\le s\}\), whose sides have length one.
Let \(v=(s,s)\) and \(w=(-s,s)\) be its own orthonormal axes.

## 1. The nine actual unit squares

Take the following seven boundary squares, in clockwise cyclic order:

| Label | Center | Frame |
|---|---|---|
| \(A\) | \((0,0)\) | aligned |
| \(E\) | \((e,1)\) | aligned |
| \(D\) | \((7/4,h)\) | diagonal |
| \(B\) | \((b,s)\) | diagonal |
| \(B'\) | \((b,-s)\) | diagonal |
| \(D'\) | \((7/4,-h)\) | diagonal |
| \(E'\) | \((e,-1)\) | aligned |

Primes denote reflection in the horizontal axis. The two enclosed units
are

\[
T=[1/2,3/2]\times[-1/2,1/2],\qquad
U=\{(X,Y):|X-(3/2+s)|+|Y|\le s\}.
\]

The inequalities \(7/10<s<3/4\) suffice for every elementary ordering
used below. In particular \(1/2<e<11/20\) and \(19/20<h<1\).

## 2. Every consecutive boundary pair actually touches

The squares \(A,E\) share a positive horizontal side segment at
\(y=1/2\): their horizontal intervals overlap because \(0<e<1\).
The reflection gives the \(E'A\) contact.

The leftmost vertex of \(D\) is

\[
p_{ED}=(7/4-s,h)=(e+1/2,h).
\]

It lies in the strict interior of the right side of \(E\), since
\(1/2<h<3/2\). The whole square \(D\) lies to the right of the
line through that side. Thus \(E,D\) touch and have disjoint interiors.
The reflected assertion handles \(D',E'\).

The displacement from \(D\) to \(B\) is

\[
B-D=(2s-1/4,-1/4).
\]

Its own-axis coordinates satisfy

\[
(-w)\cdot(B-D)=1,\qquad
v\cdot(B-D)=1-s/2\in(0,1).
\]

Consequently these two diagonal units share a positive-length side
segment. The reflected assertion handles \(B',D'\).

Finally \(B-B'=(0,2s)\) has both absolute own-axis coordinates equal
to one. Hence \(B,B'\) meet only at the common vertex

\[
p_{BB'}=(b,0).
\]

These are all the prescribed cyclic contacts.

## 3. All nonconsecutive boundary squares are strictly separated

Horizontal separation alone handles \(A\) versus any \(D,D',B,B'\),
since their center differences are respectively \(7/4\) and \(b\),
both strictly greater than the halfwidth sum \(1/2+s\).
It also handles \(E,E'\) versus either \(B,B'\), since

\[
b-e=1/4+3s>1/2+s.
\]

The aligned squares \(E,E'\) are vertically separated by two.
The pairs \(E,D'\) and \(E',D\) are vertically separated because

\[
1+h=5/4+s>1/2+s.
\]

The diagonal squares \(D,D'\) are strictly separated in an own axis:
their center difference has own projection

\[
2sh=1+s/2>1.
\]

For \(D,B'\), the own-axis projection in direction \(-w\) has magnitude

\[
s\bigl((2s-1/4)+(1/4+2s)\bigr)=2>1.
\]

Reflection handles \(D',B\). This list exhausts all nonconsecutive pairs,
so the complete touching graph on these seven boundary squares is
exactly \(C_7\).

## 4. The two inner units are disjoint from every boundary square

The units \(T,U\) meet only at \((3/2,0)\), because the leftmost vertex
of \(U\) is that point and all its other points have larger first
coordinate. The unit \(T\) touches \(A\) along the line \(x=1/2\),
and touches \(E,E'\) along \(y=\pm1/2\), with interiors on opposite
sides in each case.

The line with normal \(v\) supports \(T\) at \((3/2,1/2)\), with
support value \(2s\). The minimum of \(v\cdot x\) on \(D\) is

\[
s(7/4+h)-1/2=s(2+s)-1/2=2s.
\]

The contact point lies on the indicated side of \(D\); in its other
own coordinate its deviation from the center is \((s-1)/2\in(-1/2,1/2)\).
Thus \(D\) touches \(T\) only at that corner. Reflection handles \(D'\).
Horizontal separation handles \(B,B'\) versus \(T\), because their
leftmost first coordinate is \(b-s=3/2+s>3/2\).

The own-axis coordinates of \(D-c_U\), where \(c_U=(3/2+s,0)\), are

\[
v\cdot(D-c_U)=s/2,\qquad w\cdot(D-c_U)=1.
\]

Thus \(D,U\) share a positive side segment, and so do \(D',U\) by
reflection. The square \(B\) is the own-axis translate \(U+v\), and
\(B'\) is \(U-w\), so each shares a side with \(U\). Their common
point \(p_{BB'}\) is the rightmost vertex of \(U\).

Finally \(A,E,E'\) are horizontally separated from \(U\): their
largest first coordinates are \(1/2,e+1/2,e+1/2\), all less than
the smallest first coordinate \(3/2\) of \(U\). Every pair among the
nine units therefore has disjoint open interiors.

## 5. The two units are on the inner side of the actual seven-cycle

Choose the side-interior contact points described above, and use
\(p_{BB'}\) for the vertex contact. The contact-spoke curve through the
seven centers is a Jordan curve: the seven open square interiors are
disjoint, nonconsecutive squares do not touch, and the incoming and
outgoing contacts on each square are distinct.

The seven centers form a strictly convex polygon in the displayed order.
This follows directly by the consecutive edge cross products; their
upper-chain slopes strictly decrease from \(A\) through \(E,D,B\),
and the right edge is vertical. The centers of \(T,U\), namely
\((1,0)\) and \((3/2+s,0)\), lie strictly inside that polygon.

Each center-edge replacement triangle has area at most \(1/4\), as
its two contact spokes have lengths at most \(1/\sqrt2\). Its boundary
avoids the open interiors of \(T,U\): the spokes lie in outer squares,
and the center edges avoid an enclosed unit by the clear-endpoint
short-chord lemma in `C7_CENTER_POLYGON_LOCALIZATION.md`. A connected open
unit cannot lie inside a triangle of area at most \(1/4\), so each
replacement preserves winding about that unit's interior. Therefore the
actual contact-spoke curve has winding one about both inner units.

Alternatively, one can verify the enclosure directly from the upper
contacts and their reflections. The rightmost contact is \((b,0)\),
the two centers lie between the leftmost center and that contact, and
the upper and lower ring arcs stay respectively above and below them.
Boundary contacts of the inner units, including their contact at
\(p_{BB'}\), do not affect the enclosure of their open interiors.

## 6. Boundary-center diameter strictly less than three

The largest squared distance among the seven centers is

\[
|A-B|^2=|A-B'|^2
=(3/2+2s)^2+s^2
=\frac{19}{4}+6s
=\frac{19}{4}+3\sqrt2<9.
\]

The strict comparison is equivalent to \(288<289\).
For transparency, all distinct squared pair-distance expressions,
up to reflection, are listed here:

| Pair | Squared distance |
|---|---|
| \(AE\) | \(49/16-5s/2\) |
| \(AD\) | \(29/8+s/2\) |
| \(AB\) | \(19/4+6s\) |
| \(EE'\) | \(4\) |
| \(ED\) | \(29/16-s/2\) |
| \(ED'\) | \(45/16+7s/2\) |
| \(EB\) | \(97/16-s/2\) |
| \(EB'\) | \(97/16+7s/2\) |
| \(DD'\) | \(9/4+2s\) |
| \(DB\) | \(17/8-s\) |
| \(DB'\) | \(33/8\) |
| \(BB'\) | \(2\) |

Using \(7/10<s<3/4\), every entry other than \(AB\) is strictly
smaller than \(19/4+6s\). For the only close comparison, \(EB'\),
the difference is \(5s/2-21/16>0\). In particular every boundary
edge is shorter than or equal to \(\sqrt2\), as required for the actual
contacts.

## 7. Why this does not refute C7 completion

The acute triangle \(ABB'\) has circumcenter \(O=(x_0,0)\) and
circumradius \(x_0\), where

\[
x_0=\frac{19/4+3\sqrt2}{3+2\sqrt2}>\frac{91}{60}.
\]

The comparison follows from \(12>2\sqrt2\) after clearing the positive
denominator. Thus **no translation** places all seven boundary centers in
a disk of radius \(91/60\). The known center-radius upper bound for
circle-touching units in the C7 radius window is violated independently
of the choice of origin.

At this natural origin \(O\), the lower center annulus fails as well.
Since \(3/2<x_0<8/5\),

\[
|D-O|^2<(1/4)^2+(1/4+s)^2
<\frac1{16}+1<\frac{25}{16}.
\]

Nevertheless all consecutive center angular gaps lie strictly between
forty and seventy-two degrees. For an exact check, set

\[
\arg(E-O)=\pi-\alpha,\quad
\arg(D-O)=\beta,\quad
\arg(B-O)=\gamma.
\]

One has \(40^\circ<\alpha<50^\circ\),
\(75^\circ<\beta<90^\circ\), and
\(20^\circ<\gamma<30^\circ\). Here are elementary exact bounds.
Since \(3/2<x_0<8/5\) and \(1/2<e<11/20\),

\[
\frac{10}{11}<\tan\alpha=\frac1{x_0-e}<\frac{20}{19}.
\]

The increasing triple-angle cubic gives \(\cos40^\circ>3/4\),
and hence \(\tan40^\circ<\sqrt7/3<9/10\). Thus the lower
bound exceeds \(\tan40^\circ\), while the upper bound is smaller
than \(10/9<\cot40^\circ=\tan50^\circ\).
Also \(h>19/20\) and \(0<7/4-x_0<1/4\), so

\[
\tan\beta>19/5>2+\sqrt3=\tan75^\circ.
\]

Finally,

\[
\frac12<\tan\gamma=\frac{s}{b-x_0}
<\frac{s}{2s-1/10}<\frac1{\sqrt3}.
\]

The last comparison uses \((2-\sqrt3)s>1/10\), which follows from
\(\sqrt3<7/4\) and \(s>7/10\). Since
\(\tan20^\circ<\tan22.5^\circ=\sqrt2-1<1/2\), these give the
claimed bounds on \(\gamma\).

The four gap types \(\alpha,\pi-\alpha-\beta,\beta-\gamma,2\gamma\)
therefore all lie in \((40^\circ,72^\circ)\). The angular constraints
alone do not repair the false extraction.

There is also a direct obstruction to putting the actual nine squares
inside the target disk: the vertex \((-1/2,-1/2)\) of \(A\) and the
rightmost vertex \((3/2+3s,s)\) of \(B\) have squared distance

\[
(2+3s)^2+(1/2+s)^2=\frac{37}{4}+13s
>\frac{1105}{64}=4Q.
\]

For example \(s>7/10\) already proves the strict comparison.

The remaining legitimate diameter route must therefore establish its
extraction **with the actual disk/annular hypotheses or positive stress
retained**. The unrestricted enclosing-ring statement is conclusively
unavailable.
