# Two whole origin-quadrant witnesses in a three-square cap at offset 17/80

Research continuation, 2026-10-12. This sharpens the \(h\ge13/60\)
whole-quadrant theorem from
[HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md](HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md)
in the already proved eight-square radius window. It keeps every
square frame independent and proves a **whole-square** geometric conclusion.

## Theorem

Suppose eight pairwise interior-disjoint unit squares fit in a
circle of radius
\[
\sqrt2+1/2<R,\qquad R^2\le9789/2500.
\]
Let three of them be contained *as whole squares* in the outward cap
\[
D_R\cap\{x\ge h\},\qquad h\ge17/80.
\]
Then **two distinct** actual cap squares are wholly contained in
the open upper-right and lower-right origin quadrants, respectively:
one lies in \(\{x>0,y>0\}\) and another in \(\{x>0,y<0\}\).

No common frame, physical contact, outer-center condition, or choice
of separating axes is imposed.

## 1. Work at one fixed cap offset

Write \(H=17/80\). Since \(h\ge H\), all three squares lie
in the *larger* cap \(x\ge H\). Thus it is enough to prove the
claim at the fixed offset \(H\). Put
\[
X=(R+H)/2,\quad m=(R-H)/2,\quad
B=\sqrt{R^2-X^2}.
\]
The upper bound \(R<9894/5000\) follows from
\[
(9894/5000)^2-9789/2500=309/6250000>0.
\]
In particular, \(m<1\).
The squared disk-chord identity
\(B^2=(3R^2-2RH-H^2)/4\) increases in \(R\)
and decreases in \(H\ge0\), and gives the exact rational bound
\[
B<164779/100000,                                  \tag{1}
\]
because
\[
(164779/100000)^2-
\frac{3(9894/5000)^2-2(9894/5000)(17/80)-(17/80)^2}{4}
=56833/5000000000>0.
\]

## 2. All three chords have length at least one

Take the vertical section of any one of these squares at \(x=X\).
For its unsigned tilt \(0\le\theta\le\pi/4\), put
\[
c=\cos\theta,\quad s=\sin\theta,\quad
L=c+s\in[1,\sqrt2],\quad cs=(L^2-1)/2.
\]
The square's entire horizontal projection, of width \(L\),
lies in \([H,R]\), so \(x=X\) cuts its open interior and
its vertical chord has length \(\ell\).
On the parallel-side plateau, including the axis-parallel limit,
\(\ell=1/c\ge1\). On either flank,
\[
\ell\ge\frac{L-m}{cs}
=\frac{2(L-m)}{L^2-1}.                            \tag{2}
\]
For \(m<1\), the final rational function decreases as \(L\)
increases (its derivative numerator is
\(-2[(L-m)^2+(1-m^2)]<0\)). Its minimum is therefore at
\(L=\sqrt2\), giving
\[
\ell\ge2\sqrt2-R+H
>2(7071/5000)-9894/5000+17/80
=10621/10000>1.                                    \tag{3}
\]
Here \((7071/5000)^2<2\). Thus **every chord length
\(\ell\ge1\)**. The top/bottom intervals are distinct and
ordered since the square interiors are pairwise disjoint.

## 3. Bound the entire vertical extension of the extreme square

Let \(S_{\rm top}\) be the actual square with the highest
midpoint chord. Let its chord be \((y_0,y_0+\ell)\), its
horizontal and vertical projection width be \(L\), and its
center ordinate be \(p_y\). The two lower disjoint chords
each have length at least one, hence
\[
y_0\ge -B+2.
\]
Since the top chord endpoint is at most the square's maximal
vertical coordinate \(p_y+L/2\), its **entire-square**
minimum ordinate satisfies
\[
\min_{z\in S_{\rm top}}z_y=p_y-L/2
\ge y_0+\ell-L
\ge -B+2+(\ell-L).                               \tag{4}
\]

We now claim the following *tilt-dependent whole-projection reserve*:
\[
\ell-L\ge\sqrt2-R+H.                              \tag{5}
\]

For a sloping chord, (2) implies
\(\ell-L\ge2(L-m)/(L^2-1)-L\), a strictly
decreasing function of \(L\in(1,\sqrt2]\).
Its minimum is at \(L=\sqrt2\), where it equals
\(\sqrt2-R+H\).

For a plateau chord, let \(t=\tan\theta=s/c\in[0,1]\).
Then
\[
\ell-L=1/c-(c+s)
=-\frac{t(1-t)}{\sqrt{1+t^2}}\ge-1/4.
\]
But our lower radius bound gives
\[
\sqrt2-R+H< -1/2+17/80=-23/80<-1/4,
\]
so (5) also holds in the plateau and axis-parallel cases.

Combining (1), (4), and (5) with
\(\sqrt2>7071/5000\), \(R<9894/5000\),
we obtain the **strict positive lower bound**
\[
\min_{z\in S_{\rm top}}z_y
> -164779/100000+2+7071/5000-9894/5000+17/80
=11/100000>0.                                      \tag{6}
\]
Thus the *whole* top square lies in \(y>0\).
Reflecting in the x axis gives that the *whole* bottom
square lies in \(y<0\). Every cap square is wholly in
\(x\ge H>0\), so the two extreme labels supply the
claimed opposite whole origin quadrants. QED.

## Role in the eight-square reduction

The previous \(13/60\) high-offset theorem is now strengthened
to \(17/80<13/60\) in the fully applicable n=8 search interval.
At every triple offset \(\ge17/80\), the three cap members
contain a whole northeast and a whole southeast quadrant
owner. With two perpendicular triples, the respective
positive-quadrant owners must agree because two different
unit squares wholly inside \((0,2)^2\) cannot avoid sharing
\((1,1)\) in their open interiors; this reproduces a
conditional shared-double status, though the independent
[HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md](HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md)
already has the much stronger shared-square threshold \(1/11\).

The significance is the **actual whole-quadrant geometry**, not
an extra purely discrete status rejection. It sharpens the
high-offset positional routing of saturated Type A and
other triple-bearing branches. It does not eliminate the
small-offset continuum, force a contact graph, or establish
the unrestricted bound \(R_8\ge\widehat R\).
