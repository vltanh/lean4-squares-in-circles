# An actual loaded intermediate body bounds a diagonal three-edge path

Date: October 26, 2026.

**Status: accepted complete local geometric and force-line theorem after
full independent reviews in
REVIEW_C6_PATH_DIAMETER_EXTENSIONS_CERTIFICATE_REDUCTION_2026_10_26.md
and REVIEW_C6_PATH_DIAMETER_AND_FOUR_LOAD_JOIN_ROOT_2026_10_26.md.**
The force concurrence at the actual
intermediate loaded body is essential. The source does not assert the
same bound for an arbitrary force-free mixed path.

## 1. Original-domain statement

Work in the original radius window
\[
79/40\le R\le\sqrt{1105}/16,\qquad Q=1105/256.
\tag{1}
\]
Let the entire selected positive component be a simple cycle with at
least three positively circle-loaded bodies, and retain the original
compatible point normals and diagonal avoidance. Suppose four
consecutive actual bodies are
\[
A-B-U-C,
\tag{2}
\]
where \(A,B,C\) are loaded and \(U\) is the actual unloaded degree-two
diagonal transmitter. Thus \(B\) has exactly its two original positive
pair forces, at \(A\) and \(U\), and \(B-U-C\) has actual reserve
\(\sqrt2\).

**Theorem.** The unchanged actual endpoint centers satisfy
\[
\boxed{|c_A-c_C|<3.}
\tag{3}
\]

Every physical circle mask, individual nonnegative circle weight,
original support owner and application mean is retained. The theorem
does not use any equation at \(A\), except its actual contact support,
or delete any of the other bodies and forces in the cycle.

The precise local premises used below are: the diagonal channel's true
support equations and common axes at \(B,C\); its positive height and
nonnegative endpoint-center heights; and the true proper nonparallel
two-force concurrence at \(B\). The simple-cycle assumptions supply all
of them through SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md,
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma 1.1, and
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md, Section 5. They are not inferred
from the picture of a mixed path alone.

Put
\[
M=91/60,\qquad m=89/60,\qquad R_0=\sqrt{17}/2.
\tag{4}
\]
Every contained unit has center radius below \(M\). If \(R<R_0\), every
center radius is below \(3/2\), proving (3) directly. Assume henceforth
\[
R\ge R_0,\qquad |c_A-c_C|\ge3.
\tag{5}
\]
Then both endpoint center radii exceed \(m\).

## 2. Exact channel frame and the distant right endpoint

Rotate about the fixed circle origin so the actual diagonal channel
goes horizontally from \(B\) to \(C\), above the origin. Its
applications have common height \(h>0\). The compatible diagonal
convention makes the channel direction an actual side axis of both
endpoint squares, so both \(B,C\) are axis-aligned in this frame.
Their centers can be written
\[
c_C=(x,y),\qquad
c_B=(x-1-\sqrt2,y_B),\qquad
y,y_B\ge0.
\tag{6}
\]
The horizontal gap in (6) is exactly \(\sqrt2+1\); no transverse
mean has been replaced. Since \(|c_B|<M\),
\[
x>1+\sqrt2-M>\frac{53}{60}>0.
\tag{7}
\]
The last comparison uses \(\sqrt2>7/5\).

The actual far circle corner of \(C\) has coordinates
\((x+1/2,y+1/2)\), with either choice on a possible horizontal tie.
Consequently its physical circle equality and \(|c_C|>m\) give
\[
x+y=R^2-\frac12-|c_C|^2
<Q-\frac12-m^2<\frac{13}{8}.
\tag{8}
\]
Here the last reserve is \(511/57600\).

We claim
\[
0\le y<\frac3{20},\qquad x>\frac{22}{15}.
\tag{9}
\]
If \(y\ge3/20\), (7)--(8) put
\[
3/20\le y<89/120,\qquad
|c_C|^2<(13/8-y)^2+y^2.
\]
The quadratic on the right is convex. At both endpoints of that
closed interval it is strictly below \(m^2\), with exact reserves
\[
\begin{aligned}
m^2-\bigl((59/40)^2+(3/20)^2\bigr)&=31/14400,\\
m^2-\bigl((53/60)^2+(89/120)^2\bigr)&=12527/14400.
\end{aligned}
\tag{10}
\]
This contradicts \(|c_C|>m\). Now
\[
x^2>m^2-(3/20)^2>(22/15)^2,
\]
with last squared reserve \(2/75\), proving (9).

Since the actual channel application belongs to the left side of \(C\),
its full unchanged transverse mean satisfies
\[
0<h\le y+\frac12<\frac{13}{20}.
\tag{11}
\]

## 3. A distant opposite endpoint would lie wholly to the left

Write \(c_A=(a_x,a_y)\) and put
\[
K_0=\frac{9-2M^2}{2}=\frac{7919}{3600}.
\]
The assumed distance in (5) gives
\[
-c_A\cdot c_C>K_0.
\tag{12}
\]
If \(a_x\ge0\), its left side is at most \(M(3/20)<K_0\), impossible.
Set \(X=-a_x>0\). If \(X\le11/8\), containment and (9) imply
\[
-c_A\cdot c_C
<M X+\frac3{20}\sqrt{M^2-X^2}.
\tag{13}
\]
The right side increases for \(0\le X\le11/8\). Indeed
\[
\sqrt{M^2-(11/8)^2}>3/5
\]
and its derivative is at least \(M-11/32>0\).
At \(X=11/8\), use
\[
\sqrt{M^2-(11/8)^2}<2/3
\]
to bound (13) by
\[
\frac{11M}{8}+\frac1{10}
=\frac{1049}{480}
=K_0-\frac{103}{7200}.
\tag{14}
\]
This again contradicts (12). The two squared radical reserves used here
are \(143/2880\) and \(167/4800\), respectively.

We have proved
\[
a_x<-\frac{11}{8},\qquad |a_y|<\frac23.
\tag{15}
\]
Every point of the actual unit \(A\) is within horizontal halfwidth
\(1/\sqrt2<17/24\) of its center. Therefore
\[
\boxed{A\subset\{(X,Y):X<-2/3\}.}
\tag{16}
\]
This conclusion uses all of the actual square, not only its center.

## 4. The actual intermediate circle corner and concurrence

Let
\[
a=\frac32+\sqrt2-x,\qquad b=y_B+\frac12.
\tag{17}
\]
The left endpoint \(B\) is axis-aligned, its center first coordinate is
negative, and \(y_B\ge0\). Hence its upper-left corner
\[
z_B=(-a,b)
\]
is an actual circle corner. The bounds \(x<M\) and (9) give
\[
\frac{167}{120}<a<\frac{29}{20}.
\tag{18}
\]
For the first bound use \(\sqrt2>169/120\); for the second use
\(\sqrt2<17/12\). Their squared reserves are \(239/14400\) and
\(1/144\).

The exact circle identity \(a^2+b^2=R^2\), (5), and (18) imply
\[
\frac{29}{20}<b<\frac{31}{20}.
\tag{19}
\]
The two squared reserves are
\[
\frac{17}{4}-2(29/20)^2=\frac9{200},\qquad
(31/20)^2-\bigl(Q-(167/120)^2\bigr)=\frac{263}{11520}.
\]
In particular both coordinates of \(c_B=(-a+1/2,b-1/2)\) are nonzero.
The corner \(z_B\) is therefore physically unique at the circle.
No two-corner weight endpoint has been discarded: the supposed distant
configuration itself has forced this physical mask.

The proper loaded-body theorem supplies the unchanged concurrence
\[
q_B=\tau z_B,\qquad \tau>0.
\]
It lies on the actual horizontal channel force line, so
\[
\tau=\frac hb<\frac{13}{29}.
\tag{20}
\]
The unique circle load is positive. Force balance at \(B\), whose
other actual pair force is horizontal toward \(U\), therefore forces
the outward normal at its actual \(A\)-contact to have strictly
negative vertical component.

We now exhaust that actual support. For the axis-aligned square
\[
B=[-a,1-a]\times[b-1,b]
\]
it is either a mean on the bottom side, the bottom-right vertex, or
the bottom-left vertex. Side-mean endpoints remain in the side-owned
alternative; no new support normal is chosen.

## 5. Every actual bottom-support alternative contradicts (16)

### 5.1. A genuine bottom-side normal

The actual normal is vertical, so its true force line through \(q_B\)
has application first coordinate
\[
P_x=(q_B)_x=-\frac{ha}{b}>-h>-\frac{13}{20}>-\frac23,
\tag{21}
\]
where \(a<b\) follows from (18)--(19). But the same actual application
belongs to \(A\), contrary to (16). This includes every allowed true
bottom-side mean and its closed endpoints.

### 5.2. A strict bottom-right normal

The actual application is \(P=(1-a,b-1)\), with
\[
P_x=1-a>-\frac9{20}>-\frac23.
\]
Again \(P\in A\) contradicts (16).

### 5.3. A strict bottom-left normal

Now \(P=(-a,b-1)\). The outward normal of \(A\) toward \(B\) is a
positive multiple of the actual vector
\[
v=q_B-P
=\bigl((1-\tau)a,\ 1-(1-\tau)b\bigr)
=(v_1,v_2).
\tag{22}
\]
Both coordinates are strictly positive in this strict normal class.
In particular the vector is nonzero, as also follows from (18),(20).
The same formulas give the uniform bounds
\[
v_1>\frac{16}{29}\frac{167}{120}
=\frac{334}{435}>\frac34,\qquad
v_2=1-b+h<\frac15.
\tag{23}
\]
Thus \(v_2/v_1<4/15\).

Containment gives \(-a_x<M\). From (15),(18),(19),
\[
P_x-a_x<M-a<\frac18,\qquad
P_y-a_y<\frac{31}{20}-1+\frac23
=\frac{73}{60}<\frac54.
\tag{24}
\]
All coefficients in (22) are positive. Therefore
\[
\frac{v\cdot(P-c_A)}{v_1}
<\frac18+\frac4{15}\frac54
=\frac{11}{24}<\frac12.
\tag{25}
\]
On the other hand \(P\) is an actual supporting application of \(A\)
in direction \(v\). A unit square has support halfwidth at least
one half in every unit direction, so its homogeneous support obeys
\[
v\cdot(P-c_A)=H_A(v)\ge\frac{|v|}{2}\ge\frac{v_1}{2},
\tag{26}
\]
contradicting (25).

All downward support alternatives are excluded. This contradicts
(5) and proves (3), including the radius endpoint \(R=R_0\).

## 6. Scope and applications

The proof covers the entire diagonal-transmitter family at once.
It uses the actual positive degree two at \(B\), its circle force,
proper concurrence, and the unchanged contact normal. It does not
apply to a body with further positive forces unless the same local
concurrence and downward-support conclusions are proved separately.

No circle equation at \(A\) entered the proof. Accordingly the same
local conclusion holds with a merely contained endpoint \(A\) whenever
all of the explicit local channel, endpoint-height and intermediate
properness premises in Section 1 have independently been supplied.
For the stated simple-cycle use, \(A\)'s original positive circle load
remains present throughout.

In a four-load bare C6 this theorem may be used along either direction
of an actual diagonal channel, at the adjacent true loaded body.
It provides a metric conclusion only. A central-capacity application
still requires a complete pair cover and the original physical
enclosure; exterior completion allocations remain separate.

Every numerical comparison above is a fixed rational inequality.
There is no parameter sample, finite case packet, numerical
optimization premise, Lean compilation or CI step.

