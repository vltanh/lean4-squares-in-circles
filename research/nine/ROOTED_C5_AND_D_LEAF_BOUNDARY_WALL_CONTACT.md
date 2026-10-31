# A common wall separates the two signs of boundary contact

Date: October 26, 2026.

**Status: complete geometric proof, accepted after full-source root and
separate independent reviews in REVIEW_TWO_ARMS_AND_D_WALL_ROOT_2026_10_26.md
and REVIEW_D_LEAF_BOUNDARY_WALL_CONTACT_GLOBAL_2026_10_26.md.**
The theorem below is independent of every force equation and every
selected contact owner. Its final corollary is a whole connected-wall
obstruction for a genuine D leaf. It is not a proof of an arbitrary
D-leaf fan, the remaining rooted C5 families, or an original parent gate.

## 1. Full statement

Let
\[
 2\le R\le\sqrt{1105}/16,\qquad s=1+\sqrt2-R.
\tag{1}
\]
Then \(1/3<s\le\sqrt2-1<9/20\).
Let B,C be closed unit squares contained in the disk D_R, with disjoint
open interiors. Suppose both have rightmost support line x=-s, each
touches the containing circle, and each meets the same closed vertical
segment I of length one on that line, with I contained in -1<=y<=1.
All side contacts and their full application intervals are permitted.

**Theorem.** If B and C physically touch, their physical circle corners
cannot have opposite signs of their y coordinates. In fact each of B,C
has only one such sign, and the signs agree.

The statement is about physical circle corners. A zero coefficient on a
physical corner never removes that corner. No force, degree, load balance,
or mean selection is used.

For use at a genuine D leaf, the segment is the entire left side of its
actual root, not an artificially shortened interval.

## 2. Circle sign fixes the sign of every wall point

A square with a unique rightmost vertex p=(-s,y) has the exact form
\[
 p+[0,1](-a,b)+[0,1](-b,-a),
 \qquad a,b>0,\quad a^2+b^2=1.
\tag{2}
\]
If y>=0, any vertex of negative y coordinate has norm strictly less
than R. For the lower vertex, use
\[
 (s+b)^2+(y-a)^2\le(s+b)^2+a^2
 \le(s+1)^2< R^2.
\]
For the left vertex, if its y coordinate is negative, then a>b and
\[
 (s+a+b)^2+(y+b-a)^2
 \le(s+a+b)^2+(a-b)^2
 \le(s+\sqrt2)^2<R^2.
\]
The upper vertex cannot have negative y coordinate. The wall vertex
cannot be on the circle: it lies on I, which by hypothesis is contained
in \(\{(-s,y):-1\le y\le1\}\), itself strictly inside D_R.
The strict comparisons follow from s<=sqrt2-1 and R>=2:
(s+1)^2<=2<4 and (s+sqrt2)^2<4.
Reflection proves the reverse sign implication. A circle corner cannot
have y=0: every x coordinate is between -s-sqrt2 and -s, so |x|<R.
Consequently a positive circle corner forces y>0, a negative one forces
y<0, and a unique wall vertex cannot support both circle signs.

If the right support is a whole side, the square is axis aligned. Put
\[
 Y=\sqrt{R^2-(s+1)^2},\qquad k=Y-1.
\tag{3}
\]
Here Y>4/3. A physically upper circle corner forces the full vertical
interval [k,k+1], and a lower corner forces [-k-1,-k]. Every wall point
has the indicated strict sign. A square with both signs would require
Y<=1/2, impossible. Thus this case too has exactly one circle sign.

The two forms exhaust all square orientations. Below, opposite signs
are labeled so that every actual B wall point is positive and every
actual C wall point is negative. Since they meet I,
\[
 0<\Delta:=y_B-y_C\le1
\tag{4}
\]
for any chosen wall points when these are unique vertices.

## 3. A side support has a purely geometric contradiction

Suppose B has its whole right side on the wall. Then
\[
 B=[-s-1,-s]\times[k,k+1].
\]
If C is axis aligned, its top is -k<k and the two cannot touch.
Otherwise C has its unique right vertex p_C=(-s,y_C), with y_C<0.

Any separating unit normal n directed from B toward C has n_y<0.
Indeed their ordered wall points force n_y<=0, and a horizontal normal
cannot separate two positive-width squares with the same right support.
If n_x<0, the B application is its lower-left corner (-s-1,k).
The strict unit support-span lemma puts the right support of C strictly
to the left of -s, impossible. If n_x>0, the B application is the
lower-right corner (-s,k); it would equal p_C, contrary to y_C<0.
If n_x=0, C has top support y=k as well as right support x=-s.

Lemma 2.1 of D_LEAF_PARALLEL_LEFT_EXCLUSION.md is a purely geometric
statement covering every orientation of this last square: it lies
strictly inside D_R. Its proof uses only 1/3<s<9/20 and Y>4/3, both
available here, and no force equation. For clarity, its four vertices
are
\[
 (-s,k-u),\ (-s-v,k),\ (-s-u-v,k-v),\ (-s-u,k-u-v),
 \quad u,v\ge0,\quad u^2+v^2=1.
\]
The first two are immediately interior; its displayed deficits give
strict reserves greater than 1/120 and 1/3 for the left and bottom
vertices. Hence C could not touch the circle. Reflection handles a
side support on C. Every endpoint-valued side mean is included.

## 4. Exact vertex contact geometry

Both right supports are now unique vertices. Use the charts
\[
 B=p_B+[0,1](-a,b)+[0,1](-b,-a),
\]
\[
 C=p_C+[0,1](-c,d)+[0,1](-d,-c),
\tag{5}
\]
where all four coefficients are positive and a²+b²=c²+d²=1.
Reflect vertically and exchange the two bodies if necessary so that
b<=c. Set a=cos(theta), b=sin(theta), c=cos(psi), d=sin(psi).

The complete section calculation in Section 4 of
D_LEAF_PARALLEL_LEFT_EXCLUSION.md is geometric and applies here.
At horizontal depth x left of the wall, the lower section of B and
upper section of C are
\[
 \ell_B(x)=\begin{cases}y_B-(a/b)x&x\le b,\\
 y_B-1/a+(b/a)x&x\ge b,\end{cases}
\]
\[
 u_C(x)=\begin{cases}y_C+(d/c)x&x\le c,\\
 y_C+1/d-(c/d)x&x\ge c.\end{cases}
\tag{6}
\]
Their ordered, interior-disjoint sections obey ell_B>=u_C, with equality
somewhere because the squares touch. For b<c, if theta<=psi the minimum
would require Delta=(1-sin(theta-psi))/a>1. Otherwise the minimum is at
x=b and
\[
 \Delta=a+bd/c\le1.
\tag{7}
\]
It follows that psi<=theta/2 and theta+psi<=pi/2. At b=c, one has a=d
and contact gives Delta=2a; equation (7) and the same two inequalities
still hold. Thus the complete closed angular domain is
\[
 0\le\psi\le\min(\theta/2,\pi/2-\theta),
 \qquad 0\le\theta\le\pi/2.
\tag{8}
\]
In particular d<=1/2 and c>=sqrt3/2. Closed endpoints are harmless
comparison endpoints; the actual vertex domain has positive coefficients.

## 5. Both circle corners are the left vertices

The circle-clear wall vertices and the positive signs of y_B,-y_C make
the left C vertex farther than its upper vertex. It is also farther
than its lower vertex because
\[
 1+2cs+2dy_C>1-2d+2cs>0,
\]
where y_C>-1 follows from (4) and y_B>0. Thus C has exactly the circle
corner
\[
 z_C=(-s-c-d,y_C+d-c).
\]
The direct geometric estimate of Section 6 of the same source gives
-y_C>1/4: otherwise
\[
 R^2\le s^2+33/16+\sqrt{8s^2+1/2}
 <753/200<61/16<R^2.
\]
For B the left vertex is farther than its lower vertex. Its only other
possible circle vertex is its upper one. If that upper vertex were on
the circle while y_B<=3/4, then
\[
 R^2\le s^2+25/16+\sqrt{4s^2+9/4}
 <713/200<61/16<R^2.
\]
Otherwise y_B>3/4 and -y_C>1/4 contradict Delta<=1. Therefore B too
has the unique physical circle corner
\[
 z_B=(-s-a-b,y_B+b-a).
\tag{9}
\]
This proof covers the b=c boundary and excludes physical radial masks
by geometry, without assigning a single circle atom by convention.

Write
\[
 Y_B=\sqrt{R^2-(s+a+b)^2}>0,
 \quad Y_C=\sqrt{R^2-(s+c+d)^2}>0.
\]
The actual signs from Section 2 give
y_B=Y_B-b+a and y_C=-Y_C-d+c. Equation (7) consequently requires
\[
 Y_B+Y_C=b+c-d+bd/c.
\tag{10}
\]

## 6. One concavity bound excludes the entire angular domain

For 1<=w<=sqrt2 put
\[
 f(w)=\sqrt{4-(\sqrt2-1+w)^2}.
\]
Because s=1+sqrt2-R and R>=2, direct differentiation of the squared
radicand gives
\[
 \sqrt{R^2-(s+w)^2}\ge f(w).
\tag{11}
\]
The function f is strictly concave. Its two endpoint values exceed the
affine function (57-29w)/20: at w=1 this is sqrt2>7/5; at w=sqrt2
the positive squared difference is
\[
 (4906\sqrt2-6931)/400>0,
 \qquad 2\cdot4906^2-6931^2=98911>0.
\]
Consequently
\[
 f(w)>(57-29w)/20\quad(1\le w\le\sqrt2).
\tag{12}
\]
It remains to bound just one elementary function on (8):
\[
 F=29a+49b+49c+9d+20bd/c.
\]
At fixed theta its psi derivative is
-49d+9c+20b/c². Since psi<=theta/2, b>=2dc, and hence
\[
 c\,\partial_\psi F
 \ge9c^2+d(40-49c)
 \ge9(1-d^2-d)>0.
\]
Here 0<=d<=1/2. Thus the maximum has
psi=min(theta/2,pi/2-theta).

If theta<=pi/3, put d=sin(theta/2). Then
\[
 F=29-18d^2+(98d+49)\sqrt{1-d^2}+9d.
\]
Its derivative is
\[
 (98-196d^2-49d)/\sqrt{1-d^2}+9-36d>0
 \qquad(0\le d\le1/2):
\]
the numerator is at least 49/2 and the last summand is at least -9.
If theta>=pi/3, put a=cos(theta), so 0<=a<=1/2. The boundary value is
\[
 F=58a+98\sqrt{1-a^2},
\]
whose derivative is positive, since 58>98/sqrt3 (10092>9604).
Both branches therefore attain their maximum at theta=pi/3, psi=pi/6:
\[
 F\le29+49\sqrt3<114,
 \qquad85^2-3\cdot49^2=22>0.
\tag{13}
\]
Using (11)--(13),
\[
 Y_B+Y_C-(b+c-d+bd/c)
 >\frac{114-F}{20}
 \ge\frac{85-49\sqrt3}{20}>0.
\]
This contradicts the exact contact equation (10) throughout the entire
continuous domain. There is no parameter subdivision or sign packet.

## 7. Connected wall-neighbor and genuine D-leaf consequences

Let a collection of physical circle-touching units meet the same segment
I as above and each have rightmost support x=-s. Every body has one
circle sign by Section 2. The theorem proves that every physical contact
edge preserves that sign. Thus each connected physical contact component
of the collection has one strict y sign, including every arbitrary
nonnegative split of circle weights with positive total.

Now retain an actual positive component with a genuine D leaf L at A.
Its actual selected root chart is
\[
 A=[-s,1-s]\times[-b,a],\quad a,b>0,\quad a+b=1,
\]
and its leaf resultant is a strictly positive multiple of e_x. Suppose
all other positively circle-loaded bodies lie in one connected graph of
physical circle-touching neighbors of A whose actual A interfaces are
leftward root axes. Those neighbors each have right support x=-s and
meet the unchanged full left side I of A; I lies in -1<y<1.
The conclusion above makes every positive circle atom outside L have
the same strict y sign. Full component force balance is therefore
impossible. The root may have arbitrary degree; all its forces, original
side means, zero individual corner weights, and additional zero-stress
physical contacts are retained.

For a packing of nine squares the accepted same-nine theorem
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md provides R>2, so the corollary
covers the full relevant radius interval of a nine-square proof. It is
not asserted for an isolated smaller core at R<2. In particular it gives
a direct geometric replacement for the nine-square use of the parallel
left D-leaf triangle route, and applies equally to an entire wall-spoke
fan with any number of connected boundary neighbors. It does not assume
that arbitrary oblique root contacts have rightmost support on this wall.

No existing roadmap label is checked by this manuscript alone. The full
remaining D-fan and rooted C5 parent domains retain their oblique and
other original alternatives. No Lean compilation, CI, numerical pose,
or finite computed certificate is used in the proof.
