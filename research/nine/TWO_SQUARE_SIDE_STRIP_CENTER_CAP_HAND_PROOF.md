# Two high centers cannot occupy one actual-four side strip

November 2, 2026. Hand proof. No mathematical program, numerical sampling,
Lean, Lake, or CI is used. The theorem is a two-square statement and does
not assume the existence of a main chain; its strip is the one supplied
by the unrestricted actual-four-chain outsider theorem.

Put

\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 l=\frac{29}{60},\quad u=\frac{13}{12},\quad
 D=u-l=\frac35,\quad \eta=\frac9{16}.
\]

## 1. Statement

**Theorem.** Two physical unit squares with disjoint open interiors in
the closed Q-disk cannot both have centers satisfying

\[
                         l\le x\le u,\qquad y\ge\eta.
 \tag{1}
\]

Both frames are arbitrary. Reflecting either coordinate gives the other
three versions. In particular, among the outsiders of an actual horizontal
four-chain, at most one right-side outsider has center y>=9/16, and at
most one has center y<=-9/16. The left side has the same capacities.

The upper x bound u is essential to this statement. Without it the
quadrant has a simple two-square counterexample; see Section 7.

## 2. Center bounds and the physical separating normal

The universal center bound in the Q-disk is |c|<91/60. For a center with
x>=29/60 it implies |y|<36/25, since

\[
 \left(\frac{29}{60}\right)^2+\left(\frac{36}{25}\right)^2
       -\left(\frac{91}{60}\right)^2=\frac{13}{1875}>0.
 \tag{2}
\]

Label the lower center L and the higher U. If a putative pair satisfies
(1), its gaps obey

\[
 |x_U-x_L|\le\frac35,
 \qquad
 0\le y_U-y_L<\frac{36}{25}-\frac9{16}=\frac{351}{400}<1.
 \tag{3}
\]

Choose a genuine separating unit normal directed from L to U. The sum of
the two support halfwidths on this normal is at least one. Hence (3)
forces its vertical component to be positive, and its horizontal component
to have the sign of x_U-x_L. A zero center gap in either coordinate is
also impossible. Write

\[
 n=(\sigma a,b),\qquad \sigma\in\{-1,1\},\quad
 a>0,\quad b>0,\quad a^2+b^2=1.
 \tag{4}
\]

For a physical square S, let H_S(v) denote its support halfwidth in the
vector direction v. The actual separator says

\[
 n\cdot(c_U-c_L)\ge H_L(n)+H_U(n).
 \tag{5}
\]

We use the exact two-vector support minimum established in
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`:

\[
 |v|\ge|w|\quad\Longrightarrow\quad
 H_S(v)+H_S(w)\ge
 \frac12\left(|v|+
       \frac{|v\cdot w|+|\det(v,w)|}{|v|}\right).
 \tag{6}
\]

Its full hand proof minimizes between side-axis alignment breakpoints;
the smaller candidate aligns the square with the longer vector. Also
H_L(n)>=1/2 and containment gives
\(m\cdot c_U+H_U(m)\le r|m|\) for every vector m.

## 3. A scalar bound valid for every normal

Use m=(0,b). From (5), the width D of the center strip, and y_L>=eta,

\[
 b y_U\ge -Da+b\eta+H_L(n)+H_U(n).
\]

Adding H_U(m) and applying (6), with |n|=1 and |m|=b, gives

\[
 rb\ge1-Da+b\eta+\frac{b(a+b)}2.
\]

Consequently

\[
 r\ge Z(a):=\eta+\frac{a+b}{2}+\frac{1-(3/5)a}{b},
 \qquad b=\sqrt{1-a^2}.
 \tag{7}
\]

Here is a convenient exact lower bound on this scalar function:

\[
                         Z(a)>\frac{49}{24}
                    \qquad(0\le a<1).
 \tag{8}
\]

Differentiate (7):

\[
 Z'(a)=\frac12-\frac{a}{2b}+\frac{a-3/5}{b^3},
\]

\[
 Z''(a)=\frac{\tfrac12+\tfrac52a^2-\tfrac95a}{b^5}
       =\frac{\tfrac52(a-9/25)^2+22/125}{b^5}
       >\frac16.
 \tag{9}
\]

At the rational point a0=5/13, b0=12/13,

\[
 Z(a_0)=\frac{1279}{624},\qquad
 Z'(a_0)=\frac{77}{4320},\qquad 0<Z'(a_0)<\frac1{50}.
 \tag{10}
\]

Integrating (9) and completing the square yields, throughout [0,1),

\[
 Z(a)\ge Z(a_0)+Z'(a_0)(a-a_0)+\frac1{12}(a-a_0)^2
       \ge Z(a_0)-3Z'(a_0)^2
       >\frac{1279}{624}-\frac3{2500}>\frac{49}{24}.
 \tag{11}
\]

For the last comparison, 1279/624-49/24=5/624>3/2500.

## 4. Exclude the two extreme normal ranges

If 0<a<=1/4, (3)--(5) give

\[
 1<\frac35 a+\frac{351}{400}\sqrt{1-a^2}.
 \tag{12}
\]

The expression on the right increases on [0,1/4]. For example, its
derivative is at least
\(3/5-(351/400)/\sqrt{15}>3/5-117/400>0\).
At a=1/4 its value is

\[
 \frac3{20}+\frac{351\sqrt{15}}{1600}
 <\frac3{20}+\frac{351}{1600}\frac{244}{63}
 =\frac{2799}{2800}<1.
 \tag{13}
\]

The radical bound follows from 244^2-15*63^2=1. This contradicts (12).

If a>=3/4, equations (9)--(10) show that Z is strictly increasing there.
At a=3/4, b=sqrt(7)/4, and

\[
 Z(3/4)=\frac{15}{16}+\frac{123}{40\sqrt7}
       >\frac{15}{16}+\frac{369}{320}
       =\frac{669}{320}>\frac{25}{12}>r.
 \tag{14}
\]

Here sqrt(7)<8/3 and 669/320-25/12=7/960. This contradicts (7).
Every putative normal therefore satisfies

\[
                         \frac14<a<\frac34.
 \tag{15}
\]

## 5. Retain the positive horizontal coordinate in the remaining range

Set t=b/4 and m=(t,b). From (15),

\[
 |m|^2=\frac{17}{16}b^2<\frac{255}{256}<1,
 \qquad 0<t<a,
 \qquad b^2-at>0.
 \tag{16}
\]

There are two signs in (4), and both must be retained.

If sigma=1, use x_L>=l and x_U<=u to obtain from (5)

\[
 m\cdot c_U\ge-aD+tu+b\eta+H_L(n)+H_U(n).
\]

The dot product n·m and determinant are positive, with sum
\(b(a+b)+(a-b)t\). Containment and (6) therefore give

\[
 r\sqrt{t^2+b^2}\ge bZ+tB_+,
 \qquad B_+=u+\frac{a-b}{2}.
 \tag{17}
\]

If sigma=-1, use x_L<=u and x_U>=l instead. Then

\[
 m\cdot c_U\ge-aD+tl+b\eta+H_L(n)+H_U(n).
\]

Now n·m=b^2-at>0 and the determinant is negative. The sum of their
absolute values is \(b(a+b)+(b-a)t\). Thus

\[
 r\sqrt{t^2+b^2}\ge bZ+tB_-,
 \qquad B_-=l+\frac{b-a}{2}.
 \tag{18}
\]

Both coefficients have the uniform lower bound

\[
                             B_\pm>\frac7{16}.
 \tag{19}
\]

Indeed B_+>13/12-3/8=17/24. For B_-, (15) gives
b>sqrt(7)/4>79/120, because 7*30^2>79^2. Hence

\[
 B_->\frac{29}{60}+\frac12\left(\frac{79}{120}-\frac34\right)
      =\frac7{16}.
\]

Substitute t=b/4 in (17) or (18), and divide by b>0. Equations
(8) and (19) imply

\[
 r\ge\frac{4Z+B_\pm}{\sqrt{17}}
   >\frac{413}{48\sqrt{17}}.
 \tag{20}
\]

But

\[
 \left(\frac{413}{48\sqrt{17}}\right)^2-Q
 =\frac{170569-169065}{39168}
 =\frac{47}{1224}>0.
 \tag{21}
\]

This is the final contradiction. Both possible center orderings, all
separating normals, and all physical orientations have been treated.

## 6. Application and remaining scope

Every physical outsider of an actual horizontal four-chain has
|x|<13/12. Therefore at most one outsider can simultaneously have
x>=29/60 and y>=9/16. The three coordinate reflections give the other
side and sign capacities.

If three outsiders all have centers above 9/16, at least one must have
|x|<29/60, and no side can contribute two of the three. This does not
itself exclude the triple: the possible middle units and their physical
relations to both inner main squares remain necessary.

In particular, this theorem does not assert the stronger proposed
actual-four-chain terminal that three arbitrary outsiders with center
heights at least 9/16 already force Q. That is a separate geometric
obligation.

## 7. Why the upper strip bound must be retained

Take two unit squares with common 45-degree side axes, centered at

\[
 A=(1/2,13/10),\qquad B=(129/100,9/16).
\]

Both centers have x>=29/60 and y>=9/16. Their signed gap along the
side normal (1,-1)/sqrt(2) is

\[
 \frac{79/100+59/80}{\sqrt2}
 =\frac{611}{400\sqrt2}>1,
\]

so the closed squares are strictly separated. Their farthest corner
norms squared are respectively

\[
 \frac14+\left(\frac{13}{10}+\frac1{\sqrt2}\right)^2
 =\frac{61}{25}+\frac{13}{10}\sqrt2<Q,
\]

\[
 \left(\frac{129}{100}+\frac1{\sqrt2}\right)^2
       +\left(\frac9{16}\right)^2
 =\frac{16641}{10000}+\frac12+\frac{81}{256}
       +\frac{129}{100}\sqrt2<Q.
\]

For both strict upper comparisons one may substitute sqrt(2)<99/70
and multiply the displayed positive denominators. The second x-center
is 129/100>13/12. Thus the unconstrained quadrant version is false,
while the theorem correctly keeps the outsider strip upper bound.
