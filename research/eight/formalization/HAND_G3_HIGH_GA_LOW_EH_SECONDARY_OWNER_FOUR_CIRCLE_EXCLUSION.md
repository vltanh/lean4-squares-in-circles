# A four-circle exclusion for the high-GA, low-EH secondary-owner chain

## 1. Statement and scope

Use the original G0--G2 boundary cycle, with

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 c_0=\sqrt{Q/2}-\tfrac12.
\tag{1}
\]

All decimals in this note are exact rationals. Suppose the four
original states H, G, B and D are outer, with their usual sorted
unsigned coordinates

\[
 a=a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\qquad 0\le b\le c_0.
\tag{2}
\]

Their signed tangents are respectively positive, negative, negative
and negative. A, T and E may have either sign and either radial kind.
Retain actual witnesses with owners

\[
 GA=2,\quad AB=0,\quad BT=2,\quad TD=0,\quad
 DE=2,\quad EH=0,\qquad HG\in\{0,2\}.
\tag{3}
\]

Then this original cycle is impossible.

No frame order or deformation is assumed. The complete G1
total-variation consequence, proved in Section 2 of
HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md, supplies

\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<\frac7{10}.
\tag{4}
\]

The proof below is a fixed positive stress using the four actual
outer circles. The other three states cancel exactly. Its angular
minimizations are on the whole intrinsic two-error hexagon; no mesh,
sampled feasibility claim, or substituted radial state is used.
The conclusion is specifically for (3), not for an unproved
replacement of any other original owner.

Set

\[
 k=\frac{31}{40},\qquad l=\frac{31}{20},\qquad
 L=\frac{21}{20},\qquad h=\frac7{10},\qquad
 W(d)=\frac{1+\cos d+|\sin d|}{2}.
\tag{5}
\]

## 2. Exact force collection

Write the seven errors in cyclic order as

\[
 (v,u,a,x,z,d,r)=(d_{HG},d_{GA},d_{AB},d_{BT},
                         d_{TD},d_{DE},d_{EH}).
\]

Give their actual separating inequalities the respective weights

\[
                  (k,l,l,2,2,1,1).
\tag{6}
\]

The signed transverse coordinates of A, T and E cancel between
their two adjacent inequalities, without a sign assumption.
The four remaining unsigned force vectors are, for HG0,

\[
 \begin{split}
 F_H&=(\cos r,\ k+\sin r),\\
 F_G&=(l\cos u+k\sin v,\ l\sin u+k\cos v),\\
 F_B&=(2\cos x+l\sin a,\ l\cos a+2\sin x),\\
 F_D&=(\cos d+2\sin z,\ 2\cos z+\sin d).
 \end{split}
\tag{7}
\]

For HG2, replace just the first two by

\[
 F_H=(\cos r+k\sin v,\ k\cos v+\sin r),\qquad
 F_G=(l\cos u,\ l\sin u+k).
\tag{8}
\]

For a force vector define the exact sorted outer support

\[
 S(f,g)=\max_{0\le b\le c_0}\{f\,a(b)+g\,b\}.
\tag{9}
\]

A feasible cycle would therefore satisfy

\[
 \mathcal C:=
 kW(v)+lW(u)+lW(a)+2W(x)+2W(z)+W(d)+W(r)
       -S(F_H)-S(F_G)-S(F_B)-S(F_D)\le0.
\tag{10}
\]

The complete shifted circle always gives the upper bound

\[
 S(f,g)\le R\sqrt{f^2+g^2}-\frac{f+g}{2}.
\tag{11}
\]

At zero errors the H, G and B maximizers in (11) have
\(0<b<c_0\); D has its diagonal maximizer. Directly from (7),

\[
 \begin{split}
 \mathcal C_0
 &=\frac{79}{8}
  -\left[
      R\{3\sqrt{1+k^2}+\sqrt{l^2+k^2}\}
      -\frac{1+2k+2l+2}{2}+3c_0
    \right]\\
 &>.0627.
 \end{split}
\tag{12}
\]

The same value applies to HG2. For instance (12) follows from
the strict rational square bounds

\[
 \begin{gathered}
 1.978787<R<1.978788,\quad
 1.4145756<a_0<1.4145757,\quad
 .8992140<c_0<.8992141,\\
 1.2651580<\sqrt{1+k^2}<1.2651581,\quad
 1.7329526<\sqrt{l^2+k^2}<1.7329527.
 \end{gathered}
\tag{13}
\]

We add the charge \(L\) times the sum of the errors to (10).
It vanishes by (4). The remaining sections bound each of the four
charged circle terms relative to its value at zero.

## 3. The two-error full-circle function

For \(p,q>0\), put

\[
 \begin{split}
 \phi(t)&=\cos t+\max(0,\sin t),\\
 A&=p^2+q^2,\qquad B=pq,\qquad
 N(s)=\sqrt{A+2B\sin s},\\
 P_{p,q}(a,b)
 &=p\{\phi(a)-1\}+q\{\phi(b)-1\}
        -R\{N(a+b)-N(0)\}+L(a+b).
 \end{split}
\tag{14}
\]

By (11), this is a lower bound for the change of a charged
two-error circle term with force

\[
                 (q\cos b+p\sin a,\ p\cos a+q\sin b).
\tag{15}
\]

Its domain, by (4), is the closed hexagon

\[
 a_++b_+\le h,\qquad (-a)_++(-b)_+\le h.
\tag{16}
\]

Only the three pairs

\[
                 (p,q)=(k,l),\quad(l,2),\quad(k,1)
\tag{17}
\]

will be used. The second is twice the third in its force
coefficients, but its common linear charge \(L\) is unchanged.

We prove

\[
 \boxed{
 P_{k,l}>-.0576,\qquad
 P_{l,2}>-.0044,\qquad
 P_{k,1}>-.0022
 }\qquad\hbox{on (16).}
\tag{18}
\]

### 3.1 Whole-interval derivative bounds

Write \(C(s)=-RN''(s)\). Differentiation gives

\[
 \begin{split}
 N'''(s)&=-\frac{B\cos s}{N(s)^5}
       \{A^2-3B^2+AB\sin s+B^2\sin^2s\},\\
 C(0)&=\frac{RB^2}{A^{3/2}},\\
 C'(0)&=\frac{RB(A^2-3B^2)}{A^{5/2}}.
 \end{split}
\tag{19}
\]

For all pairs (17), \(2.06<A/B\le2.5\). Since
\(\sin s>-.65\), the brace in (19), divided by \(B^2\), is
at least

\[
                   2.06^2-3-2.06(.65)+(.65)^2=.3271>0.
\]

Here both partial derivatives in \(A/B\) and \(\sin s\) are
positive on the indicated rectangle. Thus \(C\) increases on
\([-h,h]\).

For \(s\ge0\), put \(t=\sin s\). A further differentiation yields

\[
 N''''(s)=\frac{B}{N(s)^7}
 \left[
 B(4A^2-15B^2)+A(A^2-2B^2)t
 +B(10B^2-A^2)t^2+2AB^2t^3+B^3t^4
 \right]>0.
\tag{20}
\]

Every coefficient is positive because \(2\le A/B\le2.5\).
Consequently

\[
 C(s)\le C(0)\quad(-h\le s\le0),\qquad
 C(s)\le C(0)+C'(0)s\quad(0\le s\le h).
\tag{21}
\]

The following bounds are substitutions in the two exact radical
expressions (19), using (13):

\[
 \begin{array}{c|cc}
 (p,q)&C(0)<&C'(0)<\\ \hline
 (k,l)&.549&.714\\
 (k,1)&.587&.360\\
 (l,2)&1.174&.720
 \end{array}
\tag{22}
\]

These are bounds for the distinct fixed force pairs, not angle
subintervals. Also

\[
          \cos h>.7648,\qquad \phi(h)>1.409.
\tag{23}
\]

### 3.2 Reduction to the intrinsic boundary

Fix \(s=a+b\). On every interval on which the signs of a and b
are fixed, \(p\phi(a)+q\phi(s-a)\) is strictly concave.
The norm and linear charge in (14) are constant. A minimum on
that slice is therefore at a zero error or on a boundary with
one error equal to \(h\) or \(-h\).

On a one-error interval with nonnegative error, (21) and the
concave chord

\[
                 \phi(s)\ge1+\frac{.409}{h}s
\]

make the second derivative strictly negative. Indeed, if
\(c_0',c_1'\) denote a row of (22), both endpoints of

\[
                   p-c_0'+\left(\frac{.409p}{h}-c_1'\right)s
\]

are positive. On a one-error interval with negative error, the
second derivative is also negative, since

\[
                            .7648p>c_0'
\tag{24}
\]

for all three rows.

If the positive fixed error is the first one, write
\(a=h,\ b=s-h,\ 0\le s\le h\). The second derivative is
\(-q\cos(h-s)+C(s)<0\): use

\[
        \cos(h-s)\ge .7648+\frac{.2352}{h}s
\]

and note that \(q(.7648)-c_0'>0\) and
\(q-c_0'-hc_1'>0\). If either fixed error equals \(-h\),
the other error is nonnegative and \(s\le0\); its second
derivative is negative by \(C(s)\le C(0)<p\le q\).

There is just one remaining boundary,
\(b=h,\ a=s-h,\ 0\le s\le h\).
The norm \(N\) is concave here. Its tangent at \(s=1/2\)
and the same cosine chord give the global lower bound

\[
 \begin{split}
 P_{p,q}(s-h,h)\ge&
       -.2352p+.409q-K\\
       &+\left(\frac{.2352p}{h}+L-V\right)s,\\
 K&=R\{N(1/2)-N(0)-N'(1/2)/2\},\qquad
 V=RN'(1/2).
 \end{split}
\tag{25}
\]

Direct square comparisons give

\[
 \begin{array}{c|cc}
 (p,q)&K<&V<\\ \hline
 (k,l)&.093&1.024\\
 (k,1)&.087&.880\\
 (l,2)&.174&1.760
 \end{array}
\tag{26}
\]

and the two endpoints of the affine lower bound (25) are
positive in every case. For the smallest margins, the
\((k,1)\) left endpoint exceeds .139, and the \((l,2)\)
right endpoint exceeds .147.

For clarity, (26) needs only the additional norm bounds

\[
 \begin{array}{c|cc}
 (p,q)&N(1/2)>&N(1/2)<\\ \hline
 (k,l)&2.0383681&2.0383682\\
 (k,1)&1.5309260&1.5309261
 \end{array}
\tag{27}
\]

together with the degree-six lower and degree-eight upper cosine
polynomials at \(1/2\). The third row is twice the second.
The squared norm is \(A+2B\sin(1/2)\); the degree-seven lower
and degree-nine upper sine polynomials verify (27).

Every boundary just examined is concave, except (25), which has
an everywhere positive lower bound. Thus a negative minimum
can occur only at one of the six intrinsic hexagon vertices

\[
               (h,0),(0,h),(-h,0),(0,-h),(h,-h),(-h,h).
\tag{28}
\]

### 3.3 The six exact endpoint substitutions

Let \(S_j,C_j\) be the ordinary alternating sine and cosine
polynomials ending at degree j. In addition to (13), the square
comparisons

\[
 \begin{array}{c|cc}
 (p,q)&N(h)<&N(-h)<\\ \hline
 (k,l)&2.1332741&1.2063965\\
 (k,1)&1.6121920&.7759432
 \end{array}
\tag{29}
\]

follow from \(S_9(h)\) and \(S_7(h)\), respectively.
The row for \((l,2)\) is twice the second.

Substitution in (14), with \(C_6(h)\) and \(S_7(h)\)
for every positive trigonometric coefficient, gives the following
strict rational lower bounds at the vertices in order (28):

\[
 \begin{array}{c|rrrrrr}
 (p,q)&(h,0)&(0,h)&(-h,0)&(0,-h)&(h,-h)&(-h,h)\\ \hline
 (k,l)&.259&.576&.124&-.0576&-.0475&.451\\
 (l,2)&-.0044&.179&.836&.730&.163&.453\\
 (k,1)&.365&.457&.050&-.0022&.081&.226
 \end{array}
\tag{30}
\]

For example, the fourth entry of the first row is bounded below by

\[
 l\{C_6(h)-1\}
 +1.978787(1.7329526-1.2063965)-Lh>-.0576.
\]

The first entry of the second row is bounded below by

\[
 l\{C_6(h)+S_7(h)-1\}
 -1.978788(2\cdot1.6121920-2\cdot1.2651580)+Lh>-.0044.
\]

The norm cancels exactly at the last two vertices. These finite
substitutions concern the endpoints proved sufficient above.
They establish (18) on the entire hexagon.

## 4. The actual one-error H and G terms are nonnegative

For a one-error force \((q\cos t,p+q\sin t)\), its charged
change from zero is bounded below by \(P_{p,q}(0,t)\).
Use the full circle for nonnegative t. Sections 3.2--3.3 make
this lower bound concave with nonnegative endpoint values in
both required cases.

For negative t write \(t=-w\).
In the H case \((p,q)=(k,1)\), use the full circle first on
\(0\le w\le.6\). The same concavity and

\[
 \begin{split}
 N(-.6)&<.8517214,\\
 C_6(.6)-1+
 1.978787(1.2651580-.8517214)-.6L&>.0133
 \end{split}
\tag{31}
\]

give a nonnegative change there.

For \(w\ge.6\), the actual sorted support is the endpoint \(b=0\).
Indeed the force ratio satisfies

\[
 \frac{k-\sin w}{\cos w}
 \le\frac{k-\sin(.6)}{\cos(.6)}
 <\frac1{2(a_0+1/2)}.
\tag{32}
\]

The ratio decreases because its derivative is
\((k\sin w-1)/\cos^2w<0\). The final inequality follows
already from \(S_7(.6),C_6(.6)\) and the upper bound for \(a_0\).
The support objective is concave in b, and its derivative at zero
is nonpositive, so this is the exact endpoint support.

The charged H expression on this interval consequently has
derivative, with respect to w,

\[
                  (a_0-\tfrac12)\sin w+\tfrac12\cos w-L<0.
\tag{33}
\]

Its derivative is increasing, since

\[
            (a_0-\tfrac12)\cos w-\tfrac12\sin w>0;
\]

its value in (33) at \(w=h\) is negative. Its minimum is at h.
Using the original full-circle support at zero, that endpoint
change is greater than .0035. Explicitly its lower bound is

\[
 \begin{split}
 &1.978787(1.2651580)-\frac{1+k}{2}-\frac12\\
 &\qquad +(1/2-1.4145757)C_8(h)+\frac12S_7(h)-Lh>.0035.
 \end{split}
\tag{34}
\]

For the G case \((p,q)=(k,l)\), the same proof uses the
intrinsic support transition below .3. On \(0\le w\le.3\),

\[
 \begin{split}
 N(-.3)&<1.5143111,\\
 l\{C_6(.3)-1\}
 +1.978787(1.7329526-1.5143111)-.3L&>.0483.
 \end{split}
\tag{35}
\]

For \(w\ge.3\), the exact support is again \(b=0\), because
\((p/q-\sin(.3))/\cos(.3)<1/[2(a_0+1/2)]\).
The charged derivative now equals

\[
             l\{(a_0-\tfrac12)\sin w+\tfrac12\cos w\}-L.
\]

It is increasing and already positive at .3. Thus this interval's
minimum is at .3, where (35) applies. We have proved

\[
 \boxed{\text{Both required actual one-error circle changes
 are nonnegative on }[-h,h].}
\tag{36}
\]

These endpoint restrictions are essential: a full unrestricted
shifted circle alone would lose a small amount near \(t=-h\).

## 5. The exact sorted D term is minimized at zero

Consider

\[
 T(z,d)=2W(z)+W(d)
 -S(\cos d+2\sin z,\ 2\cos z+\sin d)+L(z+d).
\tag{37}
\]

We prove

\[
                           T(z,d)\ge T(0,0)=3-3c_0
\tag{38}
\]

on the hexagon (16).

The second force is greater than .88, and the first is less
than 2.3. Since \(\sqrt{Q-1/4}>1.9\),

\[
                   .88-\frac{2.3}{3.8}>0.
\]

If the first force is positive, the support objective has positive
derivative at \(b=0\). If it is nonpositive, the objective increases
on the entire sorted arc. Thus the support maximizer is always
either the diagonal or the interior full-circle point; the
\(b=0\) endpoint never occurs.

Where \(d\ge0\), the envelope derivative is

\[
 \partial_d T=L-\{(b-\tfrac12)\cos d-(a-\tfrac12)\sin d\}
                      >L-(c_0-\tfrac12)>.65.
\tag{39}
\]

For \(d=-w<0\), it is

\[
 \partial_d T=L-\{(b+\tfrac12)\cos w+(a-\tfrac12)\sin w\}.
\tag{40}
\]

At the diagonal, the brace is a positive concave trigonometric
function of w; its endpoint values on \([0,h]\) exceed L.

At the full-circle point, put \(s=z-w\). The brace is

\[
 V(s)-\sin w,\qquad
 V(s)=\frac{2R\cos s}{\sqrt{5+4\sin s}}.
\tag{41}
\]

The hexagon implies \(-h\le s\le h\). If \(s\le0\),
then \(V(s)\ge V(0)\). Squaring reduces this to

\[
             -\sin s\{5\sin s+4\}\ge0,
\]

which holds since \(\sin s>-.65\). Moreover
\(V(0)-\sin h>L\).

If \(s\ge0\), then \(w\le h-s\). It remains to show

\[
                        J(s):=V(s)-\sin(h-s)>L.
\tag{42}
\]

This function is strictly concave on \([0,h]\). Here is a
whole-interval verification. For \(N(s)=\sqrt{5+4\sin s}\),
\(V=RN'\), and

\[
 -RN'''(s)=
 \frac{2R\cos s(13+10\sin s+4\sin^2s)}
                     {(5+4\sin s)^{5/2}}.
\]

Use \(R>1.97\), \(\cos s\ge1-s^2/2\),
\(\sin s\ge s-s^3/6\), and
\(\sqrt{5+4s}<2.8\). The exact difference

\[
 \begin{split}
 &\frac{197}{50}(1-s^2/2)(13+10s-5s^3/3)\\
 &\qquad-\frac{14}{5}(5+4s)^2(7/10-s)\\
 &=\frac{111}{50}+31s+\frac{5503}{100}s^2
          +\frac{278}{15}s^3+\frac{197}{60}s^5>0
 \end{split}
\tag{43}
\]

proves \(-RN'''(s)>h-s\ge\sin(h-s)\). Hence \(J''<0\).

Both endpoints of (42) exceed L. The elementary rational bounds

\[
 \sqrt5<2.237,\qquad
 \sqrt{5+4\sin h}<2.754
\]

give, respectively,

\[
       \frac{2(1.978787)}{2.237}-.6443>L,\qquad
       \frac{2(1.978787)(.7648)}{2.754}>L.
\tag{44}
\]

This proves (40) is negative throughout the negative-d interval.
Together with (39), moving d toward zero never increases T.
The derivatives agree at a support transition, so this conclusion
also holds across the diagonal/interior join.

It remains to minimize \(T(z,0)\). For \(z\le0\) its force has
second coordinate greater than the first; the support is diagonal.
The derivative has the same negative sign as the diagonal
case of (40), with an additional factor 2 in the brace.
Thus it decreases toward zero.

For \(z\ge0\) in the diagonal branch,

\[
 \partial_z T=L-2(c_0-\tfrac12)(\cos z-\sin z)>.25.
\tag{45}
\]

In the full-circle branch, its first force exceeds its second:

\[
                       1+2\sin z>2\cos z.
\]

This forces \(\sin z>.4\), since otherwise
\(\cos z>\sqrt{.84}>.9\). Consequently
\(R/\sqrt{5+4\sin z}<.78\), and

\[
 \begin{split}
 \partial_z T
 &=L+2(\cos z-\sin z)
                 -\frac{2R\cos z}{\sqrt{5+4\sin z}}\\
 &>L+2\{.22(.7648)-.6443\}>.09.
 \end{split}
\tag{46}
\]

Therefore zero also minimizes the z interval, proving (38).

## 6. The positive stress reserve

For HG0, group the charge as the G pair \((v,u)\), the B pair
\((a,x)\), the actual one-error H term r, and the actual D
pair \((z,d)\). Equations (18), (36), (38) and (12) yield

\[
 \mathcal C
 >.0627-.0576-.0044
                    =\frac7{10000}>0.
\tag{47}
\]

For HG2, use the H pair \((v,r)\), the B pair, the actual
one-error G term u, and the D pair. The same equations give

\[
                         \mathcal C>.0627-.0022-.0044=.0561>0.
\tag{48}
\]

The linear charges sum to zero in both groupings. Each pair's
hexagon condition is inherited from the actual total variation
(4), and all four circle supports concern their unchanged original
outer states. Equations (47)--(48) contradict (10).

Thus either original HG owner is excluded in the six-owner class
(3). Every strict comparison above follows from the displayed
rational square bounds, ordinary alternating Taylor bounds on a
single whole interval, intrinsic endpoint substitutions justified
by concavity, or the positive-coefficient identity (43).
