# A three-square cap with a downward exceptional separator

November 1, 2026. Hand derivation. No scripts, Lean, or CI.

Complete hand proof. All three scalar rectangle branches are proved below.
The N branch was derived independently by the global-capacity reviewer;
its exact squaring identity and every displayed polynomial coefficient
were then reconstructed independently by the author of this note.
The upward-pointing separating-normal case is a separate obligation.

## 1. The proposed cap and its exact hypotheses

Use the constants of the physical two-square cap theorem:

\[
 Q=\frac{1105}{256},\quad r=\frac{\sqrt{1105}}{16},\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},
 \quad T=\frac{211}{4}.
\]

Let M,A,B be physical unit squares with disjoint open interiors. M and A
lie in the centered disk of radius \(R\le r\). Suppose A is actually
above M in y:

\[
 y_A-y_M\ge h_A+h_M. \tag{1}
\]

Suppose a physical separating normal for A,B points right and downward:

\[
 n=(p,-s),\quad p>0,\quad s\ge0,\quad p^2+s^2=1,
\]
\[
 n\cdot(c_B-c_A)\ge H_A(n)+H_B(n). \tag{2}
\]

Finally suppose the entire square B lies above the horizontal line
\(y=1/8\), in the projection sense

\[
 y_B-h_B\ge\frac18. \tag{3}
\]

**Theorem.** Under these hypotheses,

\[
 a(-x_M-h_M)+b(1-x_B-h_B)\le T. \tag{4}
\]

This replaces the usual matched left top square A by the next
physical square B with a one-unit horizontal correction. It does not
assume that the A--B x-projections separate.

The inequality is strict if \(R<r\), and also if \(s>0\). Thus a
genuine coordinate-exceptional pair A,B gives a strict inequality
throughout the closed \(Q\)-disk domain whenever it has a separator
of the stated right/down form.

## 2. Support reduction to three scalar rectangle bounds

Put \(t=bs/p\ge0\) and multiply (2) by \(b/p\). Combine the
result with k times (1). Use the three support vectors

\[
 v_M=(-a,-k),\qquad v_A=(-b,k+t),\qquad v_B=(0,-t).
\]

Their center terms sum to

\[
 -ax_M-bx_B+k(y_A-y_M)
       +(b/p)n\cdot(c_B-c_A).
\]

Containment bounds the support expressions for M and A by
\(R\sqrt{a^2+k^2}\) and \(R\sqrt{b^2+(k+t)^2}\), respectively.
The floor condition (3) bounds the expression for B by \(-t/8\).
After subtracting the separation support terms, we obtain

\[
 \begin{aligned}
 a(-x_M-h_M)+b(-x_B-h_B)
 \le{}&R\left(\sqrt{a^2+k^2}+\sqrt{b^2+(k+t)^2}\right)
       -\frac t8\\
 &-P_M-P_A-P_B,
 \end{aligned} \tag{5}
\]

where

\[
 P_M=(a+k)h_M+H_M((a,k)),
\]
\[
 P_A=k h_A+H_A((b,-t))+H_A((-b,k+t)),
\]
\[
 P_B=(b+t)h_B+H_B((b,-t)).
\]

For every physical square and nonnegative u,v,

\[
 (u+v)h+H((\pm u,\pm v))\ge u+v. \tag{6}
\]

Indeed the inscribed aligned square of halfwidth \(g=1/(4h)\)
gives \(H\ge(u+v)g\), and \(h+g\ge1\). Thus
\(P_M\ge a+k\) and \(P_B\ge b+t\).

The quantity \(P_A\) is the sum of the two side lengths of the bounding
rectangle of the triangle with vertices \(0,(b,-t),(0,k)\), in A's
physical frame. Its minimum over frames occurs with an edge aligned to
a rectangle axis: between successive changes of a projected extreme
vertex, the sum is a positive expression \(U\cos\theta+V\sin\theta\),
strictly concave and hence without an interior minimum. The three edge
choices give

\[
 E(t)=b+k+t,
\]
\[
 N(t)=L_1+\frac{k(b+t)}{L_1},\qquad L_1=\sqrt{b^2+t^2},
\]
\[
 D(t)=L_2+\frac{bk}{L_2},\qquad L_2=\sqrt{b^2+(k+t)^2}.
\]

Thus \(P_A\ge\min(E,N,D)\). At \(t=0\),
\(L_2(0)=9r\) and

\[
 r\left(\sqrt{a^2+k^2}+9r\right)-(a+b+2k)=T.
\]

Consequently (5) proves the desired cap (4) if, for each
\(m\in\{E,N,D\}\),

\[
 r\left(L_2-9r\right)
 \le m(t)-(b+k)+\frac98t
 \qquad(t\ge0). \tag{7}
\]

If \(R<r\), the reduction is strict because the sum of the two circle
support lengths is positive. Strictness of a scalar branch can also be
retained separately.

## 3. The E branch

The map \(t\mapsto\sqrt{b^2+(k+t)^2}\) has derivative below one.
Thus for \(t>0\),

\[
 r(L_2-9r)<rt<\frac{17}{8}t
 =E(t)-(b+k)+\frac98t,
\]

because \(r<17/8\). At zero both sides vanish. This proves the E
branch, strictly away from zero.

## 4. The D branch

Set

\[
 \mu=\frac{k}{b}=\frac{23}{24},\quad
 z=\frac tb,\quad w=\mu+z,\quad L=\sqrt{1+w^2}.
\]

Since
\(r\sqrt{1+\mu^2}-(1+\mu)=353/384\), the D branch of (7)
is equivalent to

\[
 (r-1)L-\frac\mu L-\frac98(w-\mu)\le\frac{353}{384}.
 \tag{8}
\]

### 4.1. The short interval

If \(\mu\le w\le21/20\), then \(L\le29/20\).
Using \(r<133/64\), the left side of (8) is strictly less than

\[
 \frac{69}{64}\frac{29}{20}
 -\frac{23}{24}\frac{20}{29}
 =\frac{2001}{1280}-\frac{115}{174}
 <\frac{353}{384}.
\]

The last comparison is rational: after subtracting \(353/384\) from
the first fraction, it is
\(2473/3840<115/174\), or \(430302<441600\).

### 4.2. The remaining half-line

For \(w\ge21/20\), use

\[
 L\le w+\frac1{2w}.
\]

Since \((r-1)L-\mu/L\) increases with L, the left side of (8) is
strictly less than

\[
 \frac{69}{64}-\frac{3w}{64}
 +\frac{69}{128w}-\frac{2\mu w}{2w^2+1}.
\]

Its being at most \(353/384\), after multiplication by the positive
denominator \(384w(2w^2+1)\), is exactly

\[
 P(w):=36w^4-122w^3+340w^2-61w-207\ge0. \tag{9}
\]

Now

\[
 P''(w)=432w^2-732w+680>0
\]

for every real w: its discriminant is
\(732^2-4\cdot432\cdot680<0\), and its leading coefficient is
positive. Also \(P'(1)=397>0\), so P increases on \([1,\infty)\).
Finally

\[
 P(21/20)=\frac{253119}{40000}>0.
\]

For a direct integer check, the numerator over 160000 is

\[
 7001316-22596840+59976000-10248000-33120000
 =1012476>0.
\]

This proves (9), hence (8), strictly on the remaining half-line as well.
The D branch is complete for all \(t\ge0\).

## 5. The N scalar branch

It remains to prove

\[
 r\left(\sqrt{b^2+(k+t)^2}-9r\right)
 \le\sqrt{b^2+t^2}+\frac{k(b+t)}{\sqrt{b^2+t^2}}
     -(b+k)+\frac98t,
 \qquad t\ge0. \tag{10}
\]

Normalize

\[
 z=t/b,\quad \mu=23/24,\quad L=\sqrt{1+z^2}.
\]

Then (10) is equivalent to

\[
 r\sqrt{1+(z+\mu)^2}
 \le L+\frac{\mu(1+z)}{L}+\frac98z+\frac{353}{384}.
 \tag{11}
\]

Put

\[
 P=24z^2+23z+47,\quad T_1=432z+353,
 \quad U=576z^2+1104z+1105,
\]
\[
 K=18900z^4+39519z^3+52082z^2+22591z+33182,
\]
\[
 J=20736z^3+36816z^2+56846z+33182.
\]

The right side of (11) is \((16P+T_1L)/(384L)\), a positive
quantity. Squaring the two positive sides of (11) reduces it exactly to

\[
 (16P+T_1L)^2-1105(1+z^2)U
 =16(JL-K)\ge0. \tag{12}
\]

For an explicit coefficient check, \(J=2PT_1\). The coefficients of
\(1105(1+z^2)U-256P^2-T_1^2(1+z^2)\), in descending order, are

\[
 302400,\ 632304,\ 833312,\ 361456,\ 530912,
\]

which are sixteen times the printed coefficients of K. This verifies
(12) by finite integer multiplication.

### 5.1. The interval \(0\le z\le1/2\)

We have

\[
 K-J=z(18900z^3+18783z^2+15266z-34255).
\]

The cubic in parentheses increases on the nonnegative axis. Its value
at \(1/2\) is \(-78255/4<0\). Hence \(K\le J\le JL\), with
strictness when \(z>0\). At zero equality holds.

### 5.2. The interval \(1/2\le z\le2\)

The elementary unit-vector inequality gives \(L\ge(3+4z)/5\).
Direct multiplication gives

\[
 (3+4z)J-5K
 =-11556z^4+11877z^3+77422z^2+190311z-66364.
\]

Since \(z^2\le4\), this is at least

\[
 11877z^3+31198z^2+190311z-66364>0.
\]

Indeed the last two terms alone are at least
\(57583/2>0\) for \(z\ge1/2\). Thus \(JL>K\).

### 5.3. The half-line \(z\ge2\)

Use \(L\ge z\), and put \(w=z-2\ge0\). The exact expansion is

\[
 zJ-K
 =1836w^4+11985w^3+32610w^2+55963w+14808>0.
\]

This proves \(JL>K\). Together, the three ranges prove (11), hence
(10), with equality only at \(t=0\).

All three branches of (7) are now proved. Formula (5) proves the stated
three-square cap. Every scalar branch is strict for \(t>0\), while the
D branch is strict even at zero. If \(t=0\), the separator in (2) is
horizontal, so A,B already have an actual x-projection separation.
This proves the theorem's strictness assertion for a genuine exception.

## 6. A nine-square source for the floor hypothesis

In a canonical three/four/two arrangement, suppose the two bottom squares
L,R form an actual x-two-chain. Suppose the two inner main squares P,Q
are above L,R, respectively, and B is above both P,Q. Then

\[
 y_B-h_B\ge1+\max(y_L+h_L,y_R+h_R).
\]

If both bottom top-edges were at most \(-7/8\), apply circle supports
in directions \((-u,-v)\), \((u,-v)\), with \(u,v\ge0\), and
use the x-separation and (6). Their sum would give

\[
 2R\sqrt{u^2+v^2}\ge2u+\frac{15}{4}v.
\]

Choosing \((u,v)=(2,15/4)\) yields \(R\ge17/8>r\), impossible.
Therefore one bottom top-edge exceeds \(-7/8\), and

\[
 \boxed{y_B-h_B>\frac18.}
\]

Thus the floor in (3) is a consequence of all nine squares in this
arrangement. It is not an additional assumed strip restriction.

## 7. A sharp caller with an actual four-chain and a weak top three-list

Suppose seven physical unit squares have pairwise disjoint open interiors
in the disk. Four form an actual horizontal chain with endpoints M and N.
The other three, A,B,C, have \(B<_xC\), A is actually above M as
in (1), C is actually above N, and B satisfies the floor (3).
If A,B have a physical separating
normal pointing right/down as in (2), apply the proved cap to M,A,B.
Apply the existing physical two-square cap in the opposite x-direction
to N,C. The stated vertical comparison is sufficient; the unrestricted
physical cap in fact needs only their physical nonoverlap. Their sum gives

\[
 \begin{aligned}
 2T\ge{}&a(x_N-x_M-h_M-h_N)\\
        &+b(1+x_C-x_B-h_B-h_C)\\
 \ge{}&2a+b=2T.
 \end{aligned}
\]

For \(q<Q\) this is a contradiction because the cap bounds are strict.
For a genuine coordinate-exceptional A,B, the new left cap is strict
even at \(q=Q\), so the whole closed-Q domain is excluded.

The caller uses the two bottom squares only through the proved floor
condition when Section 6 applies. A separator pointing right/up is not
covered by this theorem; its treatment must retain the corresponding
different sign in the support reduction.
