# A radius-three-halves cover of boundary centers gives one strict piercing point

**Status: complete hand geometric implication; two independent hand audits passed for Sections 1--5, and a separate independent audit passed for Section 6.** Suppose finitely many interior-disjoint unit squares form the boundary of a bounded complementary region, and all their centers lie in an open disk of radius \(3/2\), centered at p. Every further unit square lying in that bounded region contains p in its strict interior. In particular, at most one interior-disjoint unit square can occupy the region. Section 6 adds the elementary minimum-disk reduction used to state the remaining C7 obligation exactly.

All square orientations are independent. No stress, regularity, or common frame is assumed. Applied to C7, this is a sufficient completion criterion. It is not yet known here that every admissible C7 has such a center cover. Diameter less than three alone does not imply the required covering-radius bound.

Write \(H_U(n)\) for the support halfwidth of a unit square U in a unit direction n, and put \(\sigma=1/\sqrt2\).

## 1. The radial-tail statement

**Lemma 1.1.** Let T be a unit square for which \(0\notin\operatorname{int}T\). Let its center be c. If an interior-disjoint unit square S meets the outward radial tail

\[
                  \{c+s c/|c|:s>0\},
 \tag{1}
\]

then its center C satisfies \(|C|\ge3/2\).

The center c is nonzero under the hypothesis. Rotate and reflect so

\[
 c=(r,0),\qquad r>0,
 \qquad 0\le\theta\le\frac\pi4,
 \qquad u=\cos\theta,\quad v=\sin\theta,
\]

and T has orthogonal frame vectors \((u,-v)\), \((v,u)\). The hypothesis is exactly

\[
                         r\ge\frac1{2u}.
 \tag{2}
\]

Take any separating unit normal n, directed from T toward S. A point \((r+s,0)\in S\) from (1) gives

\[
 (r+s)n_x\ge rn_x+H_T(n),
\]

so \(n_x>0\). Write

\[
n=(a,\varepsilon b),\qquad a>0,\quad b\ge0,\quad
 a^2+b^2=1,\quad\varepsilon\in\{+1,-1\}.
 \tag{3}
\]

Put

\[
 F=ra+H_T(n).
\]

Separation gives

\[
                     n\cdot C\ge F+H_S(n).
 \tag{4}
\]

We first bound F, retaining both signs in (3).

## 2. The inner square's full support

Since a>0, F increases with r. It suffices to set \(r=1/(2u)\) while proving the following lower bounds.

### 2.1. Shallow normal: a>=b

Parameterize n by its signed angle \(\varphi\in[-\pi/4,\pi/4]\). Between consecutive alignments with T's frame, F is a linear combination of \(\cos\varphi\) and \(\sin\varphi\), is positive, and satisfies \(F''=-F<0\). Its minimum therefore occurs at an interval endpoint or at the sole frame-alignment angle \(\varphi=-\theta\) in this range.

At \(\varphi=-\theta\),

\[
 F=\frac12+\frac12=1.
\]

At either endpoint \(\varphi=\pm\pi/4\), direct substitution gives

\[
 F=\frac{1/u+2u}{2\sqrt2}\ge1,
\]

by \(1/u+2u\ge2\sqrt2\). Consequently

\[
                           F\ge1\qquad(a\ge b).
 \tag{5}
\]

As \(H_S(n)\ge1/2\), equations (4)--(5) immediately imply \(|C|\ge3/2\). This completes the shallow case.

### 2.2. Steep normal: a<=b

Here b>0. Let \(F_+(\theta)\) and \(F_-(\theta)\) be the expressions with the two signs of n, always at \(r=1/(2u)\). The halfwidth formula gives

\[
 H_T(n)=\frac{|ua-\varepsilon vb|+|va+\varepsilon ub|}{2}.
 \tag{6}
\]

Put \(\theta_* =\arctan(a/b)\in[0,\pi/4]\). For \(\theta\le\theta_*\), subtraction gives

\[
 F_--F_+=v(b-a)\ge0;
\]

for \(\theta\ge\theta_*\), it gives

\[
 F_--F_+=a(u-v)\ge0.
\]

It therefore suffices to minimize \(F_+\). Before \(\theta_*\),

\[
 F_+(\theta)
 =\frac{a\sec\theta+(a+b)\cos\theta+(a-b)\sin\theta}{2}.
 \tag{7}
\]

Writing \(t=\tan\theta\in[0,1]\), the sign of its derivative is the sign of

\[
             a(1+t^3)-b(1+t)\le0,
\]

since a<=b and \(t^3\le t\). After \(\theta_*\),

\[
 F_+(\theta)
 =\frac{a\sec\theta+(b-a)\cos\theta+(b+a)\sin\theta}{2}.
 \tag{8}
\]

Its derivative is positive: \(\cos\theta\ge\sin\theta\), and

\[
 (b+a)\cos\theta-(b-a)\sin\theta\ge2a\cos\theta>0.
\]

Thus the minimum is attained at \(\theta_*\). There \((u,v)=(b,a)\) and \(H_T(n)=1/2\), proving

\[
                 \boxed{F\ge\frac12\left(1+\frac ab\right)}
                 \qquad(a\le b).
 \tag{9}
\]

The bound holds for either separator sign and for every r satisfying (2).

## 3. A support identity for the outer square

For a unit square S and \(n=(a,b)\) in the first quadrant, put

\[
 h=H_S(e_x)=H_S(e_y),\qquad \frac12\le h\le\sigma.
\]

Then

\[
                  H_S(n)+(a-b)h\ge a^2.
 \tag{10}
\]

To verify it, represent S's frame angle by \(\phi\in[0,\pi/2]\), and put \(\beta=\arctan(b/a)\). For \(\phi\le\beta\), the left side of (10) is \(a\cos\phi\ge a^2\). For \(\phi\ge\beta\), it is

\[
                    (a-b)\cos\phi+a\sin\phi.
\]

If a>=b this is concave, with endpoint values \(a^2\) and a. If a<b its derivative is positive, so its minimum is again \(a^2\). Reflection proves the identical inequality for the reflected square and the other sign of n.

## 4. The steep separator forces the outer center outside radius three-halves

Continue with a<=b. Reflect the second coordinate if needed and write \(C=(X,Y)\) in the resulting frame, so the separator is \((a,b)\). The radial-tail intersection implies

\[
 |Y|\le h:=H_S(e_y)=H_S(e_x)\le\sigma.
 \tag{11}
\]

Put \(K=F+H_S(n)\). By (9) and \(H_S(n)\ge1/2\),

\[
 bK\ge b+\frac a2>\sigma\ge h.
 \tag{12}
\]

Among points satisfying \(aX+bY\ge K\) and \(|Y|\le h\), the minimum squared norm occurs at

\[
 Y=h,\qquad X=\frac{K-bh}{a}.
 \tag{13}
\]

Indeed K-bY is positive on the strip. Substituting its smallest allowed X gives a quadratic in Y whose derivative is \(2(Y-bK)/a^2<0\) on \([-h,h]\), by (12).

Equations (9)--(10) give

\[
\begin{aligned}
 \frac{K-bh}{a}
 &=\frac Fa+\frac{H_S(n)-bh}{a}\\
 &\ge \frac1{2a}+\frac1{2b}+a-h
 =:L(a)-h,
\end{aligned}
 \tag{14}
\]

where

\[
                 L(a)=a+\frac1{2a}+\frac1{2\sqrt{1-a^2}},
                 \qquad 0<a\le\sigma.
 \tag{15}
\]

Here is a short uniform estimate, without an interval table:

\[
                       L(a)>\frac{51}{25}
                            >\sigma+\frac{\sqrt7}{2}.
 \tag{16}
\]

For the first inequality,

\[
 L''(a)=\frac1{a^3}+\frac1{2(1-a^2)^{3/2}}
                 +\frac{3a^2}{2(1-a^2)^{5/2}}>2.
\]

At \(a_0=3/5\),

\[
 L(a_0)=\frac{247}{120},
 \qquad L'(a_0)=\frac{227}{1152}<\frac15.
\]

The quadratic lower bound from \(L''>2\), followed by completing the square, yields

\[
 L(a)\ge L(a_0)+L'(a_0)(a-a_0)+(a-a_0)^2
 \ge L(a_0)-\frac{L'(a_0)^2}{4}
 >\frac{247}{120}-\frac1{100}
 =\frac{1229}{600}>\frac{51}{25}.
\]

For the second inequality in (16), use

\[
 \sigma<\frac{71}{100},
 \qquad \frac{\sqrt7}{2}<\frac{133}{100},
\]

both verified by squaring.

The function \((L-h)^2+h^2\) decreases for \(1/2\le h\le\sigma\), since \(L>2\sigma\). Combining (13)--(16),

\[
\begin{aligned}
 |C|^2
 &\ge (L-h)^2+h^2\\
 &\ge (L-\sigma)^2+\sigma^2\\
 &>\frac74+\frac12=\frac94.
\end{aligned}
\]

This completes the steep case, and proves Lemma 1.1 in all orientations and for arbitrary physical separating normals. In particular, no separator ownership was assumed. \(\square\)

## 5. The strict common-point conclusion

Translate the proposed covering-disk center p to the origin, so every boundary-square center has norm strictly less than \(3/2\). Let T be a unit square enclosed by the ring and interior-disjoint from all its boundary squares.

If \(0\notin\operatorname{int}T\), follow the outward radial ray from T's center. Since T lies in a bounded complementary region, this ray eventually meets a boundary square S. Lemma 1.1 says that S's center has norm at least \(3/2\), contradicting the strict center cover.

Therefore

\[
                         p\in\operatorname{int}T
\]

for every enclosed unit square T. Two such squares cannot be interior-disjoint, because their interiors would both contain p. This is the claimed capacity-one criterion. \(\square\)

## 6. Exact remaining use in C7

The audited theorem `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md` proves that every physical boundary C7 in the declared window has center diameter less than three. It does not prove that those centers have covering radius less than three-halves; the latter is stronger in the plane.

A complete proof of that covering-radius bound would combine with this manuscript and `C7_COMPLETION_LOCALIZATION.md` to exclude two completion squares. The remaining geometric obstruction has the following exact form.

Let D be a minimum enclosing closed disk of the seven centers, with center p and radius rho. Such a disk exists by compactness. The center p belongs to the convex hull of the centers lying on its boundary: otherwise a strict separating direction moves p slightly toward all those boundary centers, and the finite strict slack of every other center then gives a smaller enclosing disk. In the plane, p lies in the convex hull of at most three of those boundary centers. This last finite-dimensional assertion follows directly by eliminating an affine dependence from any convex combination with more than three terms until a coefficient vanishes.

One supporting center gives rho=0. If two suffice, they are antipodal about p and their distance is 2rho. The proved center-diameter bound therefore gives rho<3/2. If neither case applies, three supporting centers form a triangle whose interior contains p. Its circumcenter is p, so the triangle is acute. Consequently, a failure of the desired cover requires an **acute triangle of ring centers with circumradius at least3/2**.

List the three positive cyclic graph gaps between those centers. They sum to7, and, up to cyclic permutation and reversal, have one of the four forms

\[
                 (1,1,5),\quad(1,2,4),\quad(1,3,3),\quad(2,2,3).
\]

The first form is already excluded. Two of its triangle sides join touching unit squares and have lengths at most sqrt(2): the shared contact point is at distance at most1/sqrt(2) from either center. Acuteness and the cosine rule give the third side length less than2. Thus every side has length at most2. The largest triangle angle is between pi/3 and pi/2, so the sine rule bounds the circumradius by 2/sqrt(3)<3/2.

The other three gap forms remain open in this manuscript. This reduction has no stress or common-frame premise and does not assert that diameter less than3 gives covering radius less than3/2. Until the acute supporting-triple obstruction is excluded, the general C7 completion assertion remains open.
