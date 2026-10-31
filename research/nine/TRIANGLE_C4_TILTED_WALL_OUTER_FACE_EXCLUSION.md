# The entire outer-lower-face alternative of the ABC wall is impossible

**Status: complete whole-domain hand exclusion; root and separate
independent full hand and exact polynomial audits passed.**

Use the complete same-normal ABC wall domain of
TRIANGLE_C4_THREE_LOAD_PARALLEL_DOMAIN.md, with the original nine
physical squares and the intact HXY petal. Thus
\[
 \begin{gathered}
 79/40\le R\le\sqrt{1105}/16,\quad q=R^2,\quad
 d=\sqrt{q-1/4}-1<61/60,\\
 1/4<s<1/2,\quad y,w>0,\quad y+w\le1,\quad
 P_A=(-s,y),\quad P_C=(-s,-w).
 \end{gathered}
\tag{1}
\]
The true degrees are H4 and A2/B2/C2/X2/Y2. All three block loads
are positive, A/C have unique physical circle corners, and every
original mean and individual zero B corner weight remains.

Suppose the upper endpoint A is tilted, with its actual inward axes
at P_A given by
\[
 u=(-a,b),\quad v=(-b,-a),\quad
                      0<a\le b,\quad a^2+b^2=1.
\tag{2}
\]
Its unique circle corner is z_A=P_A+u+v.

**Theorem.** The outgoing A-to-B normal cannot be v, including every
actual application on the entire outer-lower side P_A+v+[0,1]u.
The reflected lower-endpoint statement holds as well. No B owner is
prescribed.

## 1. Actual coordinates, support and the full enlarged rectangle

Use the orthonormal (u,v) coordinates about the unchanged circle
origin. Put
\[
             U=1+sa+yb,\qquad V=1+sb-ya.
\]
Then
\[
             z_A=(U,V),\quad P_A=(U-1,V-1),\quad U^2+V^2=q.
\tag{3}
\]
The full wall point bound gives
\[
                        (U-1)^2+(V-1)^2<13/16.
\tag{4}
\]
Here U>1 and V>1-1/sqrt(2)>0.

If the outgoing normal is v, the actual minimum v-support of B is V.
Any contained unit with positive minimum support V has a corner
whose squared norm is at least (V+1)^2+1/4: its center norm is
at least V+1/2, and the full center/farthest-corner inequality is
\(|c|^2+|c|+1/2\). Hence V<=d.

Put \(q_0=(79/40)^2=6241/1600\). Also d>91/100, since
\[
                    q_0-1/4-(191/100)^2=101/40000>0.
\]
Thus
\[
 U^2=q-V^2\ge q-d^2=2d+5/4>307/100>49/16.
\]
Equation(4) gives U<2. If V<=2/3, it gives
\[
 U<1+\sqrt{13/16-1/9}=1+\sqrt{101}/12<37/20.
\]
Consequently
\[
 q=U^2+V^2<(37/20)^2+4/9=13921/3600<6241/1600,
\]
whose final positive gap is 97/2880. This is impossible.
The complete physical domain therefore lies in
\[
                  7/4<U<2,\qquad2/3<V<61/60.
\tag{5}
\]

## 2. Proper concurrence retains the original outer-side application

The actual endpoint A has boundary neighbor B and nonparallel pair
normals. Its true unique-corner proper concurrence is
\[
                         q_A=\kappa z_A=P_A-\lambda e_x,
                         \qquad\kappa>0,\quad\lambda\ge0.
\]
At the outer v face, the other proper line fixes the unchanged
actual AB application as
\[
                                  T=(\kappa U,V).
\tag{6}
\]
This is an identity for its original mean; no endpoint is selected.

Put tau=a/b in (0,1]. Comparing the two own coordinates gives
\[
            \kappa=1-\frac{1-\tau}{U-\tau V},
            \qquad U-\tau V>0.
\tag{7}
\]
Since
\[
            s=b[\tau(U-1)+V-1]>1/4,\qquad b\le1,
\]
we have
\[
                      \tau>\tau_0:=\frac{5/4-V}{U-1}>0.
\tag{8}
\]
The right side of(7) strictly increases with tau because U>V.
Define
\[
 \begin{split}
 D&=U^2+V^2-U-5V/4,\\
 N&=D-U-V+9/4=U^2+V^2-2U-9V/4+9/4.
 \end{split}
\tag{9}
\]
On the whole rectangle(5),
\[
 \begin{split}
 D&=(U-1/2)^2+(V-5/8)^2-41/64>59/64,\\
 N&=(U-1)^2+(V-9/8)^2-1/64>35/64.
 \end{split}
\tag{10}
\]
Equations(7)--(10) give
\[
                   \kappa>N/D>0,\qquad
              \kappa U-(U-1)=\frac{\tau(U-V)}{U-\tau V}>0.
\tag{11}
\]
The equality a=b and zero proper-length limits remain covered.

## 3. A complete support-point corner bound

If a unit square K has its minimum second coordinate h>0 at an
actual point T=(X,h), X>0, then some corner has squared norm at least
\[
                         X^2+h^2+1+2\min(X,h).
\tag{12}
\]
For a lower-side application, T+(0,1) belongs to K, so its squared
norm already gives(12); the maximum of the squared norm on K occurs
at a corner. For a lower vertex, choose its inward side axis
(c,e) with c,e>=0 and c^2+e^2=1. The adjacent corner has squared
norm
\[
                  X^2+h^2+1+2(Xc+he)
                     \ge X^2+h^2+1+2\min(X,h),
\]
because c+e>=1. This includes all aligned endpoint limits.
These two support-feature cases exhaust all original side means
and vertex applications.

Apply(12) to the unchanged T in(6), with X=kappa U and h=V.
If X<=V, the lower bound is
\((X+1)^2+V^2>U^2+V^2=q\), by(11), contradicting containment.
If X>=V, it is \(X^2+(V+1)^2\). By(11), it exceeds q whenever
\[
                    G:=U^2N^2-(U^2-2V-1)D^2>0.
\tag{13}
\]
No sign of U^2-2V-1 is required to infer this implication.

## 4. Exact positive polynomial on the entire rectangle

Put
\[
                     x=2-U\in[0,1/4],\qquad
                     z=1-V\in[-1/60,1/3].
\]
Direct expansion of(9),(13) gives the exact identity
\[
 16G=f(x)+zA(x)+z^2B(x)+z^3C(x)+96z^4-32z^5,
\tag{14}
\]
where
\[
 \begin{split}
 f(x)&=15+44x-265x^2+360x^3-184x^4+32x^5,\\
 A(x)&=-24+58x^2-24x^3,\\
 B(x)&=151-176x-16x^2+32x^3,\\
 C(x)&=-74+64x-32x^2.
 \end{split}
\tag{15}
\]
All 18 shifted monomials were independently reconstructed in exact
integer polynomial arithmetic.

For 0<=x<=1/4, f'''(x)=2160-4416x+1920x^2>=1056>0.
Since f''(1/4)=-118, f is concave on the entire interval, and
\[
                    f(x)\ge\min(f(0),f(1/4))=115/8.
\tag{16}
\]
The other exact whole-interval bounds are
\[
                  -24\le A<0,\qquad B\ge106>0,\qquad-74\le C<0.
\tag{17}
\]
When z<=0, every nonconstant z term in(14) is nonnegative, so 16G>0.
When 0<=z<=1/3, discard the nonnegative even-power terms and use
\[
                  16G\ge115/8-8-74/27-32/243
                              =6809/1944>0.
\tag{18}
\]
This proves(13) over the complete enlarged rectangle.
Both cases in Section 3 contradict actual B containment.

## 5. Scope

The result excludes the entire outgoing outer-lower-face alternative
and its reflection, including every full AB mean and both side
endpoints. Only the actual endpoint uses its true degree-two force
and torque. All B masks, true H/petal forces and all three extras
remain. The full wall assembly must still cover the remaining lower-
vertex normal and its opposite endpoint. No missing edge, canonical
motion, numerical angle cover, Lean compilation or CI is used.
