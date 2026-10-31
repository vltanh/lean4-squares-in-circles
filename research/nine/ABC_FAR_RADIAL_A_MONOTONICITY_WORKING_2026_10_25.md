# Whole-interval monotonicity in the far-radial beta chart

**Status: complete scalar lemma; author, separate independent reviewer and
root full-source reviews passed. All 52 exact coefficients and the complete
inverse identity are independently reconstructed in
ABC_FAR_RADIAL_A_MONOTONICITY_CHECK.py and its companion coefficient JSON.
The accepted full radial-C exit is ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md.**

Use the exact remaining epsilon_B=1 radial far chart in
ABC_UPPER_LEFT_FAR_RADIAL_DOMAIN_WORKING_2026_10_25.md. At fixed
\(q\in[6241/1600,1105/256]\), put
\[
\begin{gathered}
 K=\sqrt{q-1/4},\quad d=K-1,\quad 3/2<\beta<K,\quad X=\beta-1,\\
 H=\sqrt{q-\beta^2},\quad M=\sqrt{q-2\beta+3/4},\quad Z=M+t,\\
 p=\frac{X/2+HM}{M^2+1/4},\quad
 t=\frac{XM-H/2}{M^2+1/4},\quad L=\frac{\beta M}{M+t},\\
 a_q(\beta)=H+\frac{\beta^2-L^2}{2}.
\end{gathered}
\tag{1}
\]
The actual original a is this a_q(beta). All square offsets, mean points,
physical masks and selected forces are unchanged. The following scalar
calculation enlarges the domain only in inequalities.

**Lemma.** The function \(a_q(\beta)\) strictly increases throughout
\(3/2<\beta<K\). Consequently the actual original b obeys
\[
 b^2=q-a_q(\beta)^2>q-a_q(K)^2,
\]
where the continuous endpoint beta=K is used only for comparison, not as
a replacement physical mask or pose.

## 1. Derivative numerator

The exact circle/tangency relations are
\[
 Xp-Ht=1/2,\quad Hp+Xt=M,\quad p^2+t^2=1,
\]
\[
 H=Mp-t/2,\qquad \beta=1+p/2+Mt,\qquad
 K^2=M^2+2Mt+1+p.
\tag{2}
\]
Differentiating at fixed q gives
\[
 H'=-\beta/H,\qquad M'=-1/M,\qquad
 t'=\frac{p(M+t)}{HM}.
\tag{3}
\]
For the last formula differentiate \(Xp-Ht=1/2\), use
\(p'=-tt'/p\), and use \(Hp+Xt=M\) in the denominator.

Direct differentiation of a in (1), using (3), gives
\[
 \frac{HZ^3}{\beta}a'_q(\beta)=\mathcal A(M,t,p),
\]
\[
 \mathcal A=Ht(2M+t)Z+\beta Ht+\beta MpZ-Z^3,
 \quad H=Mp-t/2,\quad\beta=1+p/2+Mt,\quad Z=M+t.
\tag{4}
\]
Every factor cleared from the derivative is positive.

For explicit reconstruction, after using \(p^2=1-t^2\), (4) is
\[
\begin{aligned}
\mathcal A={}&M^3(3tp-1)\\
 &+M^2(1/2+p-3t-3t^2/2+5pt^2)\\
 &+M(t+2pt-3t^2-3t^3+pt^3)\\
 &-t^2/2-pt^2/4-t^3-t^4/2.
\end{aligned}
\tag{5}
\]

## 2. One whole-domain rational rectangle

The actual M>d and (2) imply
\[
 M>M_0:=\frac{1+t}{2p},\qquad d>M_0.
\tag{6}
\]
The first inequality follows from
\(K<M+1\), and the second follows on comparing (2) with
\(K^2=d^2+2d+1\) and using M>d.
Put \(z=t/(1+p)\), so
\[
 p=\frac{1-z^2}{1+z^2},\quad t=\frac{2z}{1+z^2},\quad
 M_0=\frac{1+z}{2(1-z)}.
\]
Since \(d<61/60\), (6) gives
\[
                    0<z<31/91,\qquad t<5/8.
\tag{7}
\]

We also have the strict upper bound
\[
                              M<p+1/2.
\tag{8}
\]
Indeed q increases with M in
\(q=M^2+2Mt+5/4+p\). At \(M=p+1/2\), this value is
\[
 5/2+2p+t+2pt-t^2
 \ge9/2+t(3-3t-2t^2)>9/2,
\]
where \(p\ge1-t^2\) and \(0<t<5/8\) were used. The actual
\(q\le1105/256<9/2\), proving (8).

Thus the entire original domain lies in the single enlarged strip
\(M_0<M<p+1/2\), \(0<z<31/91\). It has the rational parametrization
\[
 M=\frac{(1+z)(1+z^2)+2\lambda(1-2z-z^2)}
           {2(1-z)(1+z^2)},\qquad 0<\lambda<1.
\tag{9}
\]
Here \(1-2z-z^2>0\) on (7). There is no splitting into angle or pose
boxes: (9) is one enlarged interval for M at each z.

## 3. Exact global positivity certificate

Define the polynomial
\[
 G(\lambda,z)=8(1-z)^3(1+z^2)^5
       \mathcal A\left(M(\lambda,z),
             \frac{2z}{1+z^2},\frac{1-z^2}{1+z^2}\right).
\tag{10}
\]
Equations (5), (9) show directly that this is a polynomial of degree
at most 3 in lambda and 12 in z. Let
\[
 \widehat G(\lambda,w)=G(\lambda,(31/91)w)
       =\sum_{r=0}^3\sum_{s=0}^{12}a_{rs}\lambda^r w^s.
\]
Its exact Bernstein coefficients on the whole unit square are
\[
 b_{ij}=\sum_{r\le i,\,s\le j}
       a_{rs}\frac{\binom{i}{r}}{\binom{3}{r}}
              \frac{\binom{j}{s}}{\binom{12}{s}},
 \qquad0\le i\le3,\quad0\le j\le12.
\tag{11}
\]
They give the identity
\[
 \widehat G(\lambda,w)=
 \sum_{i=0}^3\sum_{j=0}^{12}b_{ij}
 \binom3i\lambda^i(1-\lambda)^{3-i}
 \binom{12}j w^j(1-w)^{12-j}.
\tag{12}
\]
For a compact exact sign check, the integer floors of all 52 rational
coefficients from (10)--(11), in order j=0,...,12, are
\[
\begin{array}{c|rrrrrrrrrrrrr}
i&0&1&2&3&4&5&6&7&8&9&10&11&12\\\hline
0&2&2&2&3&3&3&3&3&3&2&2&1&1\\
1&4&4&5&5&5&5&5&5&5&4&3&2&1\\
2&6&6&7&7&8&8&8&8&7&6&5&4&2\\
3&0&3&6&9&10&11&12&12&11&9&8&6&3
\end{array}
\]
The sole zero entry is exactly \(b_{30}=0\). Every other coefficient
is strictly positive. Since the actual \(0<\lambda,w<1\), (12) gives
\(G>0\). Its cleared factor in (10) is positive, so
\(\mathcal A>0\); equation (4) proves \(a'_q(\beta)>0\).

All 52 coefficients and their displayed floors were computed with the
author's standard-Fraction checker, which then reconstructed the full
reverse identity (12). This is an exact polynomial certificate over
the single whole-domain rectangle, not numerical evaluation of sample
poses. A separate complete mathematical/source audit and independent polynomial
reconstruction passed; root also regenerated and matched the saved exact
data. REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md records the join.

## 4. What the lemma does and does not establish

It reduces the whole original b lower-bound problem to the rational
endpoint beta=K. It does not prove the required rho bound, the sign or
size of k dot j, the H/A/B block-pressure sign, or a complete HC return
exclusion. The original radial B tie at beta=K is a comparison boundary
only. No actual mask, multiplier, offset or mean is replaced.

No far-return parent family or roadmap gate is claimed closed, and no
Lean compilation or CI was run.
