# Exact far-radial domain and a coarse centered-H criterion

**Status: the exact domain and complete lower-B-corner exclusion below
have passed independent full review. The centered-H route in Sections
3--4 remains a working sufficient criterion; its two stronger angle
comparisons are not proved or used as premises. The entire far-radial
family is now excluded by the separate accepted block-pressure theorem
ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md. See
REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md for the complete UUS join.**

Retain the original negative H-owned HA / B-owned upper-left AB chart,
true H4/A2/B2/C2 equations, intact HXY petal, all physical units, original
forces, offsets and means. Use
\[
 q_0=6241/1600\le q\le1105/256,
\quad z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,
\]
\[
 x=a-1,\quad P=(x,b-1),\quad T=(x,b),
\quad f=(s,c),\quad g=(-c,s),\quad c,s>0,
\]
with the notation of ABC_UPPER_LEFT_FAR_RETURN_SUPPORT_WORKING_2026_10_25.md.
BC uses the strict far vertex, with actual normal
\[
 k=-pf+tg,\quad p,t>0,\quad p^2+t^2=1,\quad k_y<0.
\]
Set \(K=\sqrt{q-1/4}\), \(d=K-1\).

## 1. The radial C orientation and full lower-corner exclusion

The compatible fixed-tip selection at unique true B2 makes C own this
strict BC vertex normal. For a radial C, an owned radial-axis side cannot
be its BC feature: the outer side has support K and a unit neighbor would
extend beyond radius R; an inner-side normal cannot meet a physical
boundary neighbor by C7_FORCE_POLYGON.md, Lemma 2.1. That lemma includes
all offsets and both endpoints of the radial inner side, and B is a
physical boundary square. Its local proof does not need a seven-cycle.

Thus BC uses a tangential side of the original radial C. Its unchanged
positive origin moment fixes the radial sign. The full chart is
\[
 C=[-1/2,1/2]k+[-K,-d]Jk,\quad
 W=-\tfrac12 k-MJk,\quad d<M<K.
\tag{1}
\]
Here \(M=\det(W,k)>0\), and the strict C-owned singleton puts W in the
relative interior of its tangential side. No C circle weight is selected.

Suppose B's physical unique circle corner is the lower alternative
\(\epsilon_B=0\). Then its far-vertex geometry gives
\[
 z_B=W+f-g
     =-(\tfrac12+p+t)k-(M+t-p)Jk.
\tag{2}
\]
The original true B concurrence has \(q_B=\kappa_Bz_B\), with
\(0<\kappa_B<1\), and lies on the actual BC normal line through W.
Comparing Jk-components gives
\[
 \kappa_B(M+t-p)=M,
\]
so \(t>p\). Its unchanged circle equation gives
\[
                    K^2-M^2=2+p+t+2M(t-p).
\tag{3}
\]
Since \(M>d>9/10\),
\[
 K^2-M^2>2+p+t+(t-p)=2+2t>2+\sqrt2.
\]
But \(M>K-1\) and \(K<121/60\) give
\[
 K^2-M^2<2K-1<91/30<2+\sqrt2,
\]
a contradiction. Thus the entire \(\epsilon_B=0\) radial far feature
is excluded, without any pressure estimate, C2 equation, HC owner or
restriction of the original radial-C weights.

## 2. Exact beta parametrization of the entire remaining B alternative

The remaining physical unique B corner has \(\epsilon_B=1\). Write
\[
 z_B=\beta f+H_Bg,\qquad H_B=h+1>1/2,
\quad \beta^2+H_B^2=q.
\]
The strict far vertex is
\[
 W=(\beta-1)f+H_Bg.
\]
Equations (1) and \(k=-pf+tg\) give
\[
 (\beta-1)p-H_Bt=1/2,\qquad H_Bp+(\beta-1)t=M.
\tag{4}
\]
Consequently the whole radial far offset/normal chart is
\[
\begin{gathered}
 \frac32<\beta<K,\qquad X=\beta-1,\\
 H_B=\sqrt{q-\beta^2},\qquad
 M=\sqrt{q-2\beta+3/4},\\
 p=\frac{X/2+H_BM}{M^2+1/4},\qquad
 t=\frac{XM-H_B/2}{M^2+1/4},\\
 L=\frac{\beta M}{M+t},\qquad h=H_B-1.
\end{gathered}                                                    \tag{5}
\]
In particular t>0 is exactly \(\beta>3/2\): squaring its positive
comparison has factorization
\[
 M^2X^2-H_B^2/4=(X^2+H_B^2)(X^2-1/4).
\]
Also \(M>d\) is exactly \(\beta<K\), because
\[
 M^2-d^2=2(K-\beta).
\]
The upper offset inequality M<K follows from \(\beta>1/2\).
The value p is positive, and (4) gives \(p^2+t^2=1\).

Proper B concurrence gives the displayed L: its positive transverse
coordinate obeys \(\kappa_B=M/(M+t)\), and \(L=\kappa_B\beta\).
Thus L is the original incoming side coordinate, not a centered choice.
All remaining original A and H data are then fixed by
\[
\begin{gathered}
 a=H_B+\frac{\beta^2-L^2}{2},\qquad b=\sqrt{q-a^2},\quad x=a-1,\\
 c=\frac{Lb-hx}{L^2+h^2},\qquad
 s=\frac{Lx+hb}{L^2+h^2},\\
 \rho=\frac{c}{c+s(a/b-1)},\qquad
 v=\frac1{\sqrt{1+\rho^2}},\quad u=\rho v,\\
 n=(u,v),\quad j=(-v,u),\quad
 H=P+[-1,0]n+[r-1,r]j,\quad0<r<1.
\end{gathered}                                                    \tag{6}
\]
Retain all original inequalities: \(a>b>3/5\), \(c,s>0\), the strict
B-side offset \(0<\beta-L<1\), \(k_y<0\), actual negative A pressure,
and every physical containment and nonoverlap condition. Formula (5)
parametrizes the radial B/C relation; it is not a claim that every point
of that interval satisfies all original A/H geometry.

The equivalent earlier parameters obey the useful exact identity
\[
 K^2=M^2+2Mt+1+p,
\quad \beta=1+p/2+Mt,
\quad H_B=Mp-t/2.
\tag{7}
\]

## 3. A centered-H sufficient criterion with original side parameter

For every original r in (6), write
\[
 c_H=z_A-S_r,\qquad
 S_r=(1,1)+\tfrac12n-(r-\tfrac12)j.
\]
The function \(|S_r|^2\) is convex in r, and its endpoint values are
\[
 |S_0|^2=5/2+2u,\qquad |S_1|^2=5/2+2v.
\]
Since \(u\le v\), actual negative A pressure gives
\[
 |c_H|^2=q+|S_r|^2-2z_A\cdot S_r
          <|S_r|^2-q\le5/2+2v-q.
\tag{8}
\]
No endpoint replacement of the actual H is made.

If \(\rho\ge14/15\), then
\[
 v\le\frac{15}{\sqrt{421}}<\frac{117}{160},
\]
with squared numerator reserve \(117^2\cdot421-2400^2=3069\).
Hence (8) implies
\[
 |c_H|^2<5/2+117/80-q_0=99/1600<1/16,
 \qquad |c_H|<1/4.
\tag{9}
\]

Put \(k_j=k\cdot j\), \(k_n=k\cdot n<0\), and take C's actual outward
radial axis \(e=-Jk\). The exact H halfwidth on that axis is
\[
 h_H(e)=\frac{|k_j|+|k_n|}{2}.
\]
If also \(|k_j|\le2/5\), monotonicity of
\(z+\sqrt{1-z^2}\) on \([0,2/5]\) gives
\[
 h_H(e)\le\frac{2+\sqrt{21}}{10}<\frac{33}{50}.
\]
Together with (9),
\[
 \max_H(e\cdot z)\le |c_H|+h_H(e)
       <\frac14+\frac{33}{50}=\frac{91}{100}<d=\min_C(e\cdot z).
\tag{10}
\]
Thus the two coarse angle bounds would exclude the complete remaining
radial far family, preserving every C weight and without an HC feature
or normal selection.

## 4. Explicit missing whole-domain comparisons

It remains to prove, on the entire original negative-pressure domain
(5)--(6),
\[
                    \rho\ge14/15,\qquad |k_j|\le2/5.
\tag{11}
\]
They are not proved by this note. Numerical diagnostics suggest them,
but no diagnostic pose is a premise or certificate.

One sufficient alternative for the first comparison is to prove both
whole-prefix estimates
\[
 \rho\ge7/8\quad\hbox{on the full radius window},\qquad
 \rho\ge14/15\quad\hbox{when }q\le401/100.
\]
Indeed \(\rho\ge7/8\) gives
\(5/2+2v\le5/2+16/\sqrt{113}<401/100\); by (8), negative A pressure
is then impossible for \(q\ge401/100\). These alternative estimates
are themselves unproved.

No full UUS mask, upper-left owner family, coarse cell or roadmap gate
is closed by this working reduction. No Lean compilation or CI was run.
