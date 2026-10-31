# Three whole-domain monotonicities for the mixed-01 C6 gap

Date: October 26, 2026.

**Status: complete analytic lemmas, accepted after independent saved-source
and physical-scope review.** See
`REVIEW_C6_MIXED_01_GAP_MONOTONICITIES_C6_2026_10_26.md` and
`REVIEW_C6_MIXED_01_COMPLETE_JOIN_ROOT_2026_10_26.md`.
These lemmas apply to the original mixed corner pattern 110
with genuine outgoing shares at loaded units 0 and 1. They retain the
entire force and angle domains needed by the closure reduction in
SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md. No optimizer, interval grid,
coefficient certificate, or numerical premise is used.

The lemmas below reduce the final scalar exclusion to its tradeoff
boundary. They do not by themselves prove the required boundary
inequality or close an original roadmap gate. All physical squares,
forces, means, masks, transmitter positions and extra squares retain
the exact scope of the cited closure source. No Lean compilation or
CI was run.

## 1. Original scalar data and a Cauchy lower gap

Use the exact normalization and notation of the closure source:

\[
 K=\frac{79}{40},\qquad r=\frac1{\sqrt2},\qquad
 p=\mu_1/\mu_0>0,\quad q=\mu_2/\mu_0>0,
\]
\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\quad
 \sum_i\alpha_i=\pi/2,\quad
 c_i=\sin\alpha_i,\quad s_i=\cos\alpha_i,
 \quad t_i=s_i-c_i,\quad h_i=s_i+c_i.
\tag{1}
\]

All scalar estimates may use the closed angular enlargement.
The original positive denominator and numerator are

\[
 D_0=\sqrt{q^2+1+2qc_0},\quad
 D_1=\sqrt{1+p^2+2pc_1},\quad
 D_2=\sqrt{p^2+q^2+2pqc_2},
\]
\[
 N=2+2p+q+qh_0+h_1+\sqrt{p^2+2q^2+2pqh_2},
 \qquad R\sum_iD_i=N.
\tag{2}
\]

Define

\[
 w=1+\sqrt2+h_0,\qquad v=\sqrt{4K^2-w^2},
\]
\[
 U_0=\frac{wc_0+vs_0}{2},\qquad
 U_2=\frac{wc_2+vs_2}{2},
\]
\[
             G=KD_1-3p-2-h_1+U_0+pU_2.
\tag{3}
\]

Here \(2+\sqrt2\le w\le1+2\sqrt2<2K\), so \(v>0\).
Since \(h_2\le\sqrt2\),

\[
 \sqrt{p^2+2q^2+2pqh_2}\le p+\sqrt2q,
 \qquad N\le2+3p+h_1+wq.
\]

Apply the triangle inequality to
\((q+c_0,s_0)\) and \((q+pc_2,ps_2)\), and then Cauchy with
the vector \((w,v)\), whose norm is \(2K\). This gives

\[
 \begin{split}
 K(D_0+D_2)
 &\ge K\sqrt{(2q+c_0+pc_2)^2+(s_0+ps_2)^2}\\
 &\ge wq+\frac12[w(c_0+pc_2)+v(s_0+ps_2)].
 \end{split}
\]

Consequently, for every original positive \(q\),

\[
                         K\sum_iD_i-N\ge G.
\tag{4}
\]

No optimizing value of \(q\) has been selected. The Cauchy step is
pointwise over the whole original force range.

## 2. Useful consequences already forced by actual closure

The cited closure source proves

\[
 p>1+r,\qquad c_0+c_1\le1,\qquad
 h_1>L(c_0):=(1+r)\sqrt{1-c_0^2}-rc_0.
\tag{5}
\]

It also implies

\[
                            c_0>\frac3{10}.
\tag{6}
\]

Indeed \(L\) is decreasing and \(h_1\le\sqrt2\). At \(c=3/10\),
the inequality \(L(c)>\sqrt2=2r\) is equivalent, after moving
positive terms and squaring, to

\[
 91(1+r)^2-529r^2=182r-128>0.
\]

Using \(r>7071/10000\), the last expression exceeds
\(3461/5000>0\). Thus (5) excludes \(c_0\le3/10\).

The angular condition \(c_0+c_1\le1\) also gives a useful strict
bound on the third angle:

\[
                              c_2>\frac7{15}.
\tag{7}
\]

For a fixed sum \(S=\alpha_0+\alpha_1\in[\pi/4,\pi/2]\),
concavity of sine shows that the minimum of
\(\sin\alpha_0+\sin\alpha_1\), with each angle at most \(\pi/4\),
occurs at one of the two endpoints. Its value is

\[
 r+\sin(S-\pi/4)=r(1+s_2-c_2).
\]

Therefore (5) implies \(s_2-c_2\le\sqrt2-1\). If
\(c_2\le7/15\), monotonicity of \(\sqrt{1-c^2}-c\) instead gives

\[
 s_2-c_2\ge\frac{4\sqrt{11}-7}{15}
       >\frac5{12}>\frac{29}{70}>\sqrt2-1,
\]

a contradiction. Here \(\sqrt{11}>53/16\) has squared reserve
\(7/256\); \(5/12-29/70=1/420\); and \(\sqrt2<99/70\).
This proves (7) on the entire domain in (5).

## 3. The gap strictly decreases with theta_0 for every p >= 3/2

Fix \(\theta_1,p\), with \(\theta_2=2\pi-\theta_0-\theta_1\).
In this section only the original closed angular interval and
\(p\ge3/2\) are assumed; the other restrictions in (5) are not
needed.

Abbreviate \(a=c_0,\ b=s_0,\ A=b-a=t_0\). Then \(A\in[0,1]\).
Direct differentiation of (3) gives

\[
 \frac{\partial G}{\partial\theta_0}
             =\frac{U-pV}{2v},
\]
\[
 U=(v-A)(wb-va),\qquad
 V=(v+A)(ws_2-vc_2)>0.
\tag{8}
\]

The following two bounds hold on the complete angular interval:

\[
                  v<2,\qquad \frac{w+v}{w-v}<4.
\tag{9}
\]

For the first, use \(w\ge2+\sqrt2>2+140/99\). The positive
rational reserve is

\[
 4-\left[4K^2-(2+140/99)^2\right]
                            =\frac{211159}{3920400}>0.
\]

For the second, \(w>17/5\), and

\[
 (17/5)^2-\frac{50}{17}K^2
                            =\frac{1191}{13600}>0.
\]

This implies \(25v^2<9w^2\), hence \(5v<3w\), exactly the
second inequality in (9). In particular \(w>v>0\).

If \(U\le0\), (8) is already negative. Otherwise \(v>A\), and
\(s_2\ge r,\ c_2\le r\) give

\[
 \begin{split}
 \frac UV
 &\le\frac{v-A}{v+A}\,
       \frac{wb-va}{r(w-v)}\\
 &=\frac{v-A}{v+A}\,
       \frac{h_0+[(w+v)/(w-v)]A}{\sqrt2}\\
 &\le\frac{2-A}{2+A}(1+2\sqrt2 A)
 <\frac32.
 \end{split}
\tag{10}
\]

The penultimate inequality uses (9), \(h_0\le\sqrt2\), and
the increasing dependence of \((v-A)/(v+A)\) on \(v\).
The last inequality is equivalent to

\[
                  1+(5/2-4\sqrt2)A+2\sqrt2 A^2>0.
\tag{11}
\]

Its leading coefficient is positive, and its discriminant is
\(153/4-28\sqrt2<153/4-28(7/5)=-19/20<0\).
Thus it is positive for every real \(A\). This proves the whole-angle
strict monotonicity

\[
       \boxed{\quad \partial_{\theta_0}G<0
                    \quad\hbox{whenever }p\ge3/2.\quad}
\tag{12}
\]

## 4. The gap strictly increases with p under the necessary angle bound

Assume \(c_0+c_1\le1\) and \(p\ge1+r\). First we prove

\[
                              U_2>\frac{13}{10}.
\tag{13}
\]

By (7) and the original angular upper bound,
\(7/15<c_2\le r<3/4\). Also

\[
 \frac{17}{5}<w<\frac{23}{6}.
\]

The upper bound follows from
\(w\le1+2\sqrt2<134/35<23/6\), with the last difference
\(1/210\). For \(e\in[7/15,3/4]\), the function

\[
 \mathcal U(w,e)=
       \frac12\left[we+\sqrt{4K^2-w^2}\sqrt{1-e^2}\right]
\]

is concave separately in \(w\) and \(e\). It is therefore bounded
below by the smallest of its four rectangle-corner values. The
following rational estimates prove all four are greater than \(13/10\).

At \(w=17/5\), the corresponding \(v>2\), since
\(4K^2-(17/5)^2-4=17/400>0\). For every \(e\) in the
interval, \(\sqrt{1-e^2}\ge\sqrt7/4>13/20\), so

\[
 \mathcal U(17/5,e)>
       \frac12\left[\frac{17}{5}\frac7{15}
                              +2\frac{13}{20}\right]
       =\frac{433}{300}>\frac{13}{10}.
\]

At \(w=23/6\), the corresponding \(v>19/20\), with squared
reserve
\(4K^2-(23/6)^2-(19/20)^2=1/180>0\).
At the two \(e\)-endpoints use
\(\sqrt{1-(7/15)^2}=4\sqrt{11}/15>22/25\) and
\(\sqrt{1-(3/4)^2}=\sqrt7/4>13/20\). Thus

\[
 \mathcal U(23/6,7/15)>
    \frac12\left[\frac{23}{6}\frac7{15}
                       +\frac{19}{20}\frac{22}{25}\right]
    =\frac{2953}{2250}>\frac{13}{10},
\]
\[
 \mathcal U(23/6,3/4)>
    \frac12\left[\frac{23}{6}\frac34
                       +\frac{19}{20}\frac{13}{20}\right]
    =\frac{1397}{800}>\frac{13}{10}.
\]

This proves (13) on the entire rectangle enlargement, hence on the
original necessary domain.

For fixed angles, differentiation gives

\[
 \frac{\partial G}{\partial p}
                  =K\frac{p+c_1}{D_1}-3+U_2.
\]

The ratio \((p+c)/\sqrt{p^2+2pc+1}\) increases with \(c\ge0\).
Also \(p\ge1+r>17/10\), and
\(K^2-[(17/10)^2+1]=17/1600>0\). Hence

\[
 K\frac{p+c_1}{D_1}
 \ge K\frac p{\sqrt{p^2+1}}>\frac{17}{10}.
\]

Together with (13) this proves

\[
 \boxed{\quad \partial_pG>0
       \quad\hbox{for }p\ge1+r,\ c_0+c_1\le1.\quad}
\tag{14}
\]

## 5. The gap strictly decreases with theta_1 when c_0 > 3/10

Fix \(\theta_0,p\), and put
\[
                         J_2=ws_2-vc_2.
\]

For \(c_0>3/10\), sine plus cosine is increasing in
\(\alpha_0\in[0,\pi/4]\). Using \(\sqrt{91}>953/100\),

\[
 w>1+\frac{140}{99}+\frac{1253}{1000}
                         >\frac{11}{3}.
\tag{15}
\]

The final rational reserve is \(47/99000\). It follows that
\[
 v^2<4K^2-(11/3)^2=\frac{7769}{3600}<\frac94,
\]
so \(v<3/2\). Consequently

\[
 J_2\ge r(w-v)>
              \frac7{10}\left(\frac{11}{3}-\frac32\right)
              =\frac{91}{60}>\frac32.
\tag{16}
\]

Direct differentiation, with
\(\theta_2=2\pi-\theta_0-\theta_1\), gives exactly

\[
 \frac{\partial G}{\partial\theta_1}
                   =Kp\frac{s_1}{D_1}-t_1-\frac p2J_2.
\tag{17}
\]

For \(p\in[1+r,9/4]\), we have
\[
 K^2<\frac52+\sqrt2\le p^2+1.
\]
The first strict comparison has rational reserve
\[
 \frac52+\frac{140}{99}-K^2
                         =\frac{2141}{158400}>0.
\]
Since \(D_1\ge\sqrt{p^2+1}\), the first two terms of (17)
are therefore less than
\[
 (p-1)s_1+c_1\le\sqrt{(p-1)^2+1}<\frac{3p}{4}.
\]

The last inequality holds throughout \([3/2,9/4]\), which contains
the interval in question: the concave quadratic
\[
 \frac9{16}p^2-[(p-1)^2+1]
                   =-\frac7{16}p^2+2p-2
\]
has positive endpoint values \(1/64\) and \(73/256\).

For \(p\ge9/4\), instead use \(D_1\ge p\) to bound the first
two terms of (17) by
\[
 (K-1)s_1+c_1
 \le\sqrt{(K-1)^2+1}
 <\frac75<\frac{27}{16}\le\frac{3p}{4}.
\]

The strict squared reserve in the middle is
\((7/5)^2-(K-1)^2-1=3/320>0\).
Thus both elementary force ranges give the same uniform upper bound.
Inserting (16) into (17) proves

\[
 \boxed{\quad \partial_{\theta_1}G<0
       \quad\hbox{for }p\ge1+r,\ c_0>3/10.\quad}
\tag{18}
\]

## 6. Exact consequence and the separate boundary proof

For the full original mixed-01 orbit, actual closure supplies every
premise used in (12), (14), and (18). The force normalization and the
Cauchy lower bound (4) are unchanged from the original physical
identity. These lemmas prove genuine whole-domain monotonicities,
including all shared-mean endpoints allowed by closure.

They do not justify increasing both independent angles past the
necessary condition \(c_0+c_1\le1\). Their combined use reduces
the relevant relaxed minima to that tradeoff boundary or to a fixed
additional upper bound on \(c_0\). The required directional proof along
\(c_0+c_1=1\) is now supplied by
`SIX_CYCLE_MIXED_01_BOUNDARY_MONOTONICITY.md`, independently
reviewed in
`REVIEW_C6_MIXED_01_BOUNDARY_MONOTONICITY_C6_2026_10_26.md`.
The exact endpoint evaluations and full physical join are assembled
in `SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md`. No directional
boundary inequality is inferred merely from the two coordinate
monotonicities.
