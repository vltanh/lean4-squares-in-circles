# An analytic tradeoff-boundary inequality for the final mixed two-share C6 orbit

Date: October 26, 2026.

**Status: complete analytic lemma, accepted after independent saved-source
and physical-scope review.** See
`REVIEW_C6_MIXED_01_BOUNDARY_MONOTONICITY_C6_2026_10_26.md`.
The lemma supplies the directional monotonicity that is not
implied by the two coordinate monotonicities. It applies to the entire
necessary mixed-01 boundary, with no force upper bound or sampled sign
premise. Three elementary ranges are used to prove inequalities by
concavity and fixed radical comparisons; there is no coefficient packet
or interval-evaluation certificate.

The original physical scope, all nine squares, actual shared means,
strict turns, positive forces, and the Cauchy lower gap are those of
SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md,
SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md, and
SIX_CYCLE_MIXED_01_CAUCHY_AND_ENDPOINTS.md. This source alone does
not tick an original roadmap gate.

## 1. Statement and exact derivative

Put
\[
 K=\frac{79}{40},\qquad r=\frac1{\sqrt2},\qquad P=1+r,
 \qquad \frac3{10}\le a\le r,\qquad b=1-a,
\]
\[
 s=\sqrt{1-a^2},\quad t=\sqrt{1-b^2},\quad T=s-a,\quad
 w=1+\sqrt2+a+s,\quad v=\sqrt{4K^2-w^2},
\]
\[
 e=st-ab,\quad f=sb+at,\quad
 D=\sqrt{1+p^2+2pb},\quad
 U_0=\frac{wa+vs}{2},\quad U_2=\frac{we+vf}{2}.
\tag{1}
\]
In particular \(T\ge0\), \(b<r\), \(t>b\), and \(v>0\).
For the original Cauchy gap restricted to this boundary,
\[
 \mathcal G(p,a)=KD-2-b-t-3p+U_0+pU_2,
\tag{2}
\]
we prove
\[
 \boxed{\qquad \partial_a\mathcal G(p,a)<0
       \quad\hbox{for every }p\ge P,\quad 3/10\le a\le r.\qquad}
\tag{3}
\]
Endpoint derivatives mean the derivative of the same smooth formulas
on a neighborhood of the stated interval.

Direct differentiation gives
\[
 U_0'=\frac{(v-T)(ws-va)}{2sv},\qquad
 U_2'=-B H,
\]
\[
 B=\frac{wf-ve}{2s},\qquad
 H=\frac{t-s}{t}+\frac{T}{v},
\]
\[
 \partial_a\mathcal G
       =1-\frac bt-\frac{Kp}{D}+U_0'-pBH.
\tag{4}
\]
All these identities include the derivative of \(w\) and \(v\);
neither is held constant on the tradeoff boundary.

We will prove, at \(p=P\),
\[
                U_0'<\frac{KP}{D},
       \qquad PBH>1-\frac bt.
\tag{5}
\]
These two strict inequalities imply (3) at \(P\). They also show
\(B,H>0\). Since
\[
 \frac{\partial}{\partial p}\frac pD=\frac{1+pb}{D^3}>0,
\]
equation (4) is strictly decreasing in \(p\). Thus the proof at \(P\)
implies (3) for the whole unbounded force range.

## 2. The first derivative contribution is smaller than the force term

First, \(w\) is increasing in \(a\), because \(w'=T/s\ge0\).
At \(a=3/10\), use \(\sqrt2>141/100\) and
\(s=\sqrt{91}/10>19/20\) to obtain \(w>183/50\).
Consequently
\[
 v<\frac32,\qquad
 \frac94-\left[\frac{6241}{400}
                         -\left(\frac{183}{50}\right)^2\right]
                            =\frac{431}{10000}>0.
\tag{6}
\]

An exact subtraction in (4) gives
\[
 U_0'-\frac{w-v}{2}
                  =\frac{T}{2sv}\left(v^2+av-ws\right).
\tag{7}
\]
We claim the parenthesized expression is negative. By (6),
\[
 ws-av-v^2>
       w(w+s)-\frac32a-4K^2=:\Phi(a).
\]
Writing \(k=1+\sqrt2\), direct differentiation yields
\[
              \Phi''(a)=-2-\frac{6a}{s}
                                  -\frac{3(k+a)}{s^3}<0.
\]
The concave function \(\Phi\) is bounded below by the smaller of its
endpoint values. At \(a=3/10\), the bounds \(w>73/20\) and
\(w+s>23/5\) give
\[
 \Phi(3/10)>
   \frac{73}{20}\frac{23}{5}-\frac9{20}-\frac{6241}{400}
       =\frac{59}{80}>0.
\]
At \(a=r\),
\[
 \Phi(r)=11+\frac{15}{4}\sqrt2-\frac{6241}{400}
          >\frac{259}{400}>0,
\]
using \(\sqrt2>7/5\). Therefore (7) proves
\[
                         U_0'\le\frac{w-v}{2}.
\tag{8}
\]

We compare this bound with \(KP/D\), always with \(p=P\).
For fixed \(P\), the latter decreases with \(b\).

### 2.1. The range \(3/10\le a\le1/2\)

Here
\[
 w\le\frac32+\sqrt2+\frac{\sqrt3}{2}<\frac{121}{32},
       \qquad v>\frac98.
\]
For the bound on \(w\), use \(\sqrt2<99/70\) and
\(\sqrt3<97/56\); the remaining rational difference is \(1/1120\).
The positive squared reserve for \(v>9/8\) is \(999/25600\).
Thus
\[
 U_0'<\frac{85}{64}<\frac43.
\]
Since \(b\le r\),
\[
 K^2P^2-\frac{16}{9}(1+P^2+2Pr)
       =-\frac{10693}{28800}+\frac{4969}{14400}\sqrt2
       >\frac{1789}{16000}>0.
\]
This proves \(KP/D>4/3>U_0'\).

### 2.2. The range \(1/2\le a\le3/5\)

Now \(b\le1/2\), and
\[
 w\le\frac{12}{5}+\sqrt2<\frac{191}{50},
       \qquad v>1.
\]
The squared reserve for the latter is \(101/10000\). Hence
\[
 U_0'<\frac{141}{100}<\sqrt2.
\]
The comparison at \(b=1/2\) is
\[
 K^2P^2-2(1+P^2+P)
       =-\frac{3677}{3200}+\frac{1441}{1600}\sqrt2
       >\frac{1789}{16000}>0.
\]
It follows that \(KP/D>\sqrt2>U_0'\).

### 2.3. The range \(3/5\le a\le r\)

Here \(b\le2/5\), and
\[
 w\le1+2\sqrt2<\frac{23}{6},\qquad v>\frac{19}{20}.
\]
The positive squared reserve in the second bound, using \(w<23/6\),
is \(1/180\). Thus
\[
 U_0'<\frac{173}{120}<\frac{29}{20}.
\]
At \(b=2/5\),
\[
 K^2P^2-\frac{841}{400}
                       \left(1+P^2+\frac45P\right)
       =-\frac{17397}{16000}+\frac{7657}{8000}\sqrt2
       >\frac{20213}{80000}>0.
\]
Therefore \(KP/D>29/20>U_0'\). This completes the first
inequality in (5) on the full interval.

## 3. Two lower bounds for the positive angular factor \(B\)

Let \(A=\arcsin a\), \(C=\arcsin b\), and define
\(\gamma\in(0,\pi/2)\) by
\[
 \cos\gamma=\frac{w}{2K},\qquad \sin\gamma=\frac{v}{2K}.
\]
Because \(a+b=1\), convexity of arcsine gives \(A+C\ge\pi/3\).
Both \(a,b\le r\), and they are not both \(r\), so \(A+C<\pi/2\).
Also \(e=\cos(A+C)\), \(f=\sin(A+C)\), and hence
\[
                         B=\frac K{s}\sin(A+C-\gamma).
\tag{9}
\]

On the whole interval, \(\gamma<\pi/8\). Indeed
\(\cos(\pi/8)<37/40\), proved from
\(\cos^2(\pi/8)=(2+\sqrt2)/4\), \(\sqrt2<99/70\), and the
positive reserve \(23/11200\). On the other hand,
\[
 w>\frac{183}{50}>
                  \frac{79}{20}\frac{37}{40};
\]
the last difference is \(1/160\). Therefore
\[
 \sin(A+C-\gamma)>\sin(5\pi/24),\qquad
 \sin^2(5\pi/24)=\frac{4-\sqrt6+\sqrt2}{8}
                  >\frac{59}{160}>
                              \left(\frac{95}{158}\right)^2.
\]
Use \(\sqrt6<49/20\), \(\sqrt2>7/5\) for the first strict
bound; the last rational reserve is \(7219/998560\).
Since \(s\le1\), equation (9) proves
\[
                         B>\frac{19}{16}.
\tag{10}
\]

For \(a\ge3/5\), a stronger bound is available. Here \(s\le4/5\),
\(w\ge12/5+\sqrt2>19/5\), and \(v<11/10\). Consequently
\[
 \cos\gamma>\frac{76}{79},\quad
 \sin\gamma<\frac{22}{79},\quad
 \sin(A+C)\ge\frac{\sqrt3}{2}>\frac67,\quad
 \cos(A+C)\le\frac12.
\]
All terms have their displayed positive signs. Thus
\[
 \sin(A+C-\gamma)>
                \frac67\frac{76}{79}-\frac12\frac{22}{79}
                   =\frac{379}{553},
\]
\[
                      B>\frac{379}{224}>\frac53.
\tag{11}
\]
The last difference is \(17/672>0\).

## 4. Concavity proves the required lower bounds for \(H\)

We prove
\[
 H>\frac12\left(1-\frac bt\right)
                  \quad(3/10\le a\le3/5),
\tag{12}
\]
\[
 H>\frac38\left(1-\frac bt\right)
                  \quad(3/10\le a\le r).
\tag{13}
\]
These are analytic inequalities on whole intervals. The endpoints
below are used through concavity, not through interpolation of
numerically evaluated signs.

For constants \(0<\lambda,m<1\), define
\[
 F_{\lambda,m}(a)
       =(1-\lambda)t-s+\lambda b+mt(s-a).
\tag{14}
\]
If \(1/v\ge m\), then
\[
 t\left[H-\lambda\left(1-\frac bt\right)\right]
                                    \ge F_{\lambda,m}(a).
\tag{15}
\]
Its exact second derivative is
\[
 F_{\lambda,m}''=
 -\frac{(1-\lambda)+m(s-a)}{t^3}
 +\frac{1-mt}{s^3}
 -2m\frac bt\left(1+\frac as\right).
\tag{16}
\]
Globally \(1/v>2/3\) by (6). For \(a\ge1/2\), also
\(1/v>5/6\): monotonicity of \(w\), together with
\(\sqrt2>141/100\) and \(\sqrt3/2>43/50\), gives
\[
 w>\frac{377}{100},\qquad
 \frac{36}{25}-\left[\frac{6241}{400}
                         -\left(\frac{377}{100}\right)^2\right]
                           =\frac{63}{1250}>0.
\tag{17}
\]

### 4.1. Half of \(1-b/t\) on \(3/10\le a\le1/2\)

Take \((\lambda,m)=(1/2,2/3)\). Here
\[
 s>\frac67,\quad \frac7{10}<t<\frac78,\quad s-a>\frac13.
\]
The magnitude of the first negative term of (16) exceeds
\((13/18)(512/343)\), while the positive term is less than
\((8/15)(343/216)\). Their difference is
\(32111/138915>0\); the last term in (16) is negative.
Thus \(F_{1/2,2/3}\) is strictly concave.

At \(a=3/10\), use \(t>7/10\), \(s<24/25\), and \(b=7/10\).
Expression (14) increases with \(t\) and decreases with \(s\)
on these ranges, so
\[
 F_{1/2,2/3}(3/10)>
  \frac7{10}\left[\frac12+\frac23
                \left(\frac{24}{25}-\frac3{10}\right)\right]
             -\frac{24}{25}+\frac7{20}
        =\frac6{125}>0.
\]
At \(a=1/2\),
\[
 F_{1/2,2/3}(1/2)=\frac34-\frac{5\sqrt3}{12}
                       >\frac1{48}>0,
\]
using \(\sqrt3<7/4\). Concavity and (15) prove (12) on
this interval.

### 4.2. Half of \(1-b/t\) on \(1/2\le a\le3/5\)

Use \((\lambda,m)=(1/2,5/6)\), justified by (17).
Here \(s\ge4/5\), \(t>6/7\), \(s-a\ge1/5\), and \(t<1\).
The magnitude of the first negative term of (16) exceeds \(2/3\);
the positive term is less than \(125/224\). Their difference is
\(73/672>0\), so this function is also strictly concave.
Its endpoint values satisfy
\[
 F_{1/2,5/6}(1/2)=\frac78-\frac{11\sqrt3}{24}
                        >\frac7{96}>0,
\]
\[
 F_{1/2,5/6}(3/5)=\frac23\frac{\sqrt{21}}5-\frac35
                       >\frac1{150}>0.
\]
For the latter use \(\sqrt{21}/5>91/100\), a direct positive
square comparison. This proves the rest of (12).

### 4.3. Three eighths of \(1-b/t\) on the entire interval

Take \((\lambda,m)=(3/8,2/3)\). For \(a\le1/2\), the
concavity argument in Section 4.1 becomes stronger, since the
first negative numerator has increased.
For \(a\ge1/2\), use
\[
 s\ge r>\frac{70}{99},\quad t>\frac67,\quad
 b\ge1-r>\frac27,\quad \frac as>\frac47.
\]
In (16) the positive term is less than \(2910897/2401000\).
The first and last negative terms have total magnitude greater than
\(5/8+88/147\). The exact difference is
\[
 \frac58+\frac{88}{147}-\frac{2910897}{2401000}
                         =\frac{10148}{900375}>0.
\]
Thus \(F_{3/8,2/3}\) is strictly concave throughout the interval.

At \(a=3/10\), it exceeds \(F_{1/2,2/3}(3/10)>0\), because
their difference is \((t-b)/8>0\). At \(a=r\), where \(s=a=r\),
\[
 F_{3/8,2/3}(r)=\frac{5t+3-11r}{8}>0.
\]
To prove the final sign, both \(5t\) and \(11r-3\) are positive,
and
\[
 (5t)^2-(11r-3)^2=116r-82>0
\]
because \(r>70/99>41/58\), with
\(70/99-41/58=1/5742\). Concavity and (15) now prove (13).

## 5. Completion of the directional inequality

For \(a\le3/5\), combine (10), (12), and \(P>17/10\):
\[
 PBH>
 \frac{17}{10}\frac{19}{16}\frac12
                    \left(1-\frac bt\right)
       =\frac{323}{320}\left(1-\frac bt\right)
       >1-\frac bt.
\]
For \(a\ge3/5\), use (11), (13), and \(P>8/5\):
\[
 PBH>
 \frac85\frac53\frac38\left(1-\frac bt\right)
                   =1-\frac bt.
\]
The factor \(1-b/t\) is strictly positive throughout. This proves
the second inequality in (5). Section 2 proves the first.
Substitution in (4), followed by its strictly decreasing dependence
on \(p\), proves the claimed whole-boundary inequality (3).

This is the missing directional statement needed to combine the
coordinate monotonicities with the two fixed endpoints. Its use in
the physical contradiction uses the explicit case join in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md` and the exact original
force and angle implications in the cited sources.
No original force, mean, transmitter or extra square has been removed.
No Lean compilation, CI, workflow, finite sign mesh, or coefficient
file was used.
