# The entire low-turn single radial-incident mean family is excluded

Date: October 26, 2026.

**Status: accepted complete analytic physical-family proof**, after
REVIEW_C6_RADIAL_LOW_SINGLE_MEAN_AND_SHARED_ANGLE_2026_10_26.md and
REVIEW_C6_RADIAL_LOW_REMAINING_ROOT_2026_10_26.md. This proof keeps the original genuine mean and excludes every
strict-partner type simultaneously. It does not change a mean to an
adjacent vertex and uses no computational certificate.

Retain the original alternating all-side C6 with one physically radial
loaded unit S, two physically unique loaded units L,T, and three true
unloaded degree-two reserve-one side transmitters. Both original radial
corner weights, all original positive forces and actual normals, the
full application means and their endpoints, all transmitter sliders
and all nine physical units remain. The zero-individual-weight cases
retain their separate accepted exclusion.

Suppose L has turn at most \(\pi/2\), its original S-incident interface
is genuinely shared, and L does not own its return interface. This is
the S-owned placement in either one-owner row of
`SIX_CYCLE_ONE_RADIAL_LOW_TURN_FEATURE_COVER.md`. That exhaustive
cover puts L's other actual application at the appropriate adjacent
vertex, and keeps the S mean as its true strict-interior point.

**Theorem.** This entire original family has no nine-square completion
in the target radius window. The proof applies to both orientations
and every true S-mean value; there is no choice of a new endpoint.

For an actual completion the accepted global measure theorem gives
\(R>2\). It suffices to prove the contradiction on
\[
 2\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,
 \qquad d_0=\sqrt{15}/2-1\le d<61/60.
\tag{1}
\]

## 1. The exact low single-mean chart

At the original S port choose its complete reflected chart as needed:
\[
 P=(d,1/2),\qquad v=(-\cos\alpha,\sin\alpha),
 \qquad u=(\sin\alpha,\cos\alpha),
 \qquad 0<\alpha<\pi/2.
\tag{2}
\]
Here v is the actual S-to-L channel direction and u is its clockwise
perpendicular. Since L owns this normal, v and u are its actual own
side axes in the orientation fixed by the physical moment. Write
its actual circle corner as
\[
                              z=av+bu,
 \qquad a,b>1/2,\qquad a^2+b^2=R^2.
\]
The actual S mean, concurrence and nonowned return vertex are exactly
\[
 Q=(a-1)v+\tau b\,u,
 \qquad q=\tau(av+bu),
 \qquad T=av+(b-1)u,
 \qquad 0<\tau\le1.
\tag{3}
\]
These are the incoming-bottom-owner row after exchanging the names
of the two physical axes, or its reflected outgoing-owner version.
The actual normal reserve is \(P=Q-v\). Taking its scalar products
with the two actual axes in (2), define
\[
 \begin{split}
 k&=d\cos\alpha-\tfrac12\sin\alpha,\qquad a=2-k,\\
 h&=d\sin\alpha+\tfrac12\cos\alpha=\tau b,\\
 b&=\sqrt{d^2+2d+5/4-a^2},\qquad t=1-\tau=1-h/b.
 \end{split}
\tag{4}
\]
Thus h is the unchanged true mean coordinate. No new independent
mean parameter is introduced.

The proper vector from q to the actual return vertex is
\[
                         T-q=ta\,v-(1-tb)u.
\tag{5}
\]
The one-owner row has \(ta>0\) and \(1-tb>0\); otherwise the
actual return would also be an owned axis or would violate the
strict point-normal convention. Therefore its actual turn is acute
and satisfies
\[
                         \tan\theta_L=\frac{1-tb}{ta}.
\tag{6}
\]

Let \(\beta>0\) be the other actual radial-port angle. The original
turn sum, \(\theta_S=\pi-\alpha-\beta\), and the complete unique
bound \(\theta_T\le3\pi/4\) give
\[
           \theta_L=\pi+\alpha+\beta-\theta_T
                    \ge\pi/4+\alpha+\beta>\pi/4.
\tag{7}
\]
Combining (6)--(7), every actual member of the family must obey
\[
                  \boxed{F(d,\alpha):=t(a+b)<1.}
\tag{8}
\]

## 2. A connected whole-domain comparison for the true mean

We prove
\[
 F(d,\alpha)>1
 \quad\text{whenever}\quad
 d_0\le d\le61/60,\quad0\le\alpha\le1/2.
\tag{9}
\]
All quantities in this comparison remain the exact functions (4).
The comparison is in scalar formulas; it does not move any actual
square or change its mean.

Write \(s=\sin\alpha,c=\cos\alpha\). The elementary bounds
\(d>187/200\), \(c\ge7/8\), \(0\le s\le1/2\) give
\[
 a\ge2-d\ge59/60>1/2,
 \qquad
 b^2-h^2=2d(1+2c)-3-2s>457/400>0.
\tag{10}
\]
Hence b is positive on the complete comparison rectangle, b>h>0,
and \(0<t<1\). Also \(b<d+1\), since
\(a^2>1/4\) and \(a^2+b^2=d^2+2d+5/4\).
Thus every differentiation below occurs on a connected domain with
all denominators strictly positive. No disconnected root branch or
unproved physical interpolation is used.

### 2.1 Increasing the radius parameter increases F

At fixed alpha,
\[
 a_d=-c,\qquad h_d=s,\qquad
 b_d=\frac{d+1+ac}{b}.
\]
Writing \(\tau=h/b\), its derivative has the sign of
\[
 \begin{split}
 s b^2-h(d+1+ac)
 &=s\{2d(1+2c)-3-2s\}-h(1+2c)\\
 &=s\{d(1+2c)-3\}-1-s^2-c/2<0.
 \end{split}
\tag{11}
\]
Indeed \(d(1+2c)-3\le1/20\) and \(s\le1/2\), so the last
expression is less than \(1/40-1<0\). Therefore t increases
strictly with d.

The sum of the own corner coordinates also increases:
\[
 (a+b)_d=\frac{d+1+c(a-b)}b>0.
\tag{12}
\]
For the last sign use \(d+1>b\): its numerator exceeds
\(b+c(a-b)=ca+(1-c)b>0\). Since t and a+b are positive,
\[
                              F_d>0.
\tag{13}
\]

### 2.2 Increasing the radial-port angle decreases F

At fixed d, the actual radius is fixed and
\[
 a_\alpha=h,\qquad h_\alpha=k,\qquad
 b_\alpha=-ah/b,
 \qquad
 \tau_\alpha=\frac{k}{b}+\frac{ah^2}{b^3}>\frac{k}{b}>0.
\tag{14}
\]
Here
\[
                 k>909/1600>0,
 \qquad h\le121/120,
 \qquad b-a<2d-1\le31/30.
\tag{15}
\]
The first follows from \(d>187/200,c\ge7/8,s\le1/2\);
the others follow from (4), \(b<d+1\) and \(a\ge2-d\).

If \(a\ge b\), then \((a+b)_\alpha=h(1-a/b)\le0\),
so \(F_\alpha<0\) immediately. If \(a<b\), use \(t<1\),
\(a+b>R\ge2\), and
\[
 k(a+b)>\frac{909}{800}
        >\frac{121}{120}\frac{31}{30}>h(b-a).
\tag{16}
\]
The middle reserve is \(679/7200>0\). Consequently
\[
 \begin{split}
 F_\alpha
 &=-\tau_\alpha(a+b)+t h(1-a/b)\\
 &<\frac{-k(a+b)+h(b-a)}b<0.
 \end{split}
\tag{17}
\]
Thus the decreasing sign holds throughout the full comparison
rectangle, on both sides of \(a=b\).

Equations (13),(17) reduce (9) to the single fixed endpoint
\((d,\alpha)=(d_0,1/2)\).

## 3. The fixed endpoint has F greater than one by elementary bounds

At this endpoint,
\[
             187/200<d_0<15/16.
\tag{18}
\]
The upper square comparison has reserve \(1/256\).
The signed sine and cosine estimates at \(1/2\) give
\[
 \frac{23}{48}<\sin(1/2)<\frac{12}{25},
 \qquad
 \frac{351}{400}<\cos(1/2)<\frac89.
\tag{19}
\]
For the nontrivial rational comparisons, the upper sine polynomial
of degree five lies below \(12/25\) by \(11/19200\), the lower
cosine polynomial of degree six exceeds \(351/400\) by
\(19/230400\), and the upper cosine polynomial of degree four
lies below \(8/9\) by \(13/1152\).

It follows that
\[
 a>2-\frac{15}{16}\frac89+\frac{23}{96}
       =\frac{45}{32}>\frac75,
\]
\[
 a<2-\frac{187}{200}\frac{351}{400}+\frac6{25}
       =\frac{113563}{80000}<\frac{71}{50}.
\tag{20}
\]
Since the endpoint radius is exactly two,
\[
 b^2=4-a^2>4-(71/50)^2>(7/5)^2,
\tag{21}
\]
where the last reserve is \(59/2500\). Also
\[
 h<\frac{15}{16}\frac{12}{25}+\frac12\frac89
       =\frac{161}{180}<\frac9{10}.
\tag{22}
\]
Thus a,b>7/5 and h<9/10 at the fixed endpoint. Therefore
\[
 F(d_0,1/2)
 =\left(1-\frac hb\right)(a+b)
 >\left(1-\frac{9/10}{7/5}\right)\frac{14}{5}=1.
\tag{23}
\]
The whole-domain monotonicities prove (9). Comparing it with the
actual strict inequality (8) yields the original necessary bound
\[
                              \boxed{\alpha>1/2.}
\tag{24}
\]

## 4. Every strict partner is now excluded without changing the mean

The original turn cover gives \(\alpha+\beta\le\pi/4\).
Equation (24) consequently implies
\[
                         0<\beta<\pi/4-1/2<2/7.
\tag{25}
\]
The local theorem
`SIX_CYCLE_RADIAL_STRICT_PARTNER_SMALL_ANGLE_EXCLUSION.md`
excludes strict partner types A, M and O directly from (25).
Its local statement has no adjacent-application premise at L.

For strict partner type T, use the exact angle argument of
`SIX_CYCLE_ONE_RADIAL_LOW_ADJACENT_RETURN_OWNER_EXCLUSION.md`,
Sections 1--4. Its algebraic premises after deriving the angle bound
are precisely \(\alpha>1/2\), \(\theta_L\le\pi/2\), and the
unchanged genuine T-owned chart. In particular the owned axis gives
\(\theta_T=\pi-\eta\), so
\(\theta_L=\alpha+\beta+\eta\). Then
\(n=\sin\eta-\cos\eta<51/128<2/5\), while the actual T circle
equation gives \(d=w(m+1)+hn\). Its uniform estimate yields
\[
 d<187/200-4377/171500<187/200<d.
\]
This argument is applied to the actual mean family using the newly
proved (24), not by calling L's actual S application adjacent.
No mean, owner label or physical port has changed. Equivalently,
the generic radial-angle corollary in that source has exactly these
premises.

The strict A/M/O/T cover is exhaustive, so every strict partner is
excluded. This closes the entire low-turn single-S-owner family,
including the two reflected orientations and every genuine actual
mean allowed by the original cover.

The actual low opposite-vertex row and the separate both-inner-axis
owner row remain outside the theorem. The full original one-radial
parent is not claimed closed by this source alone. The use of all
nine squares in (1) is explicit; no unconditional lower-radius
six-core impossibility is inferred. No numerical pose, parameter
grid, extra certificate, Lean compilation or CI is used.
