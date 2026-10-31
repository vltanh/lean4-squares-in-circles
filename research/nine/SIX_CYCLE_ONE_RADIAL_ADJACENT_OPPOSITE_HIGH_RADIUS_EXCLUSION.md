# The remaining adjacent/opposite one-radial family has no nine-square completion

Date: October 26, 2026.

**Status: accepted complete analytic physical-family proof**, after
full-source and scope reviews in
REVIEW_C6_RADIAL_ADJACENT_OPPOSITE_HIGH_RADIUS_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_ADJACENT_OPPOSITE_HIGH_RADIUS_BLOCK_2026_10_26.md. The local theorem below excludes the entire
A/O core for \(2\le R\le\sqrt{1105}/16\). The accepted global nine-square
radius theorem supplies \(R>2\) when all nine original squares are retained.
Thus the final join covers the original full radius window without claiming
an unconditional six-body exclusion in its lower-radius part.

Retain the original alternating all-side C6, exactly one physically radial
loaded unit S, the two physically unique loaded units, all three original
positive side channels and their full transmitter sliders, both individual
radial circle weights, every original actual application mean, and all nine
physical squares. All three actual turns in the branch considered here are
strictly greater than \(\pi/2\). At one unique unit, the S-incident port is
its actual adjacent-to-circle vertex and its return port is its opposite
vertex (type A). At the other, the S-incident port is its actual opposite
vertex and its return port is a nonshared adjacent vertex (type O).
An actual genuine A-side mean already at the adjacent vertex is included
with its unchanged contact label.

**Theorem.** This whole original strict-turn A/O family has no nine-square
completion. No scalar sign grid or new computational certificate is used
in the analytic exclusion.

## 1. Exact physical charts and the higher radius subwindow

The geometric theorem NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md,
accepted after its two separate full-source and exact-certificate reviews,
applies to all nine actual squares and gives \(R>2\).
We shall prove the stronger conditional core statement throughout
\[
                  2\le R\le U:=\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Put
\[
 d=\sqrt{R^2-\frac14}-1,\qquad r_0^2=d^2+\frac14,\qquad
                        h=\frac{21}{25}.
\tag{2}
\]
The two actual applications on the radial unit are its different strict
inner vertices. They both have norm \(r_0\), and their distance is one.

Normalize the actual A-to-O return channel horizontally, with outward side
above the origin and original height \(H>0\). The accepted physical charts
in SIX_CYCLE_RADIAL_ADJACENT_OPPOSITE_RETURN_HEIGHT.md apply.

At the left A endpoint write
\[
 c=\cos\eta,\quad s=\sin\eta,\quad
 \pi/4\le\eta<\pi/2,\quad D=s-c,\ C=s+c,
\]
\[
 Z=H+D,\quad A=\sqrt{R^2-Z^2},\quad
 a=cA+sZ,\quad b=sA-cZ,\quad a>b>\frac12,\quad t=D/Z.
\tag{3}
\]
Its actual return span is \(m_A=A-C\). Its S-incident port, inward
normal and original radial application are
\[
 Q=(-A+c,H-c),\qquad
 V=(tA-c,c),\quad L=|V|,\quad G=V/L,\quad P=Q-G,
 \qquad |P|^2=r_0^2.
\tag{4}
\]
The strict unique turn gives \(G_x<0\), and the accepted local
adjacent theorem gives \(c>3/8\). Consequently \(D<9/16\).
The exact properness condition is
\[
 C-tA>0\quad\Longleftrightarrow\quad
                   H>D(R/\sqrt2-1).
\tag{5}
\]

Use the reflected left chart at the right O endpoint:
\[
 0<\eta<\pi/4,\quad c=\cos\eta,\quad s=\sin\eta,\quad
 Z=H+s,\quad A=\sqrt{R^2-Z^2},
\]
\[
 a=cA+sZ,\quad b=cZ-sA,\quad a>b>\frac12,\quad t=s/Z.
\tag{6}
\]
Its original span is \(m_O=A-c\), and
\[
 Q=(-A+c-s,H-c),\quad V=(tA+s-c,c),\quad
 L=|V|,\quad G=V/L,\quad P=Q-G,\quad |P|^2=r_0^2.
\tag{7}
\]
The accepted local O norm-root lemma gives \(A>c\).
In its actual own axes the normal coordinates are
\[
 X=1-ta=\frac{cb}{Z}>0,\qquad
 Y=1-tb>0,\qquad X<Y.
\tag{8}
\]
That local lemma requires no second O endpoint.

The original reserve-one return transmitter gives
\[
                              m_A+m_O=1.
\tag{9}
\]
All these formulas refer to the original means and ports. No comparison
point used below is asserted to be a new physical packing.

## 2. The actual common return height exceeds 21/25

We first prove
\[
                                   H>h.
\tag{10}
\]
Suppose \(H\le h\).

### 2.1 A single adjacent comparison forces \(D<27/100\)

Set \(D_0=27/100\). Throughout the contrary domain,
\[
 A^2-C^2=R^2-H^2-2HD-2
 \ge4-h^2-2h(9/16)-2
 =\frac{1747}{5000}>0.
\tag{11}
\]
If the actual \(D\ge D_0\), lower its angle to \(D_0\).
The properness inequality (5) persists. At this lower endpoint,
uniformly in \(H\le h\),
\[
 b=sA-cZ>\frac{82}{100}\frac{83}{50}
                    -\frac{14}{25}\frac{111}{100}>\frac12,
\]
by direct substitution in the actual own-coordinate identity.
Thus the whole interval has \(a>b>1/2\).
The exact adjacent norm derivative is positive there:
\[
 \frac{L^3}{2}(F_A)_\eta
   =b(1-C/A)\mathcal C+t_\eta(1-t)b^2>0,
\]
\[
 F_A=|P|^2,\qquad
 \mathcal C=L^3+tL^2+(1-t)(1-ta)>0.
\tag{12}
\]
Increasing H to h at fixed \(D_0\) decreases \(F_A\), because
\[
 (F_A)_a=-2\mathcal C/L^3,\quad
 (F_A)_t=2(1-t)b^2/L^3,\quad
 a_H=b/A>0,\quad t_H=-D_0/Z^2<0.
\tag{13}
\]
The same lower b bound holds at the final height, and properness
only improves, so both complete comparison intervals are valid.

We show \(F_A(R,h,D_0)>r_0^2\) on the whole radius interval (1).
Here \(Z=111/100,\ t=9/37\), and
\[
 \frac{111}{200}<c<\frac{14}{25},\quad
 A>\frac{83}{50},\quad
 x:=\frac{c-tA}{L}\in(0,27/100),\quad
 y:=\frac cL>\frac{24}{25},\quad
 \frac{A}{\sqrt{R^2-1/4}}>\frac{17}{20}.
\tag{14}
\]
Every bound is a direct positive-square comparison. For example,
\[
 4-Z^2-(83/50)^2=\frac{123}{10000},\qquad
 4-Z^2-(17/20)^2(15/4)=\frac{2341}{40000}.
\]
For x, use
\[
 \frac{c-tA}{c}
 <1-\frac{(9/37)(83/50)}{14/25};
\]
its normalized-norm squared reserve against \(x<27/100\) is
\(8109593/10732960000>0\).
The sign \(c-tA>0\) holds throughout this fixed comparison, for
example from \(c>111/200,\ t<1/4,\ A<44/25\).

For any fixed A-type angle and H, with x,y as in (14), define
\(\Gamma=F_A-r_0^2\) and \(v=\sqrt{R^2-1/4}\). Direct
differentiation, using A as the radius variable, gives
\[
 \frac{\Gamma_A}{2}
 =\frac Av-c-x+\frac{ty}{L}
                  \{y(A-c)+x(c-H)\}.
\tag{15}
\]
In (14) the first three terms exceed \(1/50\), and the bracket
is positive. Thus \(\Gamma\) increases with R. At \(R=2\),
\[
 A-c-x>\frac{83}{100},\qquad
 c+y-h>\frac{27}{40},\qquad r_0^2=5-\sqrt{15}<\frac{113}{100}.
\]
Consequently
\[
 \Gamma(2)>
 (83/100)^2+(27/40)^2-113/100
                         =\frac{581}{40000}>0.
\tag{16}
\]
This contradicts the original norm through (12)--(13). Hence
\[
                                   D<27/100.
\tag{17}
\]

### 2.2 A single opposite comparison forces \(s<4/25\)

Set \(s_0=4/25\). If the actual O angle has \(s\ge s_0\),
lower it to \(s_0\). The accepted O root has \(A>c\), and
\[
 b>0\Longleftrightarrow H>s(R-1),\quad
 (A-c)_\eta=-b/A,\quad
 a_\eta=b(1-c/A),\quad b_\eta=-a(1-c/A).
\tag{18}
\]
Thus \(A>c\) and \(b>1/2\) persist. At the comparison endpoint,
\(A\ge\sqrt3,\ Z\le1\), so \(a-b=(c+s)A-(c-s)Z>0\);
it therefore remains positive throughout the lowering interval.

Put \(h_1=a+b,\delta_1=a-b\). The whole O identities are
\[
 (F_O)_\eta=\frac{2\delta_1}{L^3}
  \{(1-c/A)\mathcal D+t_\eta(1-t)\delta_1\}>0,
\quad
 \mathcal D=L^3+tL^2+(1-t)(2-th_1)>0.
\tag{19}
\]
At fixed \(s_0\), increase H to h. At the final endpoint the
explicit bounds below give \(b>1/2,\delta_1>0,A>c\).
These signs persist on the interval: b increases, \(\delta_1\)
decreases, and A decreases with H. Moreover
\[
 (F_O)_{h_1}=-2\mathcal D/L^3,\quad
 (F_O)_t=2(1-t)\delta_1^2/L^3,\quad
 (h_1)_H=\delta_1/A>0,\quad t_H=-s_0/Z^2<0.
\tag{20}
\]
Thus this second comparison decreases \(F_O\).

Now \(H=h,\ s=s_0,\ Z=1,\ t=4/25\), with
\[
 \frac{987}{1000}<c<\frac{247}{250},\qquad
 \sqrt3\le A<\frac{911}{500},\qquad
 1<a<2,\quad \frac{69}{100}<b<1,\quad
                   0<\delta_1<13/10,\quad L>1.
\tag{21}
\]
The squared c reserves are \(231/10^6\) and \(109/62500\).
The A upper comparison has reserve \(13111/4000000\).
The displayed bound on \(\delta_1=(c+s)A-(c-s)\) follows
from these same rational bounds, with reserve \(2209/62500\).

Write \(\xi=-G_x>0\) for the global normal component, to
distinguish it from the own coordinates X,Y in (8). We have
\[
 \frac{\xi}{\sqrt{1-\xi^2}}
  =\frac{c-s-tA}{c}>\frac{27}{50},
              \qquad \xi>\frac{47}{100}.
\tag{22}
\]
The ratio reserve is \(49/24700\); the normalized comparison
has squared reserve \(157139/25000000\).

For every fixed O-type angle and H, differentiation of the exact
norm gives
\[
 \frac{(F_O-r_0^2)_A}{2}
 =\frac Av-c+s-\xi+
              \frac{tc(1-t)(a-b)}{L^3}.
\tag{23}
\]
One way to verify (23) is to write
\(F_O-r_0^2=2[d+2-a-b-(a-1)X/L-(b-1)Y/L]\).
The derivative of the final own-coordinate dot product is
\(\xi-tc(1-t)(a-b)/L^3\).

Using (21)--(22), the right side of (23) is less than
\[
 1-\frac{98}{100}+\frac4{25}-\frac{47}{100}
                                      +\frac4{25}\frac{13}{10}
                         =-\frac{41}{500}<0.
\tag{24}
\]
Thus the norm difference is minimized at R=U.

At that endpoint \(A>91/50\). In addition
\[
 \frac{c-s-tA}{c}
  <\frac{247/250-4/25-(4/25)(91/50)}{987/1000}
\]
gives \(\xi<12/25\), with normalized squared reserve
\(41953664/15221390625>0\). Therefore
\(\sqrt{1-\xi^2}>7/8\). The two absolute port coordinates give
\[
 A-c+s-\xi>\frac{51}{100},\qquad
 c+\sqrt{1-\xi^2}-h>\frac{51}{50}.
\]
Since \(r_0^2<4621/3600\) throughout the original radius window,
\[
 F_O(U,h,s_0)-r_0^2>
 (51/100)^2+(51/50)^2-\frac{4621}{3600}
                              =\frac{19}{1125}>0.
\tag{25}
\]
Equations (18)--(20) contradict the actual norm. Hence
\[
                                    s<4/25.
\tag{26}
\]

### 2.3 The original return reserve gives the contradiction

Both spans decrease with H. At \(H=h\), the A span decreases
through \(0\le D\le27/100\), by (5), and the O span decreases
through \(0\le s\le4/25\), by \(h>s(R-1)\). Both increase with R.
The contrary height assumption, (17), and (26) therefore give
\[
 \begin{split}
 m_A+m_O>&\sqrt{4-(111/100)^2}-\sqrt{2-(27/100)^2}\\
        &+\sqrt3-\sqrt{1-(4/25)^2}\\
 &>\frac{1663-1389+1732-988}{1000}
                 =1+\frac9{500}>1.
 \end{split}
\tag{27}
\]
The four positive squared reserves are respectively
\(2331/10^6,\ 2221/10^6,\ 11/62500,\ 109/62500\).
This contradicts the original equality (9) and proves (10).

## 3. Two fixed-angle norms lie below the radial-port norm

For the rest of the proof \(H\ge h\). We shall establish the
uniform local bounds
\[
 s_A>\frac{81}{100},\quad -G_{A,x}<\frac{37}{100},
 \qquad
 s_O>\frac3{25},\quad -G_{O,x}<\frac{111}{200}.
\tag{28}
\]
The two normal inequalities require the whole fixed-normal
comparison in Section 4; they are not inferred from the angles
alone.

### 3.1 The adjacent reference \(H=h,\ s=81/100\)

In this reference, \(c=\sqrt{3439}/100,\ D=s-c,\ Z=h+D,\ t=D/Z\).
Direct positive-square comparisons give, uniformly over (1),
\[
 \frac{293}{500}<c<\frac{1173}{2000},\quad
 \frac{21}{100}<t<\frac{211}{1000},\quad
 \frac{1693}{1000}<A<\frac{357}{200}.
\tag{29}
\]
The c reserves are \(63/125000,\ 329/4000000\); the t
reserves are \(11/70900,\ 9/19000\); and the A reserves
are \(331/200000,\ 851/1000000\).

For its global normal write \(x=(c-tA)/L,\ y=c/L\). Then
\[
                         \frac{33}{100}<x<\frac{37}{100},
                  \qquad \frac9{10}<y<\frac{19}{20},\quad L<2/3.
\tag{30}
\]
For the lower bound, (29) gives
\[
 \frac{c-tA}{c}>
 \frac{293/500-(211/1000)(357/200)}{587/1000}
                          >\frac7{20}.
\]
The last reserve is \(783/117400\), and its normalized comparison
against \(x>33/100\) has reserve \(1039/4000000\).
For the upper bound,
\[
 \frac{tA}{c}>
 \frac{(21/100)(1693/1000)}{1173/2000}
              >\frac{121}{200},
 \qquad \frac{c-tA}{c}<\frac{79}{200}.
\]
The reserves are \(93/78200\) and, after normalization against
\(x<37/100\), \(893929/400000000\).

For this entire fixed-angle comparison, \(A/v>4/5\).
Using (15), its first three terms exceed \(-1/5\), while
\[
 y(A-c)+x(c-h)>
 \frac9{10}\left(\frac53-\frac35\right)
                  -\frac25\left(\frac{21}{25}-\frac{29}{50}\right)
 >\frac45.
\]
Since \(t>1/5,\ y>9/10,\ L<2/3\), (15) yields
\[
                        \frac{\Gamma_A}{2}>
                           -\frac15+\frac15\frac9{10}\frac32\frac45
                           =\frac2{125}>0.
\tag{31}
\]
It suffices to bound this increasing norm difference at R=U.
Equations (29)--(30) give positive absolute coordinates with
\[
 A-c-x<87/100,\qquad c+y-h<7/10.
\]
At U, \(d>1\), and therefore
\[
 F_A(U,h,s=81/100)<(87/100)^2+(7/10)^2
                    =\frac54-\frac{31}{10000}<r_0^2.
\tag{32}
\]
Thus \(F_A(R,h,s=81/100)<r_0^2\) for every R in (1).

This proves the actual angular bound \(s_A>81/100\).
Indeed, if the original \(s_A\le81/100\), first decrease its
height to h at its fixed angle. The properness condition (5)
holds throughout, because it holds both at the original point
and uniformly at h; b increases under this height decrease and
stays above \(1/2\). Formula (13) gives
\(F_A(R,H,\eta)\le F_A(R,h,\eta)\).
At \(H=h\), increase the angle to the reference value.
The whole interval \(0\le D\le81/100-\sqrt{3439}/100\)
has \(A>C,\ a>b>1/2\), so (12) increases the norm.
The result would be at least the actual norm \(r_0^2\),
contrary to (32). In particular the original endpoint \(D=0\)
is excluded by proof, including a genuine adjacent mean at that endpoint.

### 3.2 The opposite reference \(H=h,\ s=3/25\)

Here
\[
 c=\sqrt{616}/25,\quad Z=24/25,\quad t=1/8,\qquad
 \frac{124}{125}<c<\frac{993}{1000},\quad
 \frac74<A\le\frac{737}{400}.
\tag{33}
\]
The upper A value is exact at R=U. The lower A squared reserve
is \(159/10000\); the two c reserves are
\(24/15625,\ 449/10^6\).

Writing \(\xi=-G_x\), the ratio bounds give
\[
                  \frac{27}{50}<\xi<\frac{111}{200}.
\tag{34}
\]
For the lower bound,
\[
 \frac{c-s-tA}{c}>
 \frac{124/125-3/25-(1/8)(737/400)}{993/1000}
                                      >\frac{129}{200}.
\]
The last reserve is \(481/397200\), and the normalized
comparison against \(\xi>27/50\) has reserve
\(311211/10^8\).
For the upper bound, \(A>7/4,\ c<1\) give
\[
 \frac{c-s-tA}{c}
  <1-\frac3{25}-\frac18\frac74<\frac23.
\]
Thus \(\xi<2/\sqrt{13}<111/200\); the last squared
reserve in normalized form is \(173/360000\).

The own variables obey \(1<a<2,\ 7/10<b<1,\ a-b<13/10,\ L>1\).
Formula (23), using the weaker \(\xi>53/100\), gives
\[
 \frac{\Gamma_A}{2}
 <1-\frac{99}{100}+\frac3{25}-\frac{53}{100}
                       +\frac18\frac{13}{10}
 =-\frac{19}{80}<0.
\tag{35}
\]
Hence this fixed-angle norm difference decreases with R.
At \(R=2\), \(A<351/200\), with squared reserve \(13/8000\).
Both absolute port coordinates are positive and satisfy
\[
 A-c+s-\xi<7/20,\qquad
 c+\sqrt{1-\xi^2}-h<1.
\]
For the second, (34) gives
\(\sqrt{1-\xi^2}<169/200\), and (33) then gives a bound below one.
Consequently
\[
 F_O(2,h,s=3/25)<1+(7/20)^2
                  =\frac98-\frac1{400}<5-\sqrt{15}=r_0^2.
\tag{36}
\]
The final strict comparison follows from \(\sqrt{15}<31/8\).
Thus the reference norm is below \(r_0^2\) on the entire interval (1).

It follows that every actual O root has \(s_O>3/25\).
If \(s_O\le3/25\), decrease H to h first.
The accepted actual \(A>c,\delta_1>0\) improve under this
decrease; and at the lower height b is still greater than
\[
 (99/100)(21/25)-(3/25)(133/64)>1/2.
\]
Thus (20) applies throughout. At \(H=h\), increasing the
angle to \(s=3/25\) keeps \(A>c,\ a>b>1/2\) and increases
the norm by (19), contradicting (36).

## 4. A whole fixed-normal monotonicity propagates the normal bounds

The following argument treats the two full vertex types with no
subdivision of their angles or force ratios. It is a comparison
of the original reconstructed norm functions only.

At an actual endpoint put
\[
                 G=(-\sin\psi,\cos\psi),\qquad
                 k=\tan\psi,\qquad w=1-k.
\tag{37}
\]
In either type \(0<\psi<\pi/4\).
For O this follows directly from (7)--(8).
For A, Section 3.1 has already excluded \(D=0\), so \(t>0\)
and the actual inward normal in own axes has both required
strict components; hence \(\psi<\pi/4\).
This step retains and then excludes the genuine endpoint case,
rather than silently imposing strictness on it.

Fix the original R and \(\psi\). Let
\[
                   A=R\cos\theta,\qquad Z=R\sin\theta.
\]
The normal equations in (4),(7), with \(T=\tan\eta\), become
\[
 \begin{array}{c|c|c}
 \text{type}&\tan\theta&\text{complete positive own-coordinate interval}\\
 \hline
 A&(T-1)/(1-k)&1<T<1/k\\
 O&T/(1-k-T)&0<T<(1-k)/(1+k).
 \end{array}
\tag{38}
\]
In type A the interval is precisely \(0<\eta-\theta<\pi/4\);
in type O it is \(0<\theta-\eta<\pi/4\).
The actual endpoint belongs to the relevant interval. Any reference
endpoint used below belongs to it as well.

On both complete intervals,
\[
                                  \theta_\eta>1.
\tag{39}
\]
Here is an elementary proof of the whole sign. In type A the positive
denominator of \(\theta_\eta-1\) is
\(w^2+(T-1)^2\), and its numerator is
\[
                    -kT^2+2T-(1-k+k^2).
\]
This is concave in T. At \(T=1\) and \(T=1/k\) its values are
\(1-k^2>0\) and \((1-k)(1/k+k)>0\), respectively.
In type O the denominator is \((w-T)^2+T^2\), and the numerator is
\[
                  w-w^2+2wT+(w-2)T^2.
\]
It is again concave; at \(T=0\) and \(T=w/(2-w)\) its values are
\(w(1-w)>0\) and \(w(2-2w+w^2)/(2-w)>0\).
This proves (39) on the whole domains, not just at their endpoints.

Write \(\beta=\eta+\psi,\ S=\sin\beta,\ C_\beta=\cos\beta\).
The original reconstructed norms have these own-frame forms:
\[
 \begin{array}{ll}
 A:&F_A=(a-1-S)^2+(b+C_\beta)^2,\\
 O:&F_O=(a-1-S)^2+(b-1-C_\beta)^2.
 \end{array}
\tag{40}
\]
In A, \(a=R\cos(\eta-\theta),\ b=R\sin(\eta-\theta)\);
in O, \(a=R\cos(\theta-\eta),\ b=R\sin(\theta-\eta)\).
Thus b decreases with \(\eta\) in A and increases with \(\eta\)
in O. In particular any interval between two endpoints with
\(b>1/2\) keeps that inequality. The complete domains (38)
also preserve \(a>b\) and \(a>R/\sqrt2>1\).

Direct differentiation of (40), with \(\psi,R\) fixed, gives
\[
 \frac{(F_A)_\eta}{2}
   =b+C_\beta-\theta_\eta
                    \{aC_\beta+b(1+S)\}<0.
\tag{41}
\]
Indeed \(S,C_\beta>0,\ a>1,\ b>0\), and (39) apply.
For O, the actual properness condition gives
\(\beta<\pi/4\), equivalently the O interval in (38), so
\(C_\beta>S>0\). Its derivative is
\[
 \frac{(F_O)_\eta}{2}
 =(1-a)C_\beta+(b-1)S
  +(\theta_\eta-1)\{b(1+S)-a(1+C_\beta)\}<0.
\tag{42}
\]
The first two terms have negative sum whether \(b\le1\) or
\(b>1\), and the expression in braces is negative because
\(a>b,\ C_\beta>S\).

The corresponding reconstructed heights are
\[
 H_A=R\sin\theta-(s-c),\qquad H_O=R\sin\theta-s.
\tag{43}
\]
They are positive on the entire intervals (38):
in A, \(\theta>\eta-\pi/4\) and \(R>\sqrt2\);
in O, \(\theta>\eta\) and \(R>1\).
Also
\[
 (A-s-c)_\eta=-Z\theta_\eta+(s-c)<-H_A<0,
\]
\[
 (A-c)_\eta=-Z\theta_\eta+s<-H_O<0.
\tag{44}
\]
Whenever the appropriate span on the left is positive at an upper
endpoint, it remains positive at every smaller angle.
On that lower interval (39) therefore gives
\[
 (H_A)_\eta=A\theta_\eta-(s+c)>0,\qquad
 (H_O)_\eta=A\theta_\eta-c>0.
\tag{45}
\]

### 4.1 Apply the comparison to the actual A normal

Suppose the actual \(x_A=-G_{A,x}\ge37/100\).
At height h, the A normal component decreases continuously from
\(1/\sqrt2\) at \(\eta=\pi/4\) to a value below \(37/100\)
at the reference \(s=81/100\), by (30).
On this entire small-angle interval, \(A>s+c,\ a>b>1/2\).
The strict decrease of the normal component follows either by
differentiating (4), or from (45): at fixed angle, both formulas
for \(\tan\theta\) in (38) strictly increase with k and hence
with \(\psi\). Thus the fixed-normal height increases with
\(\psi\), so a fixed-height increase of angle decreases \(\psi\).
Thus there is a unique matching reference angle \(\eta_0\)
at height h with the same original normal \(\psi\), no larger
than the reference angle of Section 3.1.

The fixed-height norm increases with angle on this interval by (12).
Consequently the matching reference has
\[
                         F_A(\eta_0)<r_0^2.
\tag{46}
\]
Now compare the actual angle with \(\eta_0\), at fixed
\(R,\psi\). The entire connecting interval lies in (38);
the monotone b observation after (40) preserves \(b>1/2\).
Equation (41) says the norm strictly decreases with angle.
Since the actual norm is \(r_0^2\), (46) forces
\(\eta_{\rm actual}<\eta_0\).

The matching reference has \(A>s+c\), so (44)--(45) apply
throughout this lower interval and imply
\(H_{\rm actual}<H(\eta_0)=h\).
This contradicts (10). We have proved
\[
                              -G_{A,x}<37/100.
\tag{47}
\]

### 4.2 Apply the comparison to the actual O normal

Suppose the actual \(x_O=-G_{O,x}\ge111/200\).
At height h, the O normal component decreases continuously from
\(1/\sqrt2\) at \(\eta=0\) to a value below \(111/200\)
at \(s=3/25\), by (34).
This entire interval has \(A>c,\ a>b>1/2\).
The same fixed-normal height identity (45), or direct
differentiation of (7), proves the strict decrease.
Therefore it contains a unique matching reference \(\eta_0\)
with the same \(\psi\).

The fixed-height O norm increases with angle by (19), so (36)
gives \(F_O(\eta_0)<r_0^2\).
The whole fixed-normal derivative (42) then forces the actual
angle to be smaller than \(\eta_0\), with every own-coordinate
sign preserved on their connected interval. The reference
has \(A>c\), and (44)--(45) consequently give
\(H_{\rm actual}<h\), again impossible. Thus
\[
                              -G_{O,x}<111/200.
\tag{48}
\]
Sections 3 and 4 prove all four inequalities in (28).

## 5. The actual radial port separation is greater than one

Return to the actual horizontal channel, keeping A on the left
and O on the right. Put \(x_i=-G_{i,x}>0\) in each left chart,
and \(y_i=\sqrt{1-x_i^2}\). Equations (3)--(7) give the two
unchanged applications on S:
\[
 P_A=(-m_A-s_A+x_A,\ H-c_A-y_A),
\]
\[
 P_O=(m_O+s_O-x_O,\ H-c_O-y_O).
\tag{49}
\]
Using the original reserve (9), their horizontal difference is
\[
 (P_O-P_A)_x=1+s_A+s_O-x_A-x_O.
\tag{50}
\]
The four whole-domain bounds (28) imply
\[
 (P_O-P_A)_x>
 1+\frac{81}{100}+\frac3{25}
                -\frac{37}{100}-\frac{111}{200}
                         =\frac{201}{200}>1.
\tag{51}
\]
But these are the original different inner vertices of the same
unit square S, so \(|P_O-P_A|=1\). Equation (51) is impossible.

This proves the entire conditional A/O core exclusion for (1).
The accepted global \(R>2\) theorem applies to all nine original
units, so no original A/O core in the full original radius window
can admit the required nine-square completion.

## 6. Exhaustive scope and the remaining owner cover

The source covers reflection and exchange of the A and O unique
loads. It retains a genuine S-side A mean already at its actual
adjacent endpoint; Section 3 explicitly excludes its possible
\(D=0\) endpoint before strict fixed-normal divisions are used.
The O return is the original nonshared adjacent vertex. A genuine
owned return mean belongs to the separately accepted A/T theorem
and is not silently substituted here.

Together with the accepted A/A, A/M, M/M, O/O, O/M, O/T, T/T,
T/M and A/T results, this closes the last feature pair in the
complete one-radial cover **when both unique turns are strictly
greater than \(\pi/2\)**. The radial right-turn family has its
separate accepted full-slider classification and completion join.
This source does not infer the strict unique-turn hypothesis for
the remaining lower-turn placements.

Both individual radial circle weights, all original positive
channel forces, every genuine mean and endpoint, all three
transmitter sliders and all three extra squares remain.
The only finite-certificate dependency is the already accepted
single global nine-square radius theorem; no new local sign packet,
angle grid, force box, sampled configuration, Lean compilation
or CI is used here.

