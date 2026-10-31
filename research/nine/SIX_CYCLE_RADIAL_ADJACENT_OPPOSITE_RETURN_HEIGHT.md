# An adjacent/opposite radial pair has return height greater than 41/50

Date: October 26, 2026.

**Status: complete analytic local-pair theorem, accepted after independent
full-source review in REVIEW_C6_RADIAL_ADJACENT_OPPOSITE_HEIGHT_ROOT_2026_10_26.md.**
This source proves a necessary inequality for the whole strict-turn A/O
physical family. It does not yet exclude that core or its three-square
completion, and does not close an original parent gate.

Retain the original alternating all-side C6, exactly one physically radial
loaded square S, two physically unique loaded squares, the three original
positive side channels and every transmitter slider, both individual radial
circle weights, every actual mean and all nine physical squares. Work in
\[
 K=\frac{79}{40}\le R\le U=\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad r_0^2=d^2+\frac14.
\tag{1}
\]
The radial turn and both original unique turns are strictly greater than
\(\pi/2\). The actual S-incident application at one unique unit is its
adjacent-to-circle vertex (type A); that at the other is its opposite vertex,
and its return application is a nonshared adjacent vertex (type O).
The unchanged genuine A-side mean is allowed already to equal the specified
vertex. Normalize the actual return channel horizontally with outward height
\(H>0\).

**Theorem.**
\[
                              \boxed{H>\frac{41}{50}.}
\tag{2}
\]

## 1. Actual charts and the unchanged width-one reserve

For the A endpoint use the accepted actual adjacent chart:
\[
 c=\cos\eta,\quad s=\sin\eta,\quad \pi/4\le\eta<\pi/2,\quad
 D=s-c,\ C=s+c,\ Z=H+D,\ A=\sqrt{R^2-Z^2},
\]
\[
 a=cA+sZ,\quad b=sA-cZ,\quad a>b>\frac12,\quad
 t=\frac DZ,\quad Q=(-A+c,H-c),
\]
\[
 V=(tA-c,c),\quad L=|V|,\quad G=V/L,\quad P=Q-G.
\tag{3}
\]
The actual return span is \(m_A=A-C\), its properness condition is
\[
 \lambda=C-tA>0
 \quad\Longleftrightarrow\quad
 H>D(R/\sqrt2-1),
\tag{4}
\]
and \(|P|^2=r_0^2\). The accepted local theorem
SIX_CYCLE_RADIAL_ADJACENT_RETURN_DIAGONAL_BOUND.md gives \(c>3/8\);
hence \(0\le D<9/16\). Its proof uses the actual strict unique turn
and is applicable without any premise on the other endpoint.

For the O endpoint, in the reflected left chart, write
\[
 c=\cos\eta,\quad s=\sin\eta,\quad 0<\eta<\pi/4,\quad
 Z=H+s,\quad A=\sqrt{R^2-Z^2},
\]
\[
 a=cA+sZ,\quad b=cZ-sA,\quad a>b>\frac12,\quad t=\frac sZ,
\]
\[
 Q=(-A+c-s,H-c),\quad
 V=(tA+s-c,c)=Xv+Yu,
\]
\[
 v=(-c,s),\quad u=(s,c),\quad
 X=1-ta=\frac{cb}{Z}>0,\quad
 Y=1-tb>0,\quad L=|V|,\quad G=V/L,\quad P=Q-G.
\tag{5}
\]
The actual return span is \(m_O=A-c\), and again
\(|P|^2=r_0^2\). The local norm-root lemma in Section 2 of
SIX_CYCLE_ONE_RADIAL_TWO_OPPOSITE_PORTS_SINGLETON_CHANNEL_EXCLUSION.md
gives \(A>c\). That lemma is explicitly local and does not require a
second O endpoint.

The two applications at the actual nonshared return transmitter have
distance one. Thus the original, unmodified geometric equation is
\[
                              m_A+m_O=1.
\tag{6}
\]
No intermediate scalar comparison below is asserted to be a physical
packing or to preserve (6).

Suppose for contradiction that
\[
                             H\le h:=\frac{41}{50}.
\tag{7}
\]

## 2. The A norm root forces \(D<249/1000\)

Put \(D_0=249/1000\). We first show that an actual A norm root under
(7) cannot satisfy \(D\ge D_0\).

### 2.1 Complete comparison domain

Throughout \(H\le h\), \(D\le9/16\), and \(R\ge K\),
\[
 A^2-C^2=R^2-H^2-2HD-2
 \ge K^2-h^2-2h(9/16)-2
 =\frac{12229}{40000}>0.
\tag{8}
\]
At fixed original \(R,H\), lower D from its hypothesized actual value
to \(D_0\). The properness inequality (4) persists, and \(A>C\)
persists by (8). In own coordinates,
\[
 a'=-b(1-C/A),\qquad b'=a(1-C/A),
\tag{9}
\]
where prime denotes differentiation with respect to \(\eta\).
At the lower endpoint \(D_0\), uniformly over \(0<H\le h\),
\[
 b=s\sqrt{R^2-(H+D_0)^2}-c(H+D_0)
 >\frac45\frac{83}{50}-\frac35\frac{1069}{1000}>\frac12.
\tag{10}
\]
Here the fixed-angle bounds \(s>4/5,\ c<3/5\), and
\(A>83/50\) follow directly by squaring; the last A comparison at
\(R=K,H=h\) has reserve \(283/125000\).
Thus \(b>1/2\), \(a>b\) and all positive properness denominators
hold throughout the complete interpolation.

For the actual reconstructed A norm \(F_A=|P|^2\), put
\[
 L^2=1-2ta+t^2R^2,\quad
 J=(1+t)a-tR^2-1,\quad
 \mathcal C=L^3+tL^2+(1-t)(1-ta)>0.
\]
The exact formulas are
\[
 F_A=R^2+2-2a-\frac{2J}{L},\qquad
 \frac{L^3}{2}\frac{dF_A}{d\eta}
 =b(1-C/A)\mathcal C+t'(1-t)b^2>0.
\tag{11}
\]
These are the previously accepted adjacent-norm identities. They apply
on the entire interpolation established above. In particular
\[
 F_A(R,H,D_{\rm actual})\ge F_A(R,H,D_0).
\tag{12}
\]

Next keep \(R,D_0\) fixed and increase H to h. Properness improves
by (4), \(A>C\) holds by (8), and (10) bounds b from below throughout.
The exact partial derivatives are
\[
 (F_A)_a=-\frac{2\mathcal C}{L^3},\qquad
 (F_A)_t=\frac{2(1-t)b^2}{L^3},\qquad
 a_H=\frac bA>0,\quad t_H=-\frac{D_0}{(H+D_0)^2}<0.
\tag{13}
\]
Therefore \(F_A\) strictly decreases with H. It remains to show
\[
                        F_A(R,h,D_0)>r_0^2
                        \quad(K\le R\le U).
\tag{14}
\]

### 2.2 A single whole-radius endpoint comparison

In this paragraph only, \(H=h,\ D=D_0,\ Z=1069/1000,\ t=249/1069\)
and c,s are fixed. Put
\[
 x=\frac{c-tA}{L},\qquad y=\frac cL,\qquad
 v=\sqrt{R^2-\frac14}=\sqrt{A^2+Z^2-\frac14}.
\]
The following uniform rational bounds hold:
\[
 \frac{83}{50}<A<\frac95,\quad
 \frac{57}{100}<c<\frac{143}{250},\quad
 \frac{23}{100}<t<\frac7{30},\quad
 0<x<\frac{31}{100},\quad y>\frac{19}{20},\quad L<\frac23,
 \quad \frac Av>\frac{43}{50}.
\tag{15}
\]
Here \(c-tA>57/100-(7/30)(9/5)>0\).
For the only normalized-norm comparison, put
\[
 \rho=1-\frac{(249/1069)(83/50)}{143/250}
      =\frac{49532}{152867}.
\]
Then \((c-tA)/c<\rho\), and
\[
 (31/100)^2-\{1-(31/100)^2\}\rho^2
 =\frac{280500663193}{233683196890000}>0.
\]
This proves the x bound; the y and L bounds follow from
\(x^2+y^2=1\) and \(L=c/y\). The ratio \(A/v\) increases with A,
and at \(R=K\) its squared comparison has reserve
\[
 K^2-Z^2-(43/50)^2(K^2-1/4)
 =\frac{231447}{4000000}>0.
\]
The c comparisons have squared reserves \(4339/500000\) and
\(49/20000\), respectively.

Let \(\Gamma(A)=F_A-r_0^2\) along this fixed-angle comparison.
Direct differentiation of
\(F_A=(A-c-x)^2+(h-c-y)^2\) gives
\[
 \frac{\Gamma'(A)}2
 =\frac Av-c-x+
  \frac{ty}{L}\{y(A-c)+x(c-h)\}.
\tag{16}
\]
Using (15),
\[
 \frac Av-c-x>-\frac{11}{150},\qquad
 y(A-c)+x(c-h)>\frac9{10}.
\]
Consequently
\[
 \frac{\Gamma'(A)}2>
 -\frac{11}{150}
 +\frac{23}{100}\frac{19}{20}\frac32\frac9{10}
 =\frac{26597}{120000}>0.
\tag{17}
\]
Thus it suffices to compare \(R=K\). At this endpoint,
\[
 A-c-x>\frac{389}{500},\qquad
 c+y-h>\frac7{10},\qquad d<\frac{911}{1000}.
\]
The last square comparison has reserve \(81/62500\). Therefore
\[
 \Gamma(K)>
 \left(\frac{389}{500}\right)^2+\left(\frac7{10}\right)^2
 -\left\{\left(\frac{911}{1000}\right)^2+\frac14\right\}
 =\frac{15363}{1000000}>0.
\tag{18}
\]
This proves (14), contradicting the actual A norm root via
(12)--(13). Hence
\[
                              D<D_0=\frac{249}{1000}.
\tag{19}
\]

## 3. The O norm root forces \(s<3/20\)

Put \(s_0=3/20\). Suppose the actual O endpoint has \(s\ge s_0\).

### 3.1 Complete comparison domain

At fixed original \(R,H\), lower \(\eta\) to \(\arcsin s_0\).
The accepted local root \(A>c\), the identity
\[
 b>0\ \Longleftrightarrow\ H>s(R-1),\qquad (A-c)'=-b/A,
\]
and
\[
 a'=b(1-c/A),\qquad b'=-a(1-c/A)
\tag{20}
\]
show that \(b>1/2\), \(A>c\) persist when lowering the angle.
Also \(\delta=a-b\) increases with \(\eta\). At the new lower
endpoint, throughout \(H\le h\), it is positive: \(A>43/25\),
\(Z\le97/100\), \(c+s>1\), \(c-s<1\) give
\(\delta=(c+s)A-(c-s)Z>43/25-97/100>0\).
Thus \(\delta>0\) throughout the interval.
The positive X,Y identities in (5) remain valid.

Put \(h_1=a+b\), \(\delta=a-b\), and
\[
 L^2=2-2th_1+t^2R^2,\quad
 J=(1+t)h_1-tR^2-2,\quad
 \mathcal C=L^3+tL^2+(1-t)(2-th_1)>0.
\]
The full accepted O norm identities are
\[
 F_O=R^2+3-2h_1-\frac{2J}{L},
\]
\[
 \frac{dF_O}{d\eta}
 =\frac{2\delta}{L^3}
   \{(1-c/A)\mathcal C+t'(1-t)\delta\}>0.
\tag{21}
\]
Hence the actual norm is at least the comparison norm at \(s=s_0\).

At fixed \(s_0\), increase H to h. Here b increases, \(\delta\)
decreases, and at the final endpoint all of
\(b>1/2,\ \delta>0,\ A>c\) hold by the explicit bounds in the next
paragraph. Thus this entire second interpolation also has positive
X,Y,L and \(\delta\). The exact partial derivatives are
\[
 (F_O)_{h_1}=-\frac{2\mathcal C}{L^3},\qquad
 (F_O)_t=\frac{2(1-t)\delta^2}{L^3},\qquad
 (h_1)_H=\frac{\delta}{A}>0,\quad t_H=-\frac{s_0}{Z^2}<0.
\tag{22}
\]
Therefore this comparison strictly decreases \(F_O\).

### 3.2 A coupled whole-radius comparison

Now fix \(H=h,\ s=3/20,\ c=\sqrt{391}/20,\ Z=97/100,\ t=15/97\).
On the whole radius interval,
\[
 \frac{4943}{5000}<c<\frac{9887}{10000},\quad
 \frac{43}{25}<A<\frac{919}{500},\quad
 1<a<\frac{1963}{1000},\quad
 \frac{17}{25}<b<\frac{351}{500}.
\tag{23}
\]
For example, the two c squared reserves are
\(4251/25000000\) and \(2769/100000000\); the A lower bound
has squared reserve \(53/40000\). The a,b bounds follow by
substitution in \(a=cA+sZ,\ b=cZ-sA\).

In own axes write \(x=X/L,\ y=Y/L\). The preceding bounds imply
\[
 X>\frac{69}{100},\quad Y>\frac{89}{100},\quad
 0<x<\frac{63}{100},\quad y>\frac{31}{40}.
\tag{24}
\]
For the x comparison use
\[
 \frac XY=\frac{cb}{Z-sb}
 <\frac{(989/1000)(351/500)}{97/100-(3/20)(351/500)}
 =\frac{347139}{432350}.
\]
The squared reserve against \(x<63/100\) is
\(15142785831549/1869265225000000>0\).
The y comparison then follows by squaring.

Let
\[
 B(A)=d+2-a-b.
\]
Since \(v=d+1<81/40\) and \(A>43/25\),
\[
 B'(A)=A/v-(c-s)>\frac{344}{405}-\frac{21}{25}
                         =\frac{19}{2025}>0.
\tag{25}
\]
At \(R=K\), \(A<1721/1000\), with squared reserve
\(529/250000\). Using \(d>91/100\), we obtain the whole-radius
lower bound
\[
 B(A)>
 \frac{291}{100}
 -\frac{8387}{10000}\frac{1721}{1000}
 -\frac{11387}{10000}\frac{97}{100}
 =\frac{3620583}{10000000}.
\tag{26}
\]

We bound the positive part of \(Q\cdot G=(a-1)x+(b-1)y\)
in a coupled way, preserving the dependence of x on a.
At fixed \(H,s\),
\[
 \frac{d}{dA}\{(a-1)x\}
 =\frac{c}{L^3}\{XL^2-t(a-1)Y\}>0.
\tag{27}
\]
Indeed, (23)--(24), \(t<4/25,\ a-1<1,\ Y<1\) give the
strict lower bound
\[
 XL^2-t(a-1)Y>
 \frac{69}{100}\left\{\left(\frac{69}{100}\right)^2+
                     \left(\frac{89}{100}\right)^2\right\}
 -\frac4{25}=\frac{357529}{500000}>0.
\]
Thus this positive term is largest at \(R=U\).

At \(R=U\), direct squared bounds give
\[
 \frac{1837}{1000}<A<\frac{919}{500},\quad
 a>\frac{1961}{1000},\quad b<\frac{171}{250}.
\]
The A squared reserves are \(3749/4000000\) and
\(10951/4000000\). Hence
\[
 \frac XY<
 \frac{1-(15/97)(1961/1000)}
      {1-(15/97)(171/250)},\qquad x<\frac{123}{200}.
\tag{28}
\]
The last normalized-norm squared reserve is
\(8956783697/12038124160000>0\).

Equations (23)--(24), (27)--(28) now give the uniform upper bound
\[
 Q\cdot G
 <\frac{963}{1000}\frac{123}{200}
      -\frac{149}{500}\frac{31}{40}
 =\frac{72259}{200000}.
\tag{29}
\]
The actual norm formula has the exact difference
\[
 F_O-r_0^2=2\{d+2-a-b-Q\cdot G\}.
\]
Combining (26) and (29) proves, over the entire radius interval,
\[
 F_O(R,h,s_0)-r_0^2>
          \frac{7633}{5000000}>0.
\tag{30}
\]
The two monotone comparisons in Section 3.1 now contradict the
actual O norm root. We conclude
\[
                              s<s_0=\frac3{20}.
\tag{31}
\]

## 4. The actual return reserve contradicts these two angle bounds

At fixed R,D, \(m_A=\sqrt{R^2-(H+D)^2}-\sqrt{2-D^2}\)
strictly decreases with H. At \(H=h\), it decreases with D
through \(0\le D\le D_0\), because (4) holds on that whole
interval; equivalently
\[
 \frac{\partial m_A}{\partial D}
          =-\frac{h+D}{A}+\frac{D}{C}<0.
\]
It increases with R. Similarly
\(m_O=\sqrt{R^2-(H+s)^2}-\sqrt{1-s^2}\) decreases with H,
and at \(H=h\) decreases throughout \(0\le s\le s_0\), since
\(h>s(R-1)\) there. It too increases with R.
Thus (7), (19), and (31) imply
\[
 \begin{split}
 m_A+m_O>&
 \sqrt{K^2-(1069/1000)^2}-\sqrt{2-(249/1000)^2}\\
 &+\sqrt{K^2-(97/100)^2}-\sqrt{1-(3/20)^2}.
 \end{split}
\tag{32}
\]
All comparisons use the complete connected scalar domains just
specified, without changing a physical port, mean or channel.

Four fixed rational square comparisons give, respectively,
\[
 \sqrt{K^2-(1069/1000)^2}>\frac{166068}{100000},\qquad
 \sqrt{2-(249/1000)^2}<\frac{139213}{100000},
\]
\[
 \sqrt{K^2-(97/100)^2}>\frac{172038}{100000},\qquad
 \sqrt{1-(3/20)^2}<\frac{98869}{100000}.
\tag{33}
\]
Their positive squared reserves are
\(3711/625000000,\ 269369/10000000000,\
44139/2500000000,\ 79161/10000000000\).
The right side of (32) therefore exceeds
\[
 \frac{166068-139213+172038-98869}{100000}
                  =1+\frac3{12500}>1.
\tag{34}
\]
This contradicts the original width-one reserve (6) and proves (2).

## 5. Scope retained

The theorem concerns every original strict-turn A/O placement,
including reflection and exchange of the two unique loads. Its
proof uses only the actual local norm equations and the unchanged
original return width. Both radial weights, every original mean and
endpoint, all side-channel sliders and all extra physical squares
remain in place. The comparison parameters never create or assert
a replacement physical packing.

The result is a uniform necessary height bound. A further geometric
or completion contradiction is still required for A/O. No conclusion
is claimed here for a unique turn at most \(\pi/2\), for a genuine
owned return mean replacing the O port, or for the unrestricted
one-radial parent. No angle subdivision, sampled configuration,
computational coefficient packet, Lean compilation or CI is used.

