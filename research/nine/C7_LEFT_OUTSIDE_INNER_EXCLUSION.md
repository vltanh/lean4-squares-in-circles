# The entire asymmetric left-outside inner-pair branch is impossible

**Status: complete hand branch theorem; root and separate independent full hand audits passed.**
Use the fixed circle origin, the C7 hypotheses, and the exact pair
notation from `C7_INNER_PAIR_FAR_FACE_CENTERS.md`. Put

\[
Q=\frac{1105}{256},\qquad M=\frac{91}{60},\qquad
k=\frac{3721}{7200},\qquad e=k-\frac12=\frac{121}{7200}.
\]

All boundary units are contained in the disk of squared radius at most
\(Q\); their centers have norms less than \(M\), pairwise distances
less than three, and mutual distances at least one. The established
center-polygon and radial-tail consequences apply to every enclosed
unit. In particular, all its own center coordinates have absolute value
less than \(k\), and every vertex has norm greater than \(19/300\).

Choose an actual separating axis owned by the left inner unit \(T\).
Write

\[
C_T=(-\alpha,\beta),\qquad C_U=a u+\eta v,
\quad u=(c,s),\quad v=(-s,c),\quad
c=\cos\theta,\quad s=\sin\theta>0.
\]

The pair restrictions give

\[
0<s<\frac4{15},\quad c>\frac{14}{15},\quad
0<\tau:=\tan(\theta/2)<\frac4{29},
\tag{1}
\]

and the far-face theorem supplies an actual boundary center

\[
C_R=(a+1+\varepsilon)u+(\eta+r)v,
\qquad \varepsilon\ge0,\quad |r|\le\frac12,
\qquad r>\frac12-\frac32\tau.
\tag{2}
\]

The preceding theorem `C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md` leaves
exactly

\[
\boxed{a<\frac12,\qquad \alpha>\frac12.}
\tag{3}
\]

**Theorem.** The entire case (3) is impossible. The proof keeps the
original separating-axis owner, every inner tangential coordinate,
every actual outer frame, and all separator owner/sign cases. Together
with the right-outside theorem and the parallel-pair exclusion, this
excludes two interior-disjoint enclosed units in the C7 domain.

## 1. The whole remaining parameter range

The actual pair separator says

\[
\alpha+a c-\eta s\ge\frac{1+c+s}{2}.
\tag{4}
\]

The far-face theorem gives \(a>9/20\). Both secondary own center
coordinates have magnitude less than \(1/2\): otherwise the
outside-face/corner restriction would make the corresponding main
coordinate less than \(3/8\). In particular \(|\eta|<1/2\).

First, \(\eta<0\). If \(\eta\ge0\), using
\(\alpha,a<k\) in (4) yields

\[
(1/2+\eta)\tau<e,\qquad
r>1/2-3e=1079/2400.
\]

But the first own coordinate of \(C_R\) is greater than \(29/20\),
so its other coordinate satisfies

\[
|\eta+r|<\sqrt{M^2-(29/20)^2}
=\sqrt{89/450}<89/200<1079/2400,
\]

a contradiction. Set

\[
\eta=-b,\qquad d=1/2-a,
\qquad P=1/2-b.
\]

Thus \(0<b<1/2\) and \(d>0\). The general pair estimate and (1)
give

\[
a>\frac12-e\frac{1+s}{c}
>\frac12-\frac{19e}{14}>\frac{19}{40}.
\tag{5}
\]

In fact \(b<a\). If \(b\ge a\), the inner vertex with own
coordinates \((a-1/2,1/2-b)\) has norm less than
\(\sqrt2/40<19/300\), contradicting the established vertex bound.

Next,

\[
b<\frac5{12}.
\tag{6}
\]

Otherwise \(b\ge5/12>2a/3\), and the sharp balanced radial-tail
theorem gives

\[
F_R(a,b):=(a+1)^2+
\left(b\left(1+\frac1{2a}\right)-\frac12\right)^2<M^2.
\]

This expression increases with \(b\) on the domain in question.
At \(b=5/12\) it also increases with \(a\in[19/40,1/2]\): its
derivative is

\[
2(a+1)-\frac{b}{a^2}
\left(b\left(1+\frac1{2a}\right)-\frac12\right)>0,
\]

because \(b/a^2<2\) and the parenthesized term is less than
\(1/2\). At the lower endpoint,

\[
F_R(19/40,5/12)
=\left(\frac{59}{40}\right)^2+
\left(\frac{27}{76}\right)^2
=M^2+\frac{1621}{1039680}>M^2,
\]

proving (6).

Equation (4), with \(\alpha<1/2+e\), now becomes

\[
d c+P s<e.
\tag{7}
\]

Here \(P>1/12\), \(d<1/40\), and \(\tau<1/2\), so
\(P>d\tau\). The identity \(c+\tau s=1\) gives
\(dc+Ps>d\). Consequently

\[
0<d<e,\qquad 1-k<a<1/2,
\qquad a>12/25.
\tag{8}
\]

Write

\[
L(d)=\sqrt{M^2-(3/2-d)^2}
=\sqrt{M^2-(a+1)^2}.
\tag{9}
\]

This is increasing on \([0,e]\), and

\[
L(d)\le L(e)<\frac8{25};
\quad
\left(\frac8{25}\right)^2-L(e)^2
=\frac{103057}{51840000}>0.
\tag{10}
\]

The last necessary lower bound is

\[
\boxed{\frac9{50}<b<\frac5{12}<a.}
\tag{11}
\]

Only the lower inequality remains to prove. If \(b\le9/50\),
then \(P\ge8/25\). Expressing (7) in half-angle coordinates gives

\[
e-d>2P\tau-(d+e)\tau^2.
\tag{12}
\]

Since

\[
2P-(d+e)\tau>
\frac{16}{25}-2e\frac4{29}>\frac58,
\]

we have \(\tau<(8/5)(e-d)\). Equations (2) and (9) give

\[
b>r-L(d)>
\frac12-L(d)-\frac{12}{5}(e-d).
\tag{13}
\]

The final expression decreases with \(d\in[0,e]\), because

\[
L'(d)=\frac{3/2-d}{L(d)}>
\frac{37/25}{8/25}=\frac{37}{8}>\frac{12}{5}.
\]

It is therefore at least \(1/2-L(e)>9/50\), contradicting the
assumed upper bound on \(b\). This proves (11).

## 2. Every outgoing ray witness has a nearly radial actual frame

Reflect the own frame of \(U\) vertically. Its center is now
\(z=(a,b)\), and its unit square is
\(z+[-1/2,1/2]^2\). A boundary unit \(S\) meets the outgoing
ray beyond this inner square, because the latter is enclosed.
Every such witness satisfies

\[
\boxed{|C_S|>\rho_0:=1483/1000.}
\tag{14}
\]

We verify (14) for arbitrary separating normals, not just own-axis
normals. Rotate the center ray to the positive first axis. The inner
center is \((\rho,0)\), its frame is
\((u_0,-v_0),(v_0,u_0)\), and

\[
u_0\ge v_0\ge0,\qquad \rho=a/u_0.
\]

Every separator toward the outgoing witness has the form
\(n=(A,\pm B)\), \(A>0\), \(B\ge0\),
\(A^2+B^2=1\). Put

\[
F=\rho A+H_U(n),\qquad
n\cdot C_S\ge F+H_S(n).
\]

### 2.1. Shallow radial normals

For \(A\ge B\), the positive expression \(F\) is concave
between consecutive frame alignments as a function of signed normal
angle. At the own-axis breakpoint it equals \(a+1/2\); at either
forty-five-degree endpoint it equals

\[
\frac{a/u_0+u_0}{\sqrt2}\ge\sqrt{2a}.
\]

Also \(a+1/2\ge\sqrt{2a}\). Thus

\[
|C_S|\ge\frac12+\sqrt{2a}>
\frac12+\sqrt{2(1-k)}>\frac{1483}{1000}.
\]

The last comparison follows from
\(2(1-k)-(983/1000)^2=899/9000000>0\).

### 2.2. Steep radial normals

For \(A\le B\), compare with the radial center
\(\rho_*=1/(2u_0)\) used in `CENTER_COVER_PIERCING.md`.
The deficit is

\[
\Delta=\rho_* -\rho=d/u_0<e\sqrt2.
\]

That manuscript's exact support inequality becomes

\[
F\ge\frac12\left(1+\frac AB\right)-\Delta A.
\]

Put \(h=H_S(e_x)=H_S(e_y)\le\sigma=1/\sqrt2\) and
\(K=F+H_S(n)\), reflecting the second coordinate if necessary.
Ray intersection gives \(|(C_S)_y|\le h\), and

\[
BK\ge B+A(1/2-\Delta B)>\sigma\ge h.
\]

Therefore the same strip minimization as in the cited proof is valid.
Its orientation-uniform outer support identity gives

\[
|C_S|^2\ge(\mathcal L(A)-h-\Delta)^2+h^2,
\quad
\mathcal L(A)=A+\frac1{2A}+\frac1{2\sqrt{1-A^2}}.
\]

The strengthened bound in `C7_INNER_SIDE_CORNER_RESTRICTIONS.md` is
\(\mathcal L>6163/3000\). In the present whole domain,

\[
\frac{6163}{3000}-e\frac{99}{70}
-\frac{99}{140}-\frac{127}{96}
=\frac{17}{33600}>0.
\]

Since \(\sqrt2<99/70\), \(\sigma<99/140\), and
\(\sqrt7/2<127/96\), this proves
\(\mathcal L-\Delta>\sigma+\sqrt7/2\). Minimizing over
\(h\le\sigma\) consequently gives \(|C_S|^2>9/4\).
This proves (14) in both radial sign regimes.

### 2.3. Consequences in an actual witness frame

Let \(\psi\in[0,\pi/4]\) be the angle between the witness center
direction and its nearest side axis. Actual containment in \(D_Q\)
gives

\[
\rho^2+\rho(\cos\psi+\sin\psi)+1/2\le Q,
\qquad
\cos\psi+\sin\psi<\frac{6468469}{5932000}<\frac{547}{500}.
\]

The first upper bound uses (14) and the decreasing function
\((Q-1/2)/\rho-\rho\). At \(\sin\psi=1/10\), the sum is
\(\sqrt{99/100}+1/10>547/500\), and it increases up to
\(\psi=\pi/4\). Hence

\[
\sin\psi<\frac1{10}.
\tag{15}
\]

If a separator is owned by this boundary unit, let \(n\) be its
normal toward \(S\), and let \(m\) be a perpendicular own axis.
Set

\[
z_n=n\cdot z>0,\quad z_m=m\cdot z,\quad
H=z_n+H_U(n),\quad \lambda=H/z_n.
\]

The positive inequality \(z_n>0\) follows from outgoing ray
membership. Separation gives \(n\cdot C_S\ge H+1/2>1\).
The minor own center coordinate has magnitude less than \(M/10\),
so this normal is the positive major own axis. Consequently

\[
n\cdot C_S>\rho_0\frac{99}{100}
=\frac{146817}{100000},\qquad
|m\cdot C_S|<\frac{91}{600}.
\tag{16}
\]

Separation and the ray's tangential strip also imply

\[
\boxed{H<\frac{61}{60},\qquad
|\lambda z_m|<\frac{391}{600}.}
\tag{17}
\]

Indeed any ray intersection has parameter at least \(\lambda\);
its tangential coordinate is within \(1/2\) of \(m\cdot C_S\).
The sign of \(z_m\) is fixed along the outgoing ray, proving the
second bound for either sign.

## 3. Every outgoing witness is the extracted far-face unit

Continue in the reflected own frame, so

\[
U=(a,b)+[-1/2,1/2]^2,\qquad
C_R=(a+1+\varepsilon,b-r).
\tag{18}
\]

The entire parameter domain is (8), (11). We retain both possible SAT
owners and all normal signs.

### 3.1. A separator owned by the inner unit

A rightward separator gives \((C_S)_x\ge a+1>37/25\).
An upward separator is impossible by actual corner containment, as
follows. Put

\[
A_0=a(1+1/(2b)),\qquad B_0=b+1/2.
\]

If \(h\) is the witness's coordinate halfwidth, separation and
ray membership give

\[
(C_S)_x\ge A_0-h,\qquad (C_S)_y\ge B_0+h.
\tag{19}
\]

Write its actual frame angle using
\(p\ge q\ge0\), \(p^2+q^2=1\), so \(h=(p+q)/2\).
For one chirality an actual corner has coordinates at least

\[
(A_0-q,\ B_0+p+q).
\]

Its projection on \((1,2)\) is at least
\(A_0+2B_0+2p+q\), where \(2p+q\ge2>4/\sqrt5\).
For the other chirality two actual corners have coordinates at least

\[
(A_0,\ B_0+p),\qquad
(A_0-p,\ B_0+p+q).
\]

Their corresponding projections are at least
\(A_0+2B_0+2p\) and \(A_0+2B_0+p+2q\).
On \(0\le q\le p\),

\[
\max(2p,p+2q)\ge\frac4{\sqrt5}:
\]

the minimum occurs where \(p=2q\); on either side the relevant
expression has its minimum at that endpoint. Thus in both chiralities
some actual corner \(w\) satisfies

\[
\begin{aligned}
w_x+2w_y
&\ge a+1+2b+\frac{a}{2b}+\frac4{\sqrt5}\\
&\ge a+1+2\sqrt a+\frac4{\sqrt5}
>\frac{581}{125}.
\end{aligned}
\tag{20}
\]

For the final rational bound use \(a>12/25\),
\(\sqrt a>69/100\), and \(4/\sqrt5>447/250\).
Cauchy's inequality yields

\[
|w|^2>\frac{(581/125)^2}{5}
=Q+\frac{87491}{20000000}>Q,
\]

contradicting actual containment. Negative coordinate normals cannot
separate an outgoing ray point from \(U\).

### 3.2. A leftward mixed-sign boundary-owned separator

Write \(n=(-v,u)\), \(m=(u,v)\), with \(u,v\ge0\).
The condition \(z_n=bu-av>0\) gives \(v/u<b/a\).
On this angular interval, \(au+bv\) increases from \(a\), and

\[
\lambda=1+\frac{u+v}{2(bu-av)}
\ge1+\frac1{2b}>\frac{11}{5}.
\]

Therefore

\[
|\lambda z_m|>\frac{11}{5}a>
\frac{132}{125}>\frac{391}{600},
\]

contrary to (17). This entire sign regime is impossible.

### 3.3. Positive-quadrant boundary-owned separators

Write \(n=(u,v)\), \(m=(-v,u)\), with \(u,v\ge0\).
We first show \(v<2/25\). Here

\[
H=(a+1/2)u+(b+1/2)v>
\frac{49}{50}u+\frac{17}{25}v.
\tag{21}
\]

If \(v\ge2/25\) and \(u\ge7/10\), the right side of (21)
is concave as a function of \(v\) on
\([2/25,\sqrt{51}/10]\). At its first endpoint it is greater than
\(32129/31250>61/60\), using
\(u\ge1-v^2=621/625\); at the other it is greater than
\((49/50+17/25)(7/10)>61/60\). This contradicts (17), so
\(u<7/10\).

If \(u\le3/10\), then \(v>19/20\), \(\lambda>2\), and

\[
av-bu>\frac{12}{25}\frac{19}{20}
-\frac5{12}\frac3{10}=\frac{331}{1000}.
\]

Consequently \(|\lambda z_m|>331/500>391/600\), again
impossible.

It remains to consider \(3/10\le u<7/10\). Put \(w=u+v\).
Concavity gives \(w>5/4\), and \(v>7/10\). If

\[
b\ge a\frac{v-3u/4}{u+3v/4},
\]

then

\[
H\ge\frac{a}{u+3v/4}+\frac w2
>\frac{12/25}{w-7/40}+\frac w2
\ge\frac{1843}{1720}>\frac{61}{60}.
\tag{22}
\]

The last nonconstant expression increases for \(w\ge5/4\), as
its derivative is \(1/2-(12/25)/(w-7/40)^2>0\); its value at
\(5/4\) is the displayed rational number. Thus the assumed inequality
on \(b\) fails, giving

\[
av-bu>\frac34(au+bv)>0.
\]

By (21) and angular concavity on \(3/10\le u\le7/10\),
\(H>47/50\): at \(u=3/10\) use \(v>19/20\), and at
\(u=7/10\) use \(v>7/10\). Hence

\[
|\lambda z_m|>\frac34H>\frac{141}{200}
>\frac{391}{600},
\]

the final contradiction. We have proved \(v<2/25\).

Since \(1-u\le v^2\), \(a+1/2<1\), and
\(b+1/2>17/25\), this also gives \(H\ge a+1/2\).
Thus \(n\cdot C_S\ge a+1>37/25\). Using (16),

\[
(C_S)_x\ge u(n\cdot C_S)-v|m\cdot C_S|
>\frac{37}{25}\frac{621}{625}
-\frac{91}{600}\frac2{25}>\frac{36}{25}.
\tag{23}
\]

### 3.4. Downward mixed-sign boundary-owned separators

Let \(n=(u,-v)=(\cos\varphi,-\sin\varphi)\) and
\(m=(v,u)\). On the whole domain \(au-bv>0\), put

\[
g=\lambda(av+bu)>0.
\]

Differentiation with respect to \(\varphi\) gives

\[
\lambda'=\frac{a+b}{2(au-bv)^2}>0,
\qquad g'=\lambda'(av+bu)+H>0.
\]

For \(0\le\varphi\le\pi/4\), we have

\[
\lambda'\ge\frac1{2a}+\frac{b}{2a^2}>
1+2b>\frac{34}{25},\qquad av+bu\ge b>\frac9{50}.
\]

Also

\[
H=(a+1/2)u+(1/2-b)v>
\frac{49}{50}u+\frac1{12}v>\frac34.
\]

The final inequality follows by concavity from the values at zero and
\(\pi/4\); at the latter, \((319/300)^2>9/8\).
Consequently \(g'>99/100\) on this interval, while

\[
g(0)=b(1+1/(2a))>2b>\frac9{25}.
\]

The upper bound \(g<391/600\) first excludes
\(\varphi\ge\pi/4\), using the monotonicity on the whole
domain. It then gives

\[
\varphi<\frac{100}{99}
\left(\frac{391}{600}-\frac9{25}\right)
=\frac{175}{594}<\frac3{10}.
\tag{24}
\]

From (16), \(\cos\varphi\ge1-\varphi^2/2\), and
\(\sin\varphi\le\varphi\), the actual center satisfies

\[
\begin{aligned}
(C_S)_x
&=u(n\cdot C_S)+v(m\cdot C_S)\\
&>\frac{146817}{100000}\frac{191}{200}
-\frac{91}{600}\frac3{10}>\frac43,
\end{aligned}
\tag{25}
\]

and

\[
(C_S)_y=-v(n\cdot C_S)+u(m\cdot C_S)
<\frac{91}{600}<\frac16.
\]

Its norm bound and (25) also give \((C_S)_y>-3/4\), because
\(M^2-16/9<9/16\). Therefore this entire sign regime lies in

\[
(C_S)_x>4/3,\qquad -3/4<(C_S)_y<1/6.
\tag{26}
\]

Normals with both coordinates negative have \(z_n\le0\) and are
impossible. All separator owners and signs have now been covered.

### 3.5. Uniqueness against the actual far-face center

The disk cap \(\{|x|^2\le M^2,\ x_1\ge36/25\}\) lies in
a disk of radius \(\sqrt{M^2-(36/25)^2}<1/2\), centered at
\((36/25,0)\). Its diameter is less than one. Thus the rightward
inner-owned and positive boundary-owned cases already force the witness
to be the actual unit with center \(C_R\), since
\((C_R)_x\ge a+1>37/25\).

For the remaining mixed-down case, (18), (1), (2), and (10) give

\[
(C_R)_x>37/25,\qquad
-\frac13<(C_R)_y=b-r
<\frac5{12}-\frac{17}{58}<\frac18.
\]

Together with (26), the horizontal center difference is less than
\(M-4/3=11/60\), and the vertical difference is less than
\(7/8\). Hence

\[
|C_S-C_R|^2<\left(\frac{11}{60}\right)^2+
\left(\frac78\right)^2=\frac{11509}{14400}<1.
\]

Two distinct physical unit squares have center distance at least one,
by their open radius-half inscribed disks. Thus this witness too is the
same actual boundary unit. We have proved, for the entire asymmetric
domain, that every outgoing witness is the far-face unit \(C_R\).

## 4. Two bounds on the same far center are incompatible

Because \(a>b\), the outgoing ray first leaves the inner square on
its right face, at height \(b(1+1/(2a))\). The just-proved witness
identity therefore gives, for the actual outer coordinate halfwidth
\(h_S\),

\[
r\le h_S-\frac{b}{2a}.
\tag{27}
\]

The center \(C_R\) has first coordinate at least \(a+1\) and
second coordinate of magnitude less than \(L=L(d)\). Its radial
angle from the first coordinate axis therefore has sine less than
\(L/(a+1)\). By (15), an own axis differs from that radial direction
by an angle with sine less than \(1/10\). The sum of these angles
is less than \(\pi/4\): each is below \(\pi/4\), and the sine
of their sum is less than
\(L/(a+1)+1/10<1/4+1/10<1/\sqrt2\).
Consequently

\[
h_S<\frac{11}{20}+\frac{L}{2(a+1)}=:h.
\tag{28}
\]

The strict norm bound gives \(b>r-L\). Combining it with
(27)--(28), we obtain

\[
\boxed{r<W(d):=
\frac{(11/10)a}{2a+1}+\frac{L}{a+1},
\qquad a=1/2-d.}
\tag{29}
\]

In the other direction, (27)--(28) and (2) imply

\[
P=1/2-b>1/2-2ah+2ar
>K(a)-3a\tau,
\]

where

\[
K(a)=\frac12-\frac a{10}-\frac{aL}{a+1}
>\frac12-\frac1{20}-\frac8{75}
=\frac{103}{300}.
\]

Substitution in the exact pair inequality (12) yields

\[
e-d>
\frac{103}{150}\tau-\frac{61}{20}\tau^2.
\tag{30}
\]

Here the actual quadratic coefficient before enlargement is
\(6a+d+e=3-5d+e<61/20\). The concave quadratic on the right of
(30) exceeds \(e\) throughout \([1/10,4/29]\): its endpoint
excesses are

\[
\frac{769}{36000}>0,
\qquad \frac{120383}{6055200}>0.
\]

Thus \(\tau<1/10\). For that smaller interval its coefficient is
greater than

\[
\frac{103}{150}-\frac{61}{200}
=\frac{229}{600}>\frac38.
\]

Therefore (30) and then (2) give

\[
\tau<\frac83(e-d),\qquad
\boxed{r>\frac12-4(e-d).}
\tag{31}
\]

It remains to compare (29) and (31), retaining all \(d\in(0,e)\).
The elementary function \(W\) is strictly concave on \([0,e]\).
Indeed

\[
W'(d)=-\frac{11/10}{(2a+1)^2}
+\frac1L+\frac{L}{(a+1)^2},
\]

\[
W''(d)=-\frac{22/5}{(2a+1)^3}
+\frac{M^2(2L^2-(a+1)^2)}{(a+1)^3L^3}<0,
\]

since \(L/(a+1)<(8/25)/(37/25)<1/4\). At zero,

\[
W(0)=\frac{11}{40}+\frac{\sqrt{181}}{90}<\frac{17}{40},
\]

\[
W'(0)=-\frac{11}{40}+\frac{8281}{135\sqrt{181}}
<\frac{43}{10}.
\]

The first bound uses \(\sqrt{181}<27/2\); the second follows from
\(\sqrt{181}>269/20\) and
\(165620/36315<183/40\). Concavity now gives

\[
r<W(d)<\frac{17}{40}+\frac{43}{10}d.
\tag{32}
\]

The upper bound in (32) is strictly below the lower bound in (31).
Indeed their difference is at most

\[
-\frac3{40}+4e+\frac3{10}e
=-\frac{197}{72000}<0.
\]

This contradiction excludes the entire asymmetric branch (3).

## 5. Exhaustive consequence and dependency scope

The two inner frames are either parallel, covered by
`PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md`, or nonparallel.
For a nonparallel pair choose any actual SAT owner as above. The
outside-coordinate cover gives either \(a\ge1/2\), excluded by
`C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md`, or exactly (3), excluded here.
No swap of separator ownership is used between those branches.

Thus the established C7 localization and center-polygon hypotheses,
the physical disk containment \(q\le Q\), and the audited strict
center-diameter bound imply that the central complementary region
contains at most one additional unit square. In particular, a selected
positive boundary C7 cannot be completed by two arbitrary
interior-disjoint unit squares in that declared domain.

The proof contains no regularity assumption, common-frame
normalization, numerical parameter cover, Lean compilation, or CI.
All endpoint limits and independent outer orientations remain in the
displayed inequalities.
