# The centers of a boundary seven-cycle have diameter strictly less than three

**Status: complete hand implication; two separate hand audits passed.** Let seven interior-disjoint unit squares lie in a disk centered at the origin with

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\qquad Q=\frac{1105}{256},
\]

all touch the containing circle, and form a physical seven-cycle. Then every pair of their centers has distance strictly less than three.

This theorem uses the actual independently oriented squares and their angular shadows. It does not require a positive stress, a common orientation, or a regular ring. It closes the center-diameter upper bound only. The separate proposed implication that a cycle enclosing two unit squares must have two centers at distance at least three is still unproved; consequently this theorem alone does not close C7 completion.

We use the proved circular order of the centers and the fact that contacts join consecutive centers from `CIRCLE_CONTACT_ANGULAR_ORDER.md`. A square's angular shadow means the interval of polar angles of its points; all squares considered below avoid the origin.

## 1. Constants and the easy radius range

Put

\[
 R_0=\frac{\sqrt{17}}2,
 \qquad M=\frac{91}{60},
 \qquad m=3-M=\frac{89}{60},
 \qquad w=\arctan\frac{23}{16}.
 \tag{1}
\]

A circle-touching unit square with center radius r has, in a side frame making angle \(\psi\in[0,\pi/4]\) with its radial direction,

\[
 R^2=r^2+2rh+\frac12,
 \qquad
 h=\frac{\cos\psi+\sin\psi}{2}\ge\frac12.
 \tag{2}
\]

Thus \(r^2+r+1/2\le R^2\). If \(R<R_0\), every center has radius less than \(3/2\), and the theorem follows immediately.

Henceforth suppose \(R\ge R_0\). For every center,

\[
 r<M,
 \tag{3}
\]

because

\[
 \overline Q:=M^2+M+\frac12
 =\frac{15541}{3600}
 =Q+\frac{31}{57600}>Q.
 \tag{4}
\]

If two centers had distance at least three, both their radii would therefore be strictly greater than m. Only these possible endpoint squares need the refined estimates in Sections 3--4.

## 2. Every boundary square has angular shadow shorter than w

Choose a farthest circle corner as \(z=(a,b)\) in the square's side frame, after reflections and relabeling, so

\[
 S=[a-1,a]\times[b-1,b],
 \qquad a\ge b\ge\frac12,
 \qquad a^2+b^2=R^2.
 \tag{5}
\]

In particular a>1.

### 2.1. The case b>=1

The two extreme shadow rays pass through \((a-1,b)\) and \((a,b-1)\). Their angle \(\omega\) is acute, and

\[
 \tan\omega=\frac{a+b-1}{R^2-a-b}
 \le \frac{\sqrt2R-1}{R^2-\sqrt2R}.
 \tag{6}
\]

The last expression decreases with R. Indeed, writing \(L=\sqrt2R>2\), it is \(2(L-1)/(L(L-2))\), whose derivative has the sign of \(-L^2+2L-2<0\). At \(R=R_0\), the comparison with \(23/16\) is equivalent to

\[
 \sqrt{17/2}<\frac{35}{12},
\]

which follows from \(1224<1225\) after squaring with denominator 144. Therefore \(\omega<w\).

### 2.2. The case 1/2<=b<=1

The two extreme rays pass through \((a-1,b)\) and \((a-1,b-1)\). Thus

\[
 \tan\omega
 =\frac{a-1}{(a-1)^2-b(1-b)}
 =\frac{a-1}{R^2-2a+1-b}.
 \tag{7}
\]

The denominator is positive: here \(a\ge\sqrt{R_0^2-1}>9/5\), so it is greater than \((4/5)^2-1/4>0\). For fixed b, (7) decreases as a, and therefore R, increases. We may set \(R=R_0\).

At that radius, the desired strict comparison \(\tan\omega<23/16\) is equivalent to

\[
 62a+23b<\frac{547}{4}.
 \tag{8}
\]

Cauchy--Schwarz gives

\[
 (62a+23b)^2
 \le (62^2+23^2)\frac{17}{4}
 =\frac{74341}{4}
 <\left(\frac{547}{4}\right)^2,
\]

where the last squared difference is \(1845/16>0\). This proves (8).

We have shown, in all orientations,

\[
                       \boxed{\omega(S)<w.}
 \tag{9}
\]

## 3. The maximum half-shadow of a possible distant endpoint

Let an endpoint square have center radius \(m\le r\le M\). Rotate its center to \((r,0)\), and use a reflection and quarter turn to write its frame tilt as \(\psi\in[0,\pi/4]\). Put

\[
 h=\frac{\cos\psi+\sin\psi}{2},
 \qquad k=\frac{\cos\psi-\sin\psi}{2},
 \qquad h^2+k^2=\frac12.
 \tag{10}
\]

Its four vertices are

\[
 (r+k,h),\quad(r+h,-k),\quad(r-k,-h),\quad(r-h,k).
 \tag{11}
\]

Because \(r>1\ge h+k\), the largest absolute angular displacement of any vertex from the center ray is

\[
                    t(r,\psi)=\arctan\frac{h}{r-k}.
 \tag{12}
\]

For completeness, the lower ray through \((r-k,-h)\) dominates the other lower ray. It also dominates the upper ray through \((r+k,h)\) immediately. The remaining comparison is

\[
 \frac{k}{r-h}\le\frac{h}{r-k},
\]

which is equivalent to \((h-k)(r-h-k)\ge0\).

From (2), \(r\ge m\), and \(R^2\le Q\), we obtain

\[
 \frac12\le h<\frac{11}{20},
 \qquad \frac{11}{25}<k\le\frac12.
 \tag{13}
\]

Indeed,

\[
 m^2+2m\frac{11}{20}+\frac12-Q
 =\frac{179}{11520}>0,
\]

and \(k^2=1/2-h^2>79/400>(11/25)^2\).

In particular

\[
 \tan t\le\frac{11/20}{m-1/2}=\frac{33}{59},
 \qquad
 \tan w\tan t\le\frac{759}{944}<1.
\]

Consequently

\[
                         0<w+t<\frac\pi2.
 \tag{14}
\]

## 4. A common disk contains all possible endpoint sectors

This is the quantitative step. Define

\[
 t_0=\arctan\frac{1/2}{M-1/2},
 \qquad
 x_0=M\cos(w+t_0),
 \qquad
 y_0=M\sin(w+t_0).
 \tag{15}
\]

Explicitly,

\[
 x_0=\frac{26026}{60\sqrt{3627485}},
 \qquad
 y_0=\frac{171353}{60\sqrt{3627485}}.
 \tag{16}
\]

The bounds needed below are

\[
                    0<x_0<\frac14,
 \qquad 0<y_0<\frac32.
 \tag{17}
\]

For the first, \(\sqrt{3627485}>1900\) and \(4\cdot26026<60\cdot1900\). For the second, direct rational arithmetic gives

\[
 \frac94-y_0^2
 =\frac{20777891}{13058946000}>0.
 \tag{18}
\]

**Sector claim.** For every actual endpoint square covered by Section 3, and every angle \(0\le\delta\le w+t(r,\psi)\), both points

\[
            (r\cos\delta,\ \pm r\sin\delta)
 \tag{19}
\]

lie in the closed disk centered at \((x_0,0)\) with radius \(y_0<3/2\).

It is enough to prove the claim for \(\delta=w+t\), since \(x_0>0\) and (14) imply that the squared distance from \((x_0,0)\) increases with \(\delta\) on this interval.

### 4.1. Enlarge only the circle parameter

For a fixed frame tilt \(\psi\), let \(\bar r(\psi)\) be the positive solution of

\[
 \bar r^2+2\bar r h+\frac12=\overline Q,
 \tag{20}
\]

with \(\overline Q\) from (4). Since \(R^2\le Q<\overline Q\), the actual r is smaller than \(\bar r\). Also \(\bar r\le M\). Throughout the interval from r to \(\bar r\), all the bounds (13) hold and the radius remains in \([m,M]\).

Write

\[
 D=(r-k)^2+h^2>\frac65,
 \qquad \alpha=w+t(r,\psi),
\]

where the lower bound follows from

\[
 D\ge(m-1/2)^2+1/4=\frac{4381}{3600}>\frac65.
 \tag{21}
\]

The squared distance in question is

\[
 E(r,\psi)=r^2-2x_0r\cos\alpha+x_0^2.
 \tag{22}
\]

At fixed \(\psi\), \(\partial t/\partial r=-h/D\), and therefore

\[
 \frac{\partial E}{\partial r}
 =2(r-x_0\cos\alpha)-2x_0r\sin\alpha\frac hD.
 \tag{23}
\]

Here \(h/D<1/2\). Using (13), (17), (21), and \(0<\alpha<\pi/2\), we obtain

\[
 \frac{\partial E}{\partial r}
 >2(m-1/4)-\frac M4
 =\frac{167}{80}>0.
 \tag{24}
\]

Thus it suffices to bound E on the auxiliary curve (20).

### 4.2. The auxiliary endpoint curve moves strictly into the disk

Along (20), regard r as a function of \(\psi\). Since \(h'=k\) and \(k'=-h\),

\[
 r'=-\frac{rk}{r+h},
 \qquad
 \frac3{10}<-r'<\frac12.
 \tag{25}
\]

For the lower bound, use

\[
 \frac{rk}{r+h}
 >\frac{m(11/25)}{M+11/20}
 =\frac{979}{3100}>\frac3{10}.
\]

Differentiating (12) on the same curve gives

\[
 t'=\frac{rk-1/2-hr'}D.
 \tag{26}
\]

Its numerator is positive, since \(rk>m(11/25)>1/2\). Also

\[
 0<t'
 <\frac{M/2-1/2+(11/20)/2}{6/5}
 =\frac49.
 \tag{27}
\]

Using (22), (25), and (27),

\[
\begin{aligned}
 \frac{dE}{d\psi}
 &=2r'(r-x_0\cos\alpha)+2x_0r\sin\alpha\,t'\\
 &< -\frac35(m-1/4)+\frac M2\frac49\\
 &= -\frac{272}{675}<0.
\end{aligned}
 \tag{28}
\]

When \(\psi=0\), equation (20) has \(r=M\), and (15) gives

\[
 E(M,0)=y_0^2.
\]

For any tilt up to the actual endpoint tilt, the auxiliary curve stays in the range used above: h increases from 1/2, k decreases, and r decreases from M to \(\bar r\ge r_{\rm actual}\ge m\). Therefore (28) applies throughout. Equations (24) and (28) prove

\[
 E(r_{\rm actual},\psi)\le y_0^2.
\]

This proves the sector claim (19).

## 5. Three contacts cannot join centers at distance three

Suppose that four consecutive boundary squares \(S_0,S_1,S_2,S_3\) along the ring have endpoint centers at distance at least three. By Section 1, both endpoint radii exceed m. Let their lifted center angles be

\[
 \alpha_0<\alpha_1<\alpha_2<\alpha_3
\]

in the circular order. Choose lifted contact angles \(\theta_j\) at the contact between \(S_j\) and \(S_{j+1}\), for \(j=0,1,2\). Such common lifts exist because each consecutive center gap is less than \(2\pi/5\), while the contacting shadows intersect and each shadow has width less than w.

Let \(t_0,t_3\) be the maximum endpoint half-shadows from (12). Telescoping through the three contact angles gives

\[
\begin{aligned}
 \alpha_3-\alpha_0
 &=(\theta_0-\alpha_0)+(\theta_1-\theta_0)
   +(\theta_2-\theta_1)+(\alpha_3-\theta_2)\\
 &< t_0+2w+t_3.
\end{aligned}
 \tag{29}
\]

The two middle differences are bounded above by their respective square-shadow widths. They need not be positive for this estimate.

By (14), the right side of (29) is less than \(\pi\). Put \(\gamma=\alpha_3-\alpha_0\), and choose nonnegative \(\delta_0,\delta_3\) with

\[
 \delta_0+\delta_3=\gamma,
 \qquad \delta_j\le w+t_j.
 \tag{30}
\]

This is possible by (29). Rotate the reference axis so the two centers have angles \(-\delta_0\) and \(+\delta_3\). The sector claim places both actual centers in one disk of radius \(y_0<3/2\), centered at \((x_0,0)\) in this rotated frame. Their distance is at most \(2y_0<3\), contrary to the assumption.

Hence the centers at the ends of every three-edge ring path have distance less than three.

## 6. Complete diameter conclusion

Every pair of vertices of a seven-cycle is joined by a path of at most three edges. For one or two edges, the center-distance bound follows directly from

\[
 |C_i-C_{i+1}|\le\sqrt2,
 \qquad 2\sqrt2<3,
\]

since touching unit squares have a common point and each center is within \(1/\sqrt2\) of that point. Three edges are covered by Section 5. Together with the easy range \(R<R_0\), this proves

\[
                  \boxed{\max_{i,j}|C_i-C_j|<3.}
\]

The remaining C7 capacity problem still requires a separate actual-square argument excluding two interior completion squares. No such extraction or origin-piercing theorem is inferred here.
