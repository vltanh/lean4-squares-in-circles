# Central-band geometry without a coefficient table

## Status and scope

This note proves all three one-square assertions used by
`../HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md` by whole-domain
polynomial identities and one completed-square estimate. It replaces all
19 Bernstein rows of `../CENTRAL_BAND_COMMON_POINT_LEMMAS.md`.
There is no subdivision of a position or angle interval, root isolation,
computed positivity assertion, or assumed PASS result in this proof.

The three alternatives below are three different geometric statements:
the transverse segment and the two central-depth bands. Within each
statement the same proof covers the entire closed angular domain.
The rational points used in Taylor's identity are expansion points, not
endpoints of a cover. In particular, no interval next to an expansion
point is assumed small.

Together with the analytic central-existence theorem at squared radius
`98/25` in `../HUMAN_GLOBAL_GEOMETRY_CLOSURE.md`, and the forbidden-width
calculus in `../HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md`, this
supplies a table-free proof of the central one-twelfth core at

\[
Q=\frac{9789}{2500}.
\]

This is a closure of the central-core part of G9. It does not supply the
unresolved frame, word, mismatch, or owner hypotheses of the sharp
terminal theorem.

All terminating decimals, where used to explain a rational number, are
exact rational numbers.

## 1. The three geometric assertions

Let a closed unit square be contained in the disk of squared radius
\(Q\), with the disk center at the origin. Make its center ray
horizontal. Choose and sign one of its axes, and reflect if necessary,
so that its center has own-frame coordinates

\[
(a,-b)=(r\cos\alpha,-r\sin\alpha),
\qquad 0\le\alpha\le\frac\pi4,\qquad a\ge b\ge0.
\tag{1}
\]

Containment implies the farthest-corner inequality

\[
(a+\tfrac12)^2+(b+\tfrac12)^2\le Q.
\tag{2}
\]

We prove the following assertions.

**Transverse segment.** If \(a>1/2\), then the entire closed segment

\[
\{(11/12,v): |v|\le7/20\}
\tag{3}
\]

lies in the open interior of the square.

**First central-depth band.** Suppose \(a>5007/10000\). If the center
ray makes an angle of absolute value at most \(3741/10000\) with a
fixed ray, then the point at distance \(10007/10000\) on that fixed
ray belongs to the square's open interior. Consequently two such
squares with disjoint interiors have smaller center angle strictly
greater than \(3741/5000\).

**Second central-depth band.** Suppose \(a\ge107/200\). If the
center ray makes an angle of absolute value at most \(19/50\) with
a fixed ray, the point at distance \(41/40\) on that ray belongs to
the square's open interior. Consequently two such squares with disjoint
interiors have smaller center angle strictly greater than \(19/25\).

The strict and weak assumptions on \(a\) are retained exactly as
stated. All angle endpoints, axis ties at \(\alpha=0,\pi/4\), and
endpoints of the transverse segment are included.

## 2. A common reduction to two polynomials

For \(0\le\theta\le\pi/2\), define \(\rho(\theta)>0\) by

\[
\rho^2+\rho(\cos\theta+\sin\theta)+\tfrac12=Q.
\tag{4}
\]

Equation (2) implies \(r\le\rho(\alpha)\), and
\(\rho(\pi/2-\alpha)=\rho(\alpha)\).

For constants \(A,C_-,C_+,D\), we will establish

\[
\rho(\theta)\cos\theta
 <\tfrac12+C_-\cos\theta-D\sin\theta
\quad(0\le\theta\le\pi/2),
\tag{5}
\]

and

\[
C_+\sin\alpha+D\cos\alpha-A\tan\alpha<\tfrac12
\quad(0\le\alpha\le\pi/4).
\tag{6}
\]

The constants will be these explicitly specified rational numbers:

\[
\begin{array}{ll}
\text{Segment:}&
 A=\frac12,\quad C_-=C_+=\frac{11}{12},\quad D=\frac7{20};\\[3pt]
\text{First band:}&
 A=\frac{5007}{10000},\quad C_-=\frac{23287}{25000},
 \quad C_+=\frac{93149}{100000},\quad D=\frac{3657}{10000};\\[3pt]
\text{Second band:}&
 A=\frac{107}{200},\quad C_-=\frac{4759}{5000},
 \quad C_+=\frac{119}{125},\quad D=\frac{3803}{10000}.
\end{array}
\tag{7}
\]

Thus the first-band cosine bounds are simply \(0.93148,0.93149\);
the second-band bounds are \(0.9518,0.952\). These slightly coarser
bounds make the argument shorter than the older coefficient appendix.

Put

\[
u=\tan(\theta/2),\quad z=1+u^2,\quad c=1-u^2,\quad s=2u,
\quad H=\tfrac12z+C_-c-Ds.
\]

Define

\[
P(u)=H^2z+Hc(c+s)+(\tfrac12-Q)c^2z,
\tag{8}
\]

and, using the same half-angle variable for \(\alpha\),

\[
V(u)=\tfrac12cz+Asz-C_+sc-Dc^2.
\tag{9}
\]

For every case in (7), \(D<1/2\), so the right side of (5) is
positive. The number \(X=\rho(\theta)\cos\theta\) is the
nonnegative root of

\[
X^2+X\cos\theta(\cos\theta+\sin\theta)
 +(\tfrac12-Q)\cos^2\theta=0.
\]

This expression increases for \(X\ge0\). Substitution of the right
side of (5), followed by multiplication by \(z^3>0\), gives (8).
Therefore \(P>0\) on the entire interval \([0,1]\) proves (5),
including \(\theta=\pi/2\).

Similarly, multiply the difference between the right and left sides
of (6) by \(\cos\alpha>0\), then by \(z^2>0\). The result is
(9). Since

\[
0\le\tan(\alpha/2)\le\sqrt2-1<\frac37,
\]

positivity of \(V\) on \([0,3/7]\) proves (6).

## 3. A whole-interval positive-remainder identity

Here is the elementary algebra used for all three sextics. Write
\(P(u)=\sum_{j=0}^6p_ju^j\), and fix any real expansion point \(a_0\).
Taylor division gives the exact polynomial identity

\[
P(u)=P(a_0)+P'(a_0)(u-a_0)+(u-a_0)^2R(u),
\tag{10}
\]

where \(R(u)=q_0+q_1u+q_2u^2+q_3u^3+q_4u^4\) and

\[
q_k=\sum_{j=k+2}^{6}(j-k-1)a_0^{j-k-2}p_j
\qquad(0\le k\le4).
\tag{11}
\]

Put \(L=q_2+q_3+q_4\). A second exact identity is

\[
\begin{aligned}
R(u)={}&q_0+(q_1+L)u-Lu(1-u)\\
 &-q_3u^2(1-u)-q_4u^2(1-u^2).
\end{aligned}
\tag{12}
\]

Every displayed factor \(u\), \(u(1-u)\), \(u^2(1-u)\), and
\(u^2(1-u^2)\) is nonnegative on the whole interval \([0,1]\).
Thus, when the coefficients in (12) are positive, it follows at once
that \(R\ge q_0\) everywhere on that interval. This is one
factorization on the full domain; it does not call for a basis check
on any subinterval.

For reproducible algebra, the coefficients of (8), with \(C=C_-\),
are

\[
\begin{aligned}
p_0&=(C+1)^2+\tfrac14-Q,\\
p_1&=1+2C-4D(C+1),\\
p_2&=Q+\tfrac34-(C+1)^2+4D^2-4D,\\
p_3&=-4C,\\
p_4&=Q-\tfrac14+2C-C^2+4D^2+4D,\\
p_5&=2C-1-4D+4CD,\\
p_6&=(C-1)^2+\tfrac14-Q.
\end{aligned}
\tag{13}
\]

These follow by expanding
\(H=(1/2+C)-2Du+(1/2-C)u^2\). Equations (11)--(13) derive all
coefficients in the next three identities directly from the geometry.
The integer coefficients are printed so that each identity can be
checked by multiplication and addition alone.

### 3.1. Segment

Take \(a_0=2/5\). The remainder has the identity

\[
\begin{aligned}
11250000R(u)={}&80651+5361332u+5659640u(1-u)\\
 &+24865400u^2(1-u)+41159875u^2(1-u^2).
\end{aligned}
\tag{14}
\]

All five coefficients are positive and
\(80651/11250000>1/200\). Moreover

\[
P(2/5)=\frac{1009541}{156250000}>\frac1{160},
\qquad
P'(2/5)=-\frac{11807}{11718750},\qquad
|P'(2/5)|<\frac1{800}.
\]

With \(x=|u-2/5|\), equations (10), (14) give

\[
\begin{aligned}
P(u)&>\frac1{200}x^2-\frac1{800}x+\frac1{160}\\
 &=\frac1{200}(x-\tfrac18)^2+\frac{79}{12800}>0.
\end{aligned}
\tag{15}
\]

### 3.2. First band

Take \(a_0=7/15\). The full-interval identity is

\[
\begin{aligned}
6328125000000R(u)={}&2036745397849+1029147845214u\\
 &+8456151284640u(1-u)\\
 &+16795576114200u^2(1-u)\\
 &+23166664513875u^2(1-u^2).
\end{aligned}
\tag{16}
\]

All coefficients are positive. Its constant term exceeds \(8/25\),
because the numerator of the difference is \(11745397849>0\) over
the displayed denominator. The remaining Taylor data are

\[
P(7/15)=\frac{1127543919953}{3559570312500000}
 >\frac3{10000},
\]

\[
P'(7/15)=\frac{304816277161}{26367187500000},
\qquad 0<P'(7/15)<\frac3{250}.
\]

With \(x=|u-7/15|\), we obtain

\[
\begin{aligned}
P(u)&>\frac8{25}x^2-\frac3{250}x+\frac3{10000}\\
 &=\frac8{25}(x-\tfrac3{160})^2+\frac3{16000}>0.
\end{aligned}
\tag{17}
\]

The positive constant in (17) holds on the entire quadrant, including
the place where the original first-band sextic had its smallest margin.

### 3.3. Second band

Take \(a_0=1/2\). Here the identity is

\[
\begin{aligned}
400000000R(u)={}&179518421+38557484u+660186260u(1-u)\\
 &+1133199440u^2(1-u)+1465310704u^2(1-u^2).
\end{aligned}
\tag{18}
\]

The constant term exceeds \(11/25\); the numerator of its difference
from \(11/25\) is \(3518421>0\). Also

\[
P(1/2)=\frac{1608241}{320000000}>\frac1{200},
\qquad
P'(1/2)=-\frac{21358779}{400000000},
\qquad |P'(1/2)|<\frac{27}{500}.
\]

With \(x=|u-1/2|\), this gives

\[
\begin{aligned}
P(u)&>\frac{11}{25}x^2-\frac{27}{500}x+\frac1{200}\\
 &=\frac{11}{25}(x-\tfrac{27}{440})^2
   +\frac{1471}{440000}>0.
\end{aligned}
\tag{19}
\]

Thus all three required outer-circle inequalities (5) are established
over the entire interval \(0\le\theta\le\pi/2\).

## 4. One curvature argument for all three quartics

Expansion of (9) gives the short formula

\[
V(u)=\tfrac12-D+2(A-C_+)u+2Du^2
       +2(A+C_+)u^3-(\tfrac12+D)u^4.
\tag{20}
\]

Consequently

\[
V''(u)=4D+12u\{A+C_+-(\tfrac12+D)u\}.
\tag{21}
\]

All three cases satisfy

\[
D\ge\frac7{20},\quad D<\frac25,\quad
A\ge\frac12,\quad C_+>\frac9{10}.
\]

For \(0\le u\le3/7\), the expression in braces in (21) is at
least

\[
\frac75-\frac9{10}\frac37=\frac{71}{70}>0.
\]

It follows that

\[
V''(u)\ge\frac75\qquad(0\le u\le3/7)
\tag{22}
\]

for all three cases. Integrate (22) twice from \(u_0=1/4\), or
apply convexity to \(V(u)-(7/10)u^2\). We obtain the whole-interval
bound

\[
V(u)\ge V(1/4)+V'(1/4)(u-1/4)
                  +\frac7{10}(u-1/4)^2
\ge V(1/4)-\frac5{14}V'(1/4)^2.
\tag{23}
\]

There are only three fixed substitutions into (20):

* For the segment,
  \(V(1/4)=27/1024\) and \(V'(1/4)=-1/192\).
  The final expression in (23) is greater than \(1/40\).
* For the first band,
  \(V(1/4)=15339/2560000\) and
  \(V'(1/4)=-2583/200000\).
  Here (23) is greater than \(1/200\).
* For the second band,
  \(V(1/4)=181/102400\) and \(V'(1/4)=313/6400\).
  Here (23) is greater than \(1/1250\).

For example, the last comparison follows already from
\(V(1/4)>7/4000\) and \(|V'(1/4)|<49/1000\):

\[
\frac7{4000}-\frac5{14}\left(\frac{49}{1000}\right)^2
 =\frac{357}{400000}>\frac1{1250}.
\]

For the other two, one may use respectively
\((V(1/4),|V'(1/4)|)>(26/1000,0)\) with
\(|V'|<6/1000\), and
\(V(1/4)>59/10000\) with \(|V'|<13/1000\), in (23).
These are plain rational comparisons at a single expansion point;
there is no positivity check elsewhere to perform.

This proves (6) for all three cases on the complete permitted angular
interval.

## 5. The two fixed trigonometric comparisons

For the first band put \(h=3741/10000\) and
\(\lambda=10007/10000\). For the second put \(h=19/50\) and
\(\lambda=41/40\). The constants (7) obey

\[
C_-<\lambda\cos h<C_+,
\qquad \lambda\sin h<D.
\tag{24}
\]

For completeness, these follow from the elementary alternating bounds

\[
1-\frac{h^2}{2}+\frac{h^4}{24}-\frac{h^6}{720}
 <\cos h<
1-\frac{h^2}{2}+\frac{h^4}{24}-\frac{h^6}{720}
 +\frac{h^8}{40320},
\]

\[
\sin h<h-\frac{h^3}{6}+\frac{h^5}{120}.
\tag{25}
\]

All arguments lie between zero and one, so the alternating terms
decrease. At \(h=3741/10000\), the lower cosine polynomial in (25)
exceeds \(9308368/10^7\), the upper is less than
\(9308369/10^7\), and the sine polynomial is less than
\(365436/10^6\). Multiplication by \(10007/10000\) gives
respectively

\[
\frac{23287}{25000}
 <\frac{10007}{10000}\frac{9308368}{10^7},
\quad
\frac{10007}{10000}\frac{9308369}{10^7}
 <\frac{93149}{100000},
\]

\[
\frac{10007}{10000}\frac{365436}{10^6}
 <\frac{3657}{10000}.
\]

At \(h=19/50\), the cosine bounds in (25) lie respectively above
\(9286/10000\) and below \(9287/10000\), and the sine bound is
less than \(371/1000\). Multiplication by \(41/40\) puts them
strictly between the respective bounds in (7). All these statements
are the indicated finite rational substitutions into the printed
degree-six, degree-eight, and degree-five polynomials; no transcendental
decimal value is a premise.

## 6. Four strict side inequalities

### 6.1. The whole transverse segment

For a point \((11/12,v)\), with \(|v|\le7/20\), its displacement
from the center in the square frame has coordinates

\[
d_e=\frac{11}{12}\cos\alpha+v\sin\alpha-a,
\quad
d_f=-\frac{11}{12}\sin\alpha+v\cos\alpha+b.
\]

The first upper bound uses \(a>1/2\) and

\[
(11/12)^2+(7/20)^2=\frac{1733}{1800}<1:
\qquad d_e<1-\frac12=\frac12.
\]

Apply (5) at \(\theta=\alpha\). Since \(a\le\rho\cos\alpha\),
it gives \(-d_e<1/2\), even for \(v=-7/20\).
Apply (5) again at \(\theta=\pi/2-\alpha\). The symmetry of
\(\rho\) gives

\[
b<\frac12+\frac{11}{12}\sin\alpha-\frac7{20}\cos\alpha,
\]

so \(d_f<1/2\), even for \(v=7/20\). Finally
\(b=a\tan\alpha\ge(1/2)\tan\alpha\), and (6) gives
\(-d_f<1/2\). Thus the whole closed segment lies in the open square.

### 6.2. Both angular bands

Let the center ray make angle \(\beta\in[-h,h]\) with the fixed
ray, and let \((\lambda,0)\) denote the point on that ray. In the
chosen square frame its displacement is

\[
d_e=\lambda\cos(\alpha+\beta)-a,
\qquad
d_f=-\lambda\sin(\alpha+\beta)+b.
\tag{26}
\]

For the first band \(\lambda-A=1/2\) and \(a>A\). For the
second, \(\lambda-A=49/100<1/2\) and \(a\ge A\). Therefore
\(d_e\le\lambda-a<1/2\) in both bands.

Since \(|\alpha+\beta|\le\alpha+h<\pi/2\),
\(\cos(\alpha+\beta)\ge\cos(\alpha+h)\). Equations (5), (24)
give

\[
a<\frac12+C_-\cos\alpha-D\sin\alpha
 \le\frac12+\lambda\cos(\alpha+h),
\]

so \(-d_e<1/2\).

At the complementary angle, (5), (24) give

\[
b<\frac12+C_-\sin\alpha-D\cos\alpha
 \le\frac12+\lambda\sin(\alpha-h).
\]

The sine is increasing throughout
\([-h,\pi/4+h]\subset(-\pi/2,\pi/2)\); hence
\(d_f<1/2\). Finally \(b=a\tan\alpha\ge A\tan\alpha\), so
(6), (24) yield

\[
-d_f\le\lambda\sin(\alpha+h)-b
 \le C_+\sin\alpha+D\cos\alpha-A\tan\alpha<\frac12.
\]

Thus both coordinates in (26) have absolute value strictly below
\(1/2\). This proves the two common-point assertions on their full
closed angular sectors. If two center rays had smaller angle at most
\(2h\), their bisector would make angle at most \(h\) with both.
The point at radius \(\lambda\) on that bisector would belong to both
open square interiors, a contradiction. The pair-angle conclusions
follow, with strict inequalities.

## 7. Consequence for the unrestricted central core

Here is the precise dependency substitution into the existing central
proof. The analytic two-circle theorem in
`../HUMAN_GLOBAL_GEOMETRY_CLOSURE.md` gives a unique square containing
the disk center in its open interior at squared radius at most \(98/25\).
At the smaller ceiling \(Q\), shifting the disk center to a nearest
central boundary point proves that the central depth
\(\delta=1/2-a\) is strictly greater than \(1/1000\): otherwise

\[
(\sqrt Q+\delta)^2
 <Q+\frac4{1000}+\frac1{10^6}
 <\frac{98}{25},
\]

contradicting the same central-existence theorem at that boundary point.

Every other square therefore has primary coordinate
\(A\ge1/2+\delta/\sqrt2>5007/10000\). When the central primary
coordinate is at most \(9/20\), its depth is at least \(1/20\),
giving \(A>107/200\).

The segment (3), rotated to an exterior square's center ray, lies in its
open interior by Section 6.1. It cannot meet the central closed square.
The geometric forbidden-width calculation in Sections 3--6 of
`../HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md` shows that a central
primary coordinate in \([5/12,9/20]\) forbids a connected interval of
ray directions of width greater than \(347/200\). The second-band
assertion proved here makes the six gaps between the seven remaining
rays exceed \(6(19/25)\). Their required total angle is greater than

\[
\frac{347}{200}+6\frac{19}{25}
 =\frac{1259}{200}>\frac{44}{7}>2\pi.
\]

For a central primary coordinate in \([9/20,1/2)\), that same
forbidden-width calculus gives width greater than \(899/500\), while
the first-band assertion makes the six gaps exceed
\(6(3741/5000)\). The required total is now greater than

\[
\frac{899}{500}+6\frac{3741}{5000}
 =\frac{7859}{1250}>\frac{44}{7}>2\pi.
\]

The forbidden-width calculation is already a calculus proof: its only
one-square positivity premises were precisely (5), (6), now proved
above. Its scalar trigonometric comparisons are displayed Taylor
substitutions at fixed geometric constants and contain no interval
cover. Thus no Bernstein row remains a premise in this argument.

Both central bands are impossible, so \(a<5/12\). In the central
square's own frame its other center coordinate has absolute value at
most \(a\). Every point of the closed radius-\(1/12\) disk then lies
strictly within \(1/2\) of its center in both frame coordinates.
The central square contains that closed disk in its open interior.

No other closed square can meet the disk: an alleged common point can
be approached by interior points of that square while staying inside
the central open square. Since a closed square is compact, its distance
from the origin is attained; that distance is consequently strictly
greater than \(1/12\). This proves the unrestricted central-core
conclusion, with exactly the radius ceiling needed by the sharp theorem.

## 8. Replacement boundary

For the central-core theorem, replace the invocation of the 19-row
appendix in `../CENTRAL_BAND_COMMON_POINT_LEMMAS.md` with Sections 1--6
of this note. The rest of the central geometry and the two-circle
central-existence proof apply unchanged as mathematical arguments.

No Lean source, generated certificate, compiler, or external verification
program is used in the proof above. Exact symbolic arithmetic was useful
for discovering and checking the three displayed factorizations, but
their positivity follows from the identities themselves. The proof does
not claim closure of the other G9 components or of the unrestricted
eight-square sharp bound.
