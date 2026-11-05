# A cap for five original squares

This chapter proves a five-square terminal using only the original physical
squares. The geometric preliminaries and the sharp weighted pair cap are
proved in [FOUNDATION.md](FOUNDATION.md). The complete outer estimates are
proved in [FIVE_SQUARE_CAP_OUTER.md](FIVE_SQUARE_CAP_OUTER.md). The central
transfer and the ordering argument are proved below by hand, without an
interval-cover certificate.

The conclusion applies whenever a caller establishes all of its displayed
five-square hypotheses. It does not itself assert that every nine-square
packing supplies such a caller.

## 1. The physical five-square theorem

Put

\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q,\qquad
 A=46,\qquad B=\frac{27}{2},\qquad T=\frac{211}{4},
\]

and

\[
 \rho_*:=\sqrt{Q-\frac14}-\frac12
         =\frac{\sqrt{1041}-8}{16}<\frac{91}{60}.
\]

For an original unit square \(V\), let \(H_V(w)\) be its centered support
in the vector \(w\), and let

\[
 h_V=H_V((1,0))=H_V((0,1)).
\]

Thus \(1/2\le h_V\le1/\sqrt2\). A square is called aligned when its
sides are parallel to the coordinate axes.

**Five-square cap theorem.** Let \(E_L,L,U,R,E_R\) be five distinct
physical unit squares with pairwise disjoint open interiors, all contained
in the centered closed disk of radius \(R_0\le r\). Assume

\[
\begin{aligned}
 E_R:&\quad \frac{89}{60}\le x_{E_R}\le\frac{91}{60},
       \quad |y_{E_R}|\le\frac18,\quad h_{E_R}\le\frac8{15},\\
 E_L:&\quad -\frac{91}{60}\le x_{E_L}\le-\frac{89}{60},
       \quad |y_{E_L}|\le\frac18,\quad h_{E_L}\le\frac8{15},\\
 L,R:&\quad -\frac{13}{12}\le x_L\le0\le x_R\le\frac{13}{12},
       \quad y_L,y_R\ge\frac35,\\
 U:&\quad |x_U|\le\frac{29}{60},
       \quad y_U-h_U\ge\frac1{10}.
\end{aligned}                                                    \tag{1}
\]

No frame, contact, or separating-axis owner is prescribed beyond these
conditions. Define the inward endpoint span

\[
 D=x_{E_R}-x_{E_L}-h_{E_L}-h_{E_R}.
\]

Then

\[
 \boxed{AD+B\le2T,\qquad\text{equivalently }D\le2.}                \tag{2}
\]

The inequality is strict if \(R_0<r\). At \(R_0=r\), equality holds
exactly for the following family, with all five squares aligned:

\[
\boxed{
 \begin{aligned}
 c_{E_L}&=(-3/2,-1/16),&c_{E_R}&=(3/2,-1/16),\\
 c_L&=(-1,15/16),&c_R&=(1,15/16),\\
 c_U&=(0,y),&&3/5\le y\le\rho_*.
 \end{aligned}}
                                                                  \tag{3}
\]

Vertical reflection gives the corresponding lower-side theorem. More
generally the coordinates may be taken in any fixed orthonormal frame.

## 2. Column separation supplies every central normal

### 2.1. Two high centers cannot lie in one narrow column

**Column lemma.** If two original interior-disjoint unit squares lie in
the \(Q\)-disk and both center heights are at least \(3/5\), then their
horizontal center distance is strictly greater than \(29/60\).

Suppose otherwise, and call the square with higher center \(V\). Put
\(h=h_V\). Its actual contained aligned inset has halfwidth
\(g=1/(4h)\), by FOUNDATION, Section A.3. The other original square
contains the open half-unit disk about its center. Its center must
therefore have distance at least \(1/2\) from the closed inset of \(V\).
This condition remains necessary when the original squares touch.

The center bound and the uppermost support give

\[
 y_V<\min\left(\frac{91}{60},\frac{133}{64}-h\right),
 \qquad \frac12\le h\le\frac1{\sqrt2}<\frac{17}{24}.
\]

Here \(r<133/64\) follows from \(17680<17689\), and the strict center
bound follows from

\[
 \left(\frac{91}{60}\right)^2+\frac{91}{60}+\frac12-Q
   =\frac{31}{57600}>0.
\]

For a closed row \([a,b]\) below, set

\[
 g_0=\frac1{4b},\qquad
 H_0=\min\left(\frac{91}{60},\frac{133}{64}-a\right).
\]

The two coordinate gaps from the other center to the inset are at most

\[
 \left(\frac{29}{60}-g_0\right)_+,
 \qquad \left(H_0-\frac35-g_0\right)_+.
\]

The following five rows cover the entire possible range of \(h\). Each
last entry is \(1/4\) minus the sum of the squares of these two gap bounds.

| Closed interval for \(h\) | \(g_0\) | \(H_0\) | Positive squared-distance reserve |
|---|---:|---:|---:|
| \([1/2,23/40]\) | \(10/23\) | \(91/60\) | \(14693/952200\) |
| \([23/40,3/5]\) | \(5/12\) | \(481/320\) | \(1643/184320\) |
| \([3/5,5/8]\) | \(2/5\) | \(473/320\) | \(13319/921600\) |
| \([5/8,13/20]\) | \(5/13\) | \(93/64\) | \(3232367/155750400\) |
| \([13/20,17/24]\) | \(6/17\) | \(457/320\) | \(1917191/266342400\) |

Every entry is obtained by substitution of the two displayed gap bounds;
all reserves are positive, including the shared interval endpoints. The
other center therefore has distance less than \(1/2\) from the inset,
contradicting physical interior nonoverlap. This proves the column lemma.

### 2.2. The central order and both directed signs

In (1), \(y_U\ge h_U+1/10\ge3/5\), so the column lemma applies to
all three central squares. If \(x_R\le x_U\), then both coordinates
belong to \([0,29/60]\), a contradiction. The reflected argument gives

\[
 x_L<x_U<x_R.
\]

All three center heights are below \(91/60\), so both relevant vertical
center differences have magnitude less than

\[
 \frac{91}{60}-\frac35=\frac{11}{12}<1.
\]

Take a genuine directed unit separating normal \(n\) from \(U\) to
\(R\), supplied by the physical separating-axis theorem. If \(n_x\le0\),
then, because \(x_R-x_U>0\),

\[
 n\mathbin{\cdot}(c_R-c_U)
 \le |n_y|\,|y_R-y_U|<1.
\]

The two support halfwidths sum to at least one, since each square contains
its centered half-unit disk. This contradicts separation. Hence \(n_x>0\).
Reflection gives the opposite strict sign for every directed separator
from \(U\) to \(L\). Dividing by the absolute horizontal component gives
the complete forms

\[
 m_R=(1,z_R),\qquad m_L=(-1,z_L),\qquad z_L,z_R\in\mathbb R.          \tag{4}
\]

This includes every original physical owner and every touching boundary.

## 3. A central transfer for all real slopes

Define the continuous piecewise linear function

\[
 \ell(z)=\frac{29}{2}z+\frac32\min(0,\max(-1,z)).                  \tag{5}
\]

Thus \(\ell(z)=29z/2\) for \(z\ge0\), \(\ell(z)=16z\) for
\(-1\le z\le0\), and \(\ell(z)=29z/2-3/2\) for \(z\le-1\).

**Central-transfer theorem.** Let \(L,U,R\) be three original
interior-disjoint unit squares in the \(Q\)-disk, with
\(y_U-h_U\ge1/10\), and suppose that (4) are genuine directed central
separators. Then

\[
 C:=H_U(m_L)+H_U(m_R)+(z_L+z_R)y_U
 \ge1+\frac{\ell(z_L)+\ell(z_R)}B.                              \tag{6}
\]

The inequality is strict unless \(z_L=z_R=0\). All supports and the
height on the left belong to the same original square \(U\). The physical
existence of \(L\) and \(R\) is retained; the assertion is not a statement
about an isolated central square.

### 3.1. Both central slopes nonnegative

Write z=z_L, q=z_R and assume z,q>=0. Put

    c=263/270, lambda=29/27=c+1/10, d0=61/60.

Since ell is linear on this quadrant, the required inequality is

    C>=1+(29/27)(z+q),                             (P1)

strictly unless both slopes vanish. The proof retains the physical L and R
through their two genuine separators; its necessary upper bound is the
reason that an isolated low central square is not a counterexample.

#### 3.1.1. The exact triangle minimum and physical upper bound

Write

    S=z+q, P=zq, d=sqrt(1+z^2), e=sqrt(1+q^2), Dsum=d+e.

For each fixed frame of U, the quantity

    S h_U+H_U(m_L)+H_U(m_R)

is the sum of the two orthogonal projection widths of the triangle
with vertices (0,0),(1,q),(0,S). Indeed a triangle's width in a
direction is half the sum of the absolute projections of its three
edge vectors. The three edges here are m_R, m_L, and (0,-S).

Between consecutive changes of the projected extreme vertices, the
sum of the two widths is a positive expression a_0 cos(theta)+b_0 sin(theta).
Its second derivative is the negative of the expression. Therefore its
minimum over frames occurs with an edge aligned to an axis. This also
covers degeneracies by continuity.

The vertical-edge candidate is 1+S. Aligning the edge of slope z gives

    (d^2+|P-1|+S(2+z))/(2d),

and the other candidate exchanges z,d with q,e. Thus the exact frame
minimum M has the following particularly simple form:

    P<=1: M=min(1+S, d+S/d, e+S/e),
    P>=1: M=min(1+S, S(z+1)/d, S(q+1)/e).        (P2)

The original whole-floor condition gives

    C>=M+S/10.                                  (P3)

There is also a necessary upper bound using the original L and R.
Every unit square contains its centered half-unit disk, and every
square in the Q-disk has center norm at most

    rho=sqrt(Q-1/4)-1/2<91/60.

The two actual central separating inequalities consequently give

    C <= (rho-1/2)(d+e) < d0 Dsum.                 (P4)

Define

    G1=M-1-cS, G2=M+S/10-d0 Dsum.

If G1>0, equation (P3) proves (P1) strictly. If G2>=0, equations
(P3)--(P4) contradict each other. We prove that at every S>0 one of
these alternatives holds.

#### 3.1.2. Every product P>=1 is physically impossible

Here S>=2 and

    de=sqrt((P-1)^2+S^2)<=P-1+S.

For either sloping-edge candidate in (P2), subtraction of Dsum gives

    S(z+1)/d-Dsum=(P+S-1-de)/d>=0

or its exchanged version. The vertical candidate also exceeds Dsum,
since

    (1+S)^2-Dsum^2=2(P+S-de)-1>=1.

Thus M>=Dsum. Moreover d<=1+z and e<=1+q, so

    Dsum<=S+2<=2S.

It follows that

    G2>=S/10-Dsum/60>=S/15>0.                      (P5)

This disposes of the entire product range P>=1 without a slope bound.

#### 3.1.3. The range P<1 and the short-sum region

By exchanging the two slopes, assume 0<=z<=q. Then d<=e and de>=S.
Consequently

    (d+S/d)-(e+S/e)=(d-e)(1-S/(de))<=0.

Put L0=d+S/d. Equation (P2) becomes

    M=min(1+S,L0).                              (P6)

If S<=1, the identity

    L0-1-S=(d-1)(d-S)/d>=0

shows M=1+S, so G1=(1-c)S>0 whenever S>0.

If 1<=S<=7/5, each candidate in (P2) is at least 2sqrt(S), by AM-GM.
The function 2sqrt(S)-1-cS is concave, and it is positive at both
ends of this interval. At S=1 its value is 7/270. At S=7/5 the
positive squared comparison is

    28/5-(3191/1350)^2=23519/1822500>0.

Hence G1>0 throughout this region as well.

For the remaining argument suppose G1<=0. Then necessarily

    S>7/5, M=L0, L0<=1+cS.                     (P7)

We next prove the additional restriction P>19/40.

#### 3.1.4. A short polynomial proves the product restriction

Suppose, to the contrary, P<=19/40. The case z=0 gives L0=1+S,
contradicting G1<=0. We may therefore assume z>0.

For fixed z, write

    L0-1-cS=d-1+(1/d-c)S.

If 1/d>=c this is strictly positive. Otherwise the expression
decreases with S. Since S=z+P/z<=z+19/(40z), it is enough to prove

    d+Sstar/d-1-c Sstar>0,
    Sstar=z+19/(40z).                           (P8)

Use the rational half-angle parameter

    t=z/(1+d), z=2t/(1-t^2), d=(1+t^2)/(1-t^2).

As z is the smaller slope, z^2<=P<=19/40<9/16. Therefore
0<t<1/3. Direct substitution gives the identity

    21600t(1-t^2)(1+t^2)[d+Sstar/d-1-c Sstar]=R(t),

where

    R(t)=133-9273t^2+43200t^3-64893t^4
                   +43200t^5-10127t^6.          (P9)

Here is a complete hand positivity proof on [0,1/3].

On [0,1/8],

    R'(t)=-t[18546-129600t
                  +t^2(259572-216000t)+60762t^4]<=0.

The bracket is positive: its first two terms are at least 2346,
and the other displayed terms are nonnegative. Also

    R(1/8)>133-145+84-16-1=55.

The omitted fifth-degree term is positive; the other bounds follow
directly from the denominators 64,512,4096,262144. Thus R>55 on
this first interval.

On [1/8,1/3], use

    R''(t)=-18546+259200t-778716t^2
                         +864000t^3-303810t^4,
    R''''(t)=-1557432+5184000t-3645720t^2.

The last expression increases on [0,1/3] and at 1/3 equals -234512.
Thus R'' is concave on the interval. Its endpoint values satisfy

    R''(1/8)>-18546+32400-12168+1687-75=3298,
    R''(1/3)>-18546+86400-86524+32000-3751=9579.

Consequently R''>3000 throughout [1/8,1/3]. The exact interior
values are

    R(1/4)=60065/4096>14,
    R'(1/4)=98355/512,  |R'(1/4)|<200.

Taylor's lower bound from R''>3000, followed by completing the square,
now gives throughout this interval

    R(t)>=R(1/4)+R'(1/4)(t-1/4)+1500(t-1/4)^2
         >=R(1/4)-R'(1/4)^2/6000
          >14-200^2/6000=22/3>0.

This proves (P8), contradicting G1<=0. Therefore the surviving range
in (P7) satisfies

    P>19/40.                                   (P10)

#### 3.1.5. The product restriction forces the physical contradiction

Still suppose G1<=0. By (P7), M=L0 and L0<=1+cS. The exact excess
of Dsum over L0 is

    delta=Dsum-L0=(de-S)/d
          =(1-P)^2/[d(de+S)].

Using d>=1, de>=S, and (P10), we obtain

    0<=delta<441/(3200S).

Hence

    G2=L0+S/10-(61/60)(L0+delta)
       > S/10-(1+cS)/60-(61/60)*441/(3200S)
       =1357S/16200-1/60-26901/(192000S).        (P11)

The last expression is strictly increasing for S>0. Since S>7/5,
its value exceeds its value at 7/5, namely

    8149/81000-26901/268800
       =19117/36288000>0.

Thus G2>0, contradicting the physical upper bound (P4). This proves
that G1<=0 cannot survive the original three-square hypotheses.

Every nonzero positive slope pair therefore satisfies G1>0, which
proves (P1) strictly by (P3). At z=q=0 the two support terms equal
2h_U>=1, proving the non-strict statement there as well.

### 3.2. At least one negative central slope

In this region a unary argument about the original central square suffices.
The following proof includes all mixed signs and both negative-tail branches.

Let U be one original unit square in the centered Q-disk, with center
(X,Y), coordinate halfwidth h, and whole floor Y-h>=1/10. All the
supports below belong to this same original U. For real z_L,z_R put

    m_L=(-1,z_L), m_R=(1,z_R), S=z_L+z_R,
    p=(z_L)_++(z_R)_+, n=(-z_L)_++(-z_R)_+,
    s=|S|, C=H_U(m_L)+H_U(m_R)+SY.

If at least one slope is negative, then

    C > 1+[ell(z_L)+ell(z_R)]/B.                         (N1)

At z_L=z_R=0 the corresponding non-strict statement is C=2h>=1.
No condition on the other two squares is required in this part of the
central transfer. The positive-quadrant part uses their genuine physical
separators and is proved separately.

We use the usual single-square containment facts

    Y+h<=r, |(X,Y)|<=rho=sqrt(Q-1/4)-1/2<91/60,
    r<133/64, H_U(w)>=|w|/2.

The last inequality follows from U's contained centered half-unit disk.
The rational radius comparison has squared reserve 9/4096.

#### 3.2.1. The central triangle and three complete hand bounds

For the triangle with vertices (0,0),(1,z_R),(0,S), its sum of widths
in the two orthogonal side directions of U is exactly

    s h+H_U(m_L)+H_U(m_R).

Indeed, for a direction u, the range of the three projected vertices is
half the sum of the absolute projections of their three edge vectors.
Adding this identity in U's two side directions gives the formula.

Let M be the least such sum of widths over all orthogonal frames. In an
interval of frame angles where each projected extreme vertex is fixed,
the sum is a positive function a_0 cos(theta)+b_0 sin(theta). Its second
derivative is its negative. Therefore its minimum occurs at an endpoint
of such an interval, where one frame direction is parallel to a triangle
edge. This proves the edge-alignment minimum, including degenerate
triangles by continuity.

Reflect vertically if needed so that S=s>=0. For a sloping-edge parameter
z (one of the reflected z_L,z_R), put d=sqrt(1+z^2). Its exact candidate is

    [d^2+|zs-d^2|+s(2+|z|)]/(2d).

The vertical-edge candidate is 1+max(p,n). For z>=0 the displayed
candidate is

    L(s,z)=max(d+s/d, s(z+1)/d).                        (N2)

For z<=0 it is d+s(1-z)/d. Thus M is the minimum of these three
edge-alignment candidates.

##### 3.2.1.1. The bound M>=1+s for mixed signs or s<=1

For d>=1,

    d+s/d-(1+s)=(d-1)(d-s)/d.

If s<=1, this is nonnegative. It bounds (N2) from below; it also bounds
the negative-z candidate from below. The vertical candidate is at least
1+s. This proves M>=1+s whenever s<=1.

For mixed signs, the nonnegative edge parameter after the reflection is
at least s, so its d is at least s and the same calculation applies.
For the nonpositive edge parameter, d>=1 and (1-z)/d>=1, so its
candidate is again at least 1+s. Therefore

    M>=1+s if z_L z_R<=0 or s<=1.                      (N3)

##### 3.2.1.2. The global bound M>=1+(9/10)s

The negative-z and vertical candidates already exceed this bound.
For z>0, the two branches in (N2) cross at s=d^2/z. The difference
L(s,z)-1-(9/10)s is affine before and after that crossing, and its
slope after the crossing is (z+1)/d-9/10>0. Its minimum over s>=0
is consequently at s=0 or at the crossing. At zero it is d-1>=0.
At the crossing its sign is the sign of

    (d-1)z+d-(9/10)d^2.

Divide by d^2 and put u=z/d, v=1/d. Since u,v>=0 and u^2+v^2=1,

    u+v-uv=1-[(u+v)-1]^2/2>=sqrt(2)-1/2>9/10.

The crossing value is therefore positive. The z=0 candidate is 1+s.
We have proved

    M>=1+(9/10)s                                    (N4)

on the entire slope plane.

##### 3.2.1.3. The same-sign tail M>=sqrt(s^2+2s) for s>=2

After reflection both edge parameters are nonnegative. The vertical
candidate is 1+s. To bound (N2) uniformly over z>=0, put

    z_-=(s-sqrt(s^2-4))/2, z_+=(s+sqrt(s^2-4))/2.

Then z_-<=1<=z_+, z_-z_+=1, z_-+z_+=s. The first branch d+s/d
is active outside [z_-,z_+]; its derivative is z(d^2-s)/d^3.
It is nonincreasing on [0,z_-] and nondecreasing on [z_+,infinity),
because at either endpoint d^2=sz and z_-<=1<=z_+.
Inside that interval the active branch is s(z+1)/d; its derivative
is s(1-z)/d^3. Its minimum is at an endpoint. Hence the global
minimum occurs at a crossing, where

    L(s,z)^2=s(z+1/z)+2s=s^2+2s.

Since (1+s)^2=s^2+2s+1, the vertical candidate is larger. Thus

    M>=sqrt(s^2+2s)                                  (N5)

for same-sign slopes and s>=2. This is the full hand proof of the
tail bound; no compact slope table enters it.

#### 3.2.2. Every negative magnitude is at most one

In this region the desired right side is

    1+(29/27)p-(32/27)n.                             (N6)

If S<=0, containment and (N4) give

    C>=M-rs>=1+(9/10-r)s.

Since n=p+s and r<133/64, its reserve over (N6) is at least

    p/9+(61/8640)s.

It is positive unless both slopes are zero.

If S>=0 and there is a negative slope, the signs are mixed. The actual
whole floor and (N3) give C>=M+S/10>=1+(11/10)S. Its reserve over (N6) is

    (7p+23n)/270>0.

This proves all cases in this section. In particular it proves the
nonpositive-sum part of the original linear transfer entirely by hand.

#### 3.2.3. One large negative slope and a nonnegative slope

Write the slopes -t,p with t>=1 and p>=0. The target in (N1) is

    8/9+(29/27)(p-t).

For S=p-t>=0, the whole floor and (N3) give C>=1+(11/10)S. Its reserve is
1/9+(7/270)S>0.

For S=-s<0 and s<=16, (N3) and Y+h<=r<133/64 give

    C>=1-(69/64)s.

The reserve is at least 1/9-(7/1728)s>=5/108>0.

For s>=16, the half-unit-disk support bound and Y<91/60 give

    C>p-(61/60)s,

because t=p+s. The reserve is at least

    p+(31/540)s-8/9>=4/135>0.

This covers every opposite-sign pair with a large negative magnitude.

#### 3.2.4. Both negative magnitudes at least one

Write the slopes -t,-u with t,u>=1 and s=t+u>=2. The target is

    7/9-(29/27)s.

For s>=16, the half-unit-disk and center bounds give C>-(61/60)s,
whose reserve is at least (31/540)s-7/9>=19/135>0.

For 2<=s<=16, use (N5) and put

    kappa=133/64-29/27=1735/1728=1+7/1728.

It suffices to prove sqrt(s^2+2s)>7/9+kappa s. Both sides are positive.
Their squared difference is a concave quadratic in s, since kappa>1.
At the two endpoints its exact values are

    s=2: 178319/746496,       s=16: 50471/11664.

Both are positive, so concavity proves the comparison throughout.

#### 3.2.5. One negative magnitude large and one small

Write the slopes -t,-u with t>=1 and 0<=u<=1, and let s=t+u.
The target is (8-u)/9-(29/27)s. For s>=16, the same center/support
bound has reserve at least (31/540)s-8/9+u/9>=4/135.

Suppose s<=16. It is enough to show that every candidate defining M is
strictly greater than

    kappa s+(8-u)/9.                                (N7)

The vertical candidate 1+s has reserve

    (1+u)/9-(7/1728)s>=5/108>0.

##### 3.2.5.1. Reduction to a reciprocal boundary

If tu<=1, both sloping candidates use the first branch in (N2). Also

    L(s,t)-L(s,u)=(d_t-d_u)[1-s/(d_t d_u)]>=0,

because t>=u and (d_t d_u)^2-s^2=(tu-1)^2>=0. It suffices to use
L(s,u)=d_u+s/d_u. For fixed u its reserve over (N7) decreases strictly
with t, since its t coefficient is 1/d_u-kappa<0.

For 0<=u<=1/16, apply d_u>=1 and 1/d_u>=1-u^2/2 directly, retaining
the actual s<=16. The reserve is at least

    1/9-(7/1728+1/512)16=13/864>0.

For 1/16<=u<=1, the reserve is bounded below by its value at t=1/u.

If tu>=1, both sloping candidates use the second branch in (N2).
The function f(z)=(z+1)/sqrt(1+z^2) obeys f(z)=f(1/z) and increases
on [0,1]. Since 1/t<=u<=1, one has f(u)>=f(t); it suffices to use
L(s,t)=s f(t). For fixed t its reserve over (N7) has u coefficient

    f(t)-kappa+1/9>=185/1728>0.

It is minimized at u=1/t. Since t<=s<=16, this reciprocal value
belongs to [1/16,1]. Thus both regions reduce to the same boundary.

##### 3.2.5.2. The reciprocal boundary, with two elementary bounds

At t=1/u, multiplication by u>0 reduces the required inequality to

    (1+u)sqrt(1+u^2)
       >kappa(1+u^2)+u(8-u)/9,  1/16<=u<=1.        (N8)

Both sides are positive. Put

    epsilon=kappa-1=7/1728<1/240,
    A(u)=1+(8/9)u+(8/9)u^2,
    C_0(u)=18-46u+34u^2+17u^3.

Eighty-one times the difference of the squares in (N8) is exactly

    u C_0(u)
      -162 epsilon(1+u^2)A(u)
      -81 epsilon^2(1+u^2)^2.                     (N9)

For 1/16<=u<=1/4, the function u C_0(u) is increasing. Its derivative
is 18-92u+102u^2+68u^3; that derivative is decreasing up to 1/4,
since its derivative is -92+204u+204u^2<=-113/4, and its value at
1/4 is 39/16>0. Consequently

    u C_0(u)> (1/16)(18-46/16)=121/128>15/16.

The two losses in (N9), using epsilon<1/240, sum to less than

    (27/40)(17/16)(23/18)+(9/6400)(17/16)^2
      =1173/1280+2601/1638400
      =1504041/1638400
      <1536000/1638400=15/16.

Thus (N9) is positive throughout this interval.

For 1/4<=u<=1, use u^3>=u^2/4. It gives

    C_0(u)-4>=14-46u+(153/4)u^2>0,

because this quadratic has positive leading coefficient and
discriminant 46^2-153*14=-26. The functions

    (1+u^2)A(u)/u
      =1/u+8/9+(17/9)u+(8/9)u^2+(8/9)u^3,
    (1+u^2)^2/u=1/u+2u+u^3

are convex on this interval. Their maxima occur at endpoints, giving

    (1+u^2)A(u)/u<=max(391/72,50/9)=50/9,
    (1+u^2)^2/u<=max(289/64,4)<5.

The total loss in (N9), divided by u, is therefore less than

    (27/40)(50/9)+(9/6400)5=15/4+9/1280<4.

It is smaller than C_0(u), so (N9) is again positive. This proves (N8)
on its whole closed interval, with strictness at every boundary.
No Bernstein coefficients are needed.

The reciprocal reduction and the separately checked vertical candidate
now prove all of Section 3.2.5. Sections 3.2.2--3.2.5 exhaust every negative or
mixed-sign slope pair and establish (N1).

## 4. Cancellation gives the five-square cap

Apply the proved outer-envelope theorem to \((E_R,R)\) and to the
horizontally reflected pair \((E_L,L)\). In the notation of (4), put

\[
\begin{aligned}
 F_R&=A(x_{E_R}-h_{E_R})
      +B\bigl[x_R+z_Ry_R-H_R(m_R)\bigr],\\
 F_L&=A(-x_{E_L}-h_{E_L})
      +B\bigl[-x_L+z_Ly_L-H_L(m_L)\bigr].
\end{aligned}
\]

Every hypothesis of that theorem is supplied by (1), and therefore

\[
 F_R\le T+\ell(z_R),\qquad F_L\le T+\ell(z_L).                    \tag{7}
\]

The two original central separators give

\[
 m_R\mathbin{\cdot}c_R-H_R(m_R)
 \ge m_R\mathbin{\cdot}c_U+H_U(m_R),
\]

and its left counterpart. Adding them cancels the central horizontal
coordinate exactly. Consequently

\[
 AD+BC\le F_L+F_R\le2T+\ell(z_L)+\ell(z_R).                       \tag{8}
\]

Substitution of the central transfer (6) proves \(AD+B\le2T\).
Because \(2T-B=92=2A\), this is exactly \(D\le2\).

If \(R_0<r\), both inequalities in (7) are strict, by the strict-radius
outer-envelope theorem. Thus \(D<2\). In particular, an actual four-chain
whose two original endpoints have \(D\ge2\) cannot coexist, in a strictly
smaller disk, with three original squares satisfying the central conditions
in (1).

## 5. The complete equality family for this five-square terminal

Suppose \(R_0=r\) and \(D=2\). If either central slope were nonzero,
the corresponding outer inequality in (7) would be strict, so (8) and
(6) would force \(D<2\). Hence \(z_L=z_R=0\).

Then \(C=2h_U\ge1\). Equality throughout (8) requires \(h_U=1/2\),
so \(U\) is aligned. Both outer inequalities are equalities in the
sharp weighted physical pair cap of FOUNDATION, Section B. Its equality
classification, with the shoulder heights positive as required by (1),
fixes the four original centers as

\[
 c_{E_L}=(-3/2,-1/16),\quad c_L=(-1,15/16),\quad
 c_R=(1,15/16),\quad c_{E_R}=(3/2,-1/16),
\]

and fixes all four frames as aligned. The two horizontal central separators
then give \(x_U\ge0\) and \(x_U\le0\), respectively. Thus \(x_U=0\).
The whole floor and disk containment give

\[
 \frac35\le y_U,\qquad
 \frac14+(y_U+1/2)^2\le Q,
\]

which are exactly the interval in (3).

Conversely, every member of (3) satisfies all five-square hypotheses.
The shoulders meet the central square only along the vertical lines
\(x=\pm1/2\), and each endpoint meets its adjacent shoulder only along
the horizontal line \(y=7/16\). The other pairs have separated horizontal
projections. Thus all open interiors are disjoint.

The farthest endpoint and shoulder corner norms are respectively

\[
 2^2+(9/16)^2=Q,\qquad
 (3/2)^2+(23/16)^2=Q.
\]

The central square is contained precisely because
\(1/4+(y_U+1/2)^2\le Q\). The endpoint inward span is \(3-1=2\).
This proves sufficiency and completes the terminal's equality classification.

## 6. Dependencies and scope

The proof uses the physical support, separating-axis, aligned-inset, and
center-radius facts in FOUNDATION; the outer envelopes in
FIVE_SQUARE_CAP_OUTER; and the explicit column and central-transfer
arguments above. The only finite numerical entries are displayed rational
hand bounds. No archived interval cover, certificate replay, numerical
search, Lean build, or CI run is a mathematical premise.

The theorem preserves all five original squares and their mutual physical
constraints. A nine-square application must still identify five distinct
originals satisfying (1), or prove a different terminal on the part of its
domain that does not supply them. Neither the existence of that caller nor
a classification of unrestricted nine-square equality is asserted here.
