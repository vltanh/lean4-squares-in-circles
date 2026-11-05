# Physical geometry and sharp cap terminals

This chapter is a self-contained hand-proof foundation for the nine-square
problem. It consolidates the retained physical weighted cap, directional
center capture, and sharp half-plane cap, and gives their endpoint and
weak-middle consequences. The assertions concern the original squares,
with independent frames and boundary contacts allowed. No numerical search,
archived certificate, Lean theorem, common frame, or contact graph is an
input. The unrestricted all-nine routing implication is not asserted here.

Put \(Q=1105/256\) and \(r=\sqrt Q=\sqrt{1105}/16\). All disks are
centered at the origin after translation. Equations are numbered locally
within Parts B, D, and E. Their locally introduced letters are not shared
between parts.

## A. Physical preliminaries

### A.1. Squares, supports, and disk containment

For each label i let

\[
 S_i=c_i+[-1/2,1/2]u_i+[-1/2,1/2]v_i,
 \qquad |u_i|=|v_i|=1,\quad u_i\cdot v_i=0.
\]

Every frame is independent. For an arbitrary vector w set

\[
 h_i(w)=\frac{|w\cdot u_i|+|w\cdot v_i|}{2}.
\]

Maximizing the two independent frame coordinates proves that the support
of S_i in direction w is \(w\cdot c_i+h_i(w)\). Thus h_i is positively
homogeneous and even. For unit w, the elementary inequalities
\(1\le |w\cdot u_i|+|w\cdot v_i|\le\sqrt2\) give
\(1/2\le h_i(w)\le1/\sqrt2\).

The square is the convex hull of its four corners, and the disk is convex.
Consequently corner containment and whole-square containment are equivalent.
In the square's own frame, write \(\alpha=c_i\cdot u_i\) and
\(\beta=c_i\cdot v_i\). The largest squared corner radius is exactly

\[
 (|\alpha|+1/2)^2+(|\beta|+1/2)^2
 =|c_i|^2+|\alpha|+|\beta|+1/2.
 \tag{A1}
\]

In particular a square in a disk of radius R satisfies, for every w,

\[
 w\cdot c_i+h_i(w)\le R|w|.
 \tag{A2}
\]

### A.2. Physical separating axes

For two squares with disjoint open interiors, there is a signed unit vector
n parallel to a side axis of at least one square such that

\[
 n\cdot(c_j-c_i)\ge h_i(n)+h_j(n).
 \tag{A3}
\]

Conversely (A3), for any unit vector n, ensures disjoint open interiors.
To prove the forward direction, let K_i=S_i-c_i and K_j=S_j-c_j.
Their Minkowski sum \(K_i+K_j\) is a centrally symmetric convex polygon;
its edge directions are side directions of the two squares. The two open
interiors intersect exactly when \(c_j-c_i\) belongs to the interior of
this sum. Here is an elementary justification of the interior-of-sum step.
Choose interior points k_0 and l_0 and put w=k_0+l_0. If z belongs to the
interior of K_i+K_j, then, for t>1 sufficiently close to one,
\(z'=w+t(z-w)\) still belongs to that sum. Write z'=k'+l'. Then
\(z=(1-1/t)(k_0+l_0)+(k'+l')/t\) is a sum of two interior
points: each lies strictly along a segment from an interior point to a
point of its convex polygon. The reverse inclusion is immediate from
open neighborhoods. Thus nonintersection violates or saturates a facet
inequality of the sum.
The outward normal of that facet is a signed side axis of one original,
and its support is \(h_i(n)+h_j(n)\). This proves (A3), including equality.

This criterion uses the actual frames. It does not assert separation along
either axis of an arbitrarily chosen auxiliary coordinate system.

### A.3. Aligned insets and cone comparisons

Fix an auxiliary orthonormal coordinate system. A square has the same
horizontal and vertical projection halfwidth h. Write its absolute axis
components as \(a\ge b\ge0\), where \(a^2+b^2=1\). Then

\[
 h=(a+b)/2,\qquad k=(a-b)/2=\sqrt{1/2-h^2},
 \qquad g=\frac1{4h}.
\]

The concentric coordinate-aligned square of halfwidth g is contained in the
physical square. In fact each of its own-frame coordinates has absolute
value at most \(g(a+b)=2hg=1/2\). Strict inequalities hold on the open
inset. Therefore two originals with disjoint open interiors have insets with
disjoint open interiors.

In particular if \(d=x_j-x_i>0\) and \(|y_j-y_i|\le d\), then

\[
 d\ge g_i+g_j.
 \tag{A4}
\]

Otherwise both coordinate differences are smaller than the sum of the
inset halfwidths, and the open inset rectangles intersect. The inset is
only a necessary-condition device; disjoint insets do not establish
nonoverlap of the originals.

### A.4. A sharp center-radius bound and a useful rational bound

For a square contained in the closed Q-disk, the inequality
\(|\alpha|+|\beta|\ge\sqrt{\alpha^2+\beta^2}=|c|\) and (A1) give

\[
 Q\ge |c|^2+|c|+1/2,
 \qquad |c|\le\rho_*:=\frac{\sqrt{1041}-8}{16}<\rho:=\frac{91}{60}.
 \tag{A5}
\]

The last inequality follows by substitution into the increasing quadratic:

\[
 \rho^2+\rho+1/2-Q=\frac{31}{57600}>0.
\]

The exact bound is attained by an aligned square centered at
\((\rho_*,0)\). The rational bound is strict even for squares touching
the Q-circle.

Every square also contains its radius-1/2 incircle, so physical
nonoverlap implies \(|c_i-c_j|\ge1\). This latter condition is weaker
than (A3) and is not substituted for physical nonoverlap in the caps below.

### A.5. Strictification by expanding centers

Suppose finitely many originals fit strictly inside the Q-disk. For t>1
replace c_i by tc_i and retain every frame. Each chosen inequality (A3)
becomes strict because its right side is positive. Hence the resulting
closed squares are pairwise disjoint. The finitely many corner norms vary
continuously with t, so sufficiently small t−1 preserves strict Q-disk
containment. If every original lies above a positive line y=b_0, this
property is preserved because its center satisfies Y_i>0 and

\[
 tY_i-h_i=(Y_i-h_i)+(t-1)Y_i\ge b_0.
\]

This argument justifies use of closed marker points in a strict lower-bound
proof. At equality, boundary sharing must instead be analyzed explicitly.

### A.6. The horizontal-section formula

In centered auxiliary coordinates, use a reflection if necessary to write
the square's side axes as (a,b), (−b,a), where a≥b≥0 and a²+b²=1.
For b>0 its section at vertical offset t≥0 is the intersection of

\[
 \left[\frac{-1/2-bt}{a},\frac{1/2-bt}{a}\right]
 \quad\hbox{and}\quad
 \left[\frac{at-1/2}{b},\frac{at+1/2}{b}\right].
\]

The first interval supplies the upper endpoint. Its lower endpoint is
the larger one precisely when t≤j=(a−b)/2, as follows by multiplying
by ab>0 and using a²+b²=1. Thus the length is

\[
 \ell(t)=
 \begin{cases}
 1/a,&|t|\le j,\\
 (h-|t|)/(ab),&j\le |t|\le h,
 \end{cases}
 \qquad h=(a+b)/2.
 \tag{A6}
\]

Negative offsets follow by central inversion. When b=0, the aligned
square has section length one for |t|≤1/2. In all cases
\(|t|<h-ab\) puts the line strictly between the extreme heights and
makes the section length at least one. For b>0 the length is strictly
greater than one: the first regime has a<1, and the second follows by
substitution into (A6).

Writing z=a+b in [1,√2] also gives the two bounds used later:

\[
 h-ab=\frac{1+z-z^2}{2}\ge\frac{\sqrt2-1}{2},
 \qquad
 2h-ab=z-\frac{z^2-1}{2}\ge\sqrt2-\frac12.
 \tag{A7}
\]

Each polynomial decreases on this interval, so evaluation at √2 proves
the inequalities, including both endpoints.

## B. The physical weighted two-square cap

The following proof includes the triangle bounding-rectangle reduction,
every owner case, the complete four-interval table, and all endpoints.
It consolidates Sections 1–7 of the retained
[physical weighted cap manuscript](sources/PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md).
All mathematical inputs are proved in this chapter.

### 1. The two-square theorem

Write

    Q=1105/256,  r=sqrt(Q),
    a=46,  b=27/2,  k=207/16,  T=211/4.

For a unit square S centered at c_S, let h_S(e) be its projection halfwidth
in a unit direction e. Its support function about its center is

    h_S(v)=(|v.u_S|+|v.v_S|)/2

for arbitrary vectors v, so h_S is positively homogeneous. Fix any unit e.

**Theorem 1.** If M and B are two actual unit squares with disjoint open
interiors, both contained in a disk centered at zero of radius R<=r, then

    a[-e.c_M-h_M(e)] + b[-e.c_B-h_B(e)] <= T.             (1)

The inequality is strict if R<r. Equality requires both squares to be aligned
with e and its perpendicular. In coordinates with e=(1,0), their centers are

    c_M=(-3/2, sigma/16),
    c_B=(-1,-15 sigma/16),       sigma in {-1,1}.          (2)

Conversely these two squares attain equality in (1) at R=r.

The squares may initially have unrelated orientations. Neither touches the
other or the circle by hypothesis. There is no stress, graph, degree, extra
square, or common separating-frame assumption.

### 2. Reduction to a scalar support inequality

The separating-axis theorem for two rectangles gives a signed unit normal n,
parallel to an axis of at least one of M,B, such that

    n.(c_B-c_M) >= h_M(n)+h_B(n).                         (3)

For completeness, the Minkowski difference of the two centered rectangles
is a convex polygon whose sides are parallel to their side directions.
Interior nonintersection says c_B-c_M is outside the interior of that
polygon. A separating facet inequality, including its boundary, has a normal
perpendicular to a side of one of the rectangles. This proves (3).

Set c=e.n and s=sqrt(1-c^2). Reflection in e permits s>=0. Define

    L_a(c)=sqrt(a^2+k^2+2ak c),
    L_b(c)=sqrt(b^2+k^2-2bk c),
    H(c)=r[L_a(c)+L_b(c)].                               (4)

For every vector v, containment gives

    v.c_S+h_S(v) <= R|v|.

Use v_M=-ae-kn and v_B=-be+kn, add, and use (3). The left side
of (1) is at most

    R[L_a+L_b]-P_M-P_B <= H(c)-P_M-P_B,                 (5)

where

    P_M=a h_M(e)+h_M(ae+kn)+k h_M(n),
    P_B=b h_B(e)+h_B(be-kn)+k h_B(n).                    (6)

If R<r, the second inequality in (5) is strict since L_a+L_b>0.

#### 2.1 A three-direction rectangle lemma

For w>k>0 and e.n=c, the quantity

    w h_S(e)+h_S(we+kn)+k h_S(n)

is the sum of the two side lengths of the bounding rectangle of the triangle
with vertices 0,we,-kn in the frame of S. Indeed in each frame coordinate,
half the sum of the absolute projections of the three triangle edges equals
the projection range of its three vertices.

The minimum of this sum over frames occurs when one triangle edge is parallel
to a frame axis. Between successive changes of the extreme projected vertex,
the sum is a positive function A cos(theta)+B sin(theta), whose second
derivative is its negative. It has no interior minimum on such an interval.
There are finitely many extreme-vertex changes; at each change an edge is
parallel to a frame axis. The degenerate line triangles follow directly.

Consequently this quantity is at least min(E_w,N_w,D_w), where, with
L=sqrt(w^2+k^2+2wk c),

    E_w(c)=w+k[s+max(c,0)],

    N_w(c)= k+w(c+s)        if c>=0,
             k+w s         if -k/w<=c<=0,
             w(s-c)        if c<=-k/w,

    D_w(c)= L+wk s/L                      if c>=-k/w,
             w(w+kc+ks)/L                 if c<=-k/w.   (7)

These are the bounding rectangles parallel to e,n,we+kn, respectively.
All denominators are positive because w>k. If S owns the separating normal
n, its value is exactly N_w(c), without taking a minimum.

Thus it suffices to prove the following five scalar inequalities, since the
normal is owned by at least one square:

    H(c)-N_a(c)-E_b(-c) <= T,
    H(c)-N_a(c)-N_b(-c) <= T,
    H(c)-E_a(c)-N_b(-c) <= T,
    H(c)-N_a(c)-D_b(-c) <= T,
    H(c)-D_a(c)-N_b(-c) <= T.                            (8)

The sixth ownership entry duplicates the N_a,N_b entry. Every inequality is
strict unless c=0; the D entries are strict at c=0 as well.

### 3. Constants and reusable scalar estimates

The following identities will be used throughout:

    k/a=9/32,        k/b=23/24,
    a+k=943/16,     b+k=423/16,
    a+b=119/2,      a+b+2k=683/8,
    L_a(0)=23r,     L_b(0)=9r,
    H(0)=1105/8,    H'(0)=k/2,
    H(0)-(a+b+2k)=T,
    r<133/64<25/12<9/4.                                (9)

The first radius bound follows from 1105*16=17680<17689=133^2.
Direct differentiation gives

    H''(c)=-r k^2[a^2/L_a(c)^3+b^2/L_b(c)^3]<0.          (10)

In particular

    H(c)<=H(0)+(k/2)c.                                  (11)

Put c0=23/24. For c>=c0,

    L_a<=a+k,
    L_b=sqrt(b^2 s^2+(bc-k)^2)<=bs+bc-k,

and hence

    H(c)<=r[a+b(c+s)].                                  (12)

The endpoint expression

    (r-1)(a+b)-k < 6555/128 < T                         (13)

follows from r<133/64.

#### 3.1 The only convexity table

On 0<=c<=c0 the function

    F(c)=H(c)-[a+k+kc+(b+k)s]                            (14)

is strictly convex. Here is a complete rational check.

Write A(c)=a^2 k^2(s/L_a)^3 and B(c)=b^2 k^2(s/L_b)^3.
A decreases on [0,c0], and B increases on that interval: the derivatives of
s/L_a and s/L_b have respective numerator signs

    -(a+kc)(k+ac),       (b-kc)(k-bc).

Both denominators are positive. The following table bounds A+B on four
closed intervals; endpoint formulas cover shared boundaries.

| c interval | bound on A | bound on B | bound on A+B |
| --- | ---: | ---: | ---: |
| [0,1/2] | 7/2 | 9 | 25/2 |
| [1/2,3/4] | 8/5 | 11 | 63/5 |
| [3/4,7/8] | 3/5 | 12 | 63/5 |
| [7/8,23/24] | 1/4 | 1587/128 | 1619/128 |

Every bound is strict except the last upper bound on B, and every row sum
is less than 38/3. To verify the entries without any hidden arithmetic:

    a^2 k^2<356000,    b^2 k^2<30600.

The second follows from k^2<335/2 and (729/4)(335/2)<30600.
Use the following lower bounds for the positive L's and upper bounds for s^3:

| c | lower L_a | lower L_b | upper s^3 |
| --- | ---: | ---: | ---: |
| 0 | 47 | -- | 1 |
| 1/2 | 107/2 | 66/5 | 21/32 |
| 3/4 | 56 | 187/20 | 7/24 |
| 7/8 | 57 | 53/8 | 465/4096 |

The square comparisons use the exact L_a^2 values
584545/256, 736897/256, 813073/256, 851161/256 and the L_b^2
values at the last three rows 44793/256, 22437/256, 11259/256.
The bounds on s^3 use sqrt(3)<7/4, sqrt(7)<8/3, sqrt(15)<31/8.
For the displayed A and B entries the resulting comparisons are

    356000/47^3 < 7/2,
    356000(21/32)/(107/2)^3 < 8/5,
    30600(21/32)/(66/5)^3 < 9,
    356000(7/24)/56^3 < 3/5,
    30600(7/24)/(187/20)^3 < 11,
    356000(465/4096)/57^3 < 1/4,
    30600(465/4096)/(53/8)^3 < 12.

These are integer comparisons after multiplication by the positive printed
denominators. Finally L_b^2>=b^2 s^2 gives B<=k^2/b=1587/128.
Therefore (10) implies

    s^3 F''(c)>423/16-(133/64)(38/3)=11/96>0.             (15)

At c0, L_a^2=876553/256 and L_b^2=3807/256. Squaring verifies

    L_a<14629/250,  L_b<3857/1000,
    H(c0)<(133/64)(62373/1000)<1037/8.

The subtracted expression in (14) is

    [9131+141 sqrt(47)]/128 >631/8,

using sqrt(47)>137/20. Thus F(c0)<203/4, whereas F(0)=T.
Convexity gives the useful strict chord bound

    F(c)<=T-(48/23)c,       0<=c<=c0,                    (16)

with strictness when c>0.

#### 3.2 Two other convex functions

On c>=0, L_a>=a and L_b^2>=bk s^2. Consequently

    -s^3 H''(c)<=r[k^2/a+sqrt(bk)]
                  <(9/4)(4+27/2)=315/8.                (17)

It follows that

    H(c)-[b+k+ac+(a+k)s]                                (18)

is convex on [0,1], and

    G(c)=H(c)-[2k+ac+(a+b)s]                            (19)

is convex on [0,c0]. Formula (18) equals T at zero and (13) at one.
Also G(0)=T and G(c0)<45: use H(c0)<130, c0=23/24,
s(c0)>7/25 in (19). In particular

    G(c)<=T-(186/23)c,       0<=c<=c0.                   (20)

#### 3.3 A diagonal-frame loss bound for the large weight

For 0<=c<=1,

    E_a(c)-D_a(c)<=2c.                                  (21)

Indeed put L=L_a and Delta=L-a-kc=k^2 s^2/(L+a+kc). Then

    E_a-D_a=k^2 cs/L-Delta(1-ks/L)
       <=(k^2/a)cs-[(1-k/a)k^2/(2(a+k))]s^2
       <=(11/3)cs-s^2.

The coefficient comparisons are

    k^2/a=1863/512<11/3,
    (1-k/a)k^2/(2(a+k))=985527/965632>1.

To prove (11/3)cs-s^2<=2c, the case s<=6/11 is immediate.
For s>=6/11, squaring the two nonnegative sides of
c(11s-6)<=3s^2 reduces it to

    P(s)=130s^4-132s^3-85s^2+132s-36>=0.

With t=s-3/4 the exact expansion is

    P=81/128+(9/8)t+(227/4)t^2+258t^3+130t^4.

It is positive for t>=0. For -9/44<=t<=0 put x=-t; then

    P=81/128-(9/8)x+x^2[227/4-258x+130x^2]>0,

because 227/4-258(9/44)=175/44>0 and
81/128-(9/8)(9/44)>0. This proves (21).

### 4. The complete nonnegative-normal half, 0<=c<=1

#### 4.1 N_a with E_b, and N_a with N_b

The first entry in (8) is exactly (18), so its convex endpoint bound proves
it. The second is G on [0,c0], handled by (20). For c>=c0 it is at most

    r a-k+[rb-a-b](c+s) <=(r-1)(a+b)-k<T,

by (12), since rb<a+b and c+s>=1.

#### 4.2 E_a with N_b

On [0,c0] this is F, so (16) applies. For c>=c0 the subtracted expression
is a+(b+k)(c+s). By (12) the result is at most

    (r-1)a+[rb-b-k](c+s).

Here c+s<5/4 on [c0,1]. Using r<25/12 bounds this by

    299/6+(27/16)(5/4)=9973/192<T.                       (22)

#### 4.3 D_a with N_b

For c<=c0, combine (16) and (21):

    H-D_a-N_b <= F+2c <=T-(2/23)c.

At c=0, D_a(0)>E_a(0), so this entry is strict there too.
For c>=c0, the diagonal expression in (7) gives

    D_a>=a+kc+(a/(a+k))ks=a+kc+(32/41)ks.

Using (12), r<133/64, c<=1 and s<7/24, the result is less than

    1587/32+(207/128)c+(9/2)s
       <=1587/32+207/128+(9/2)(7/24)
       =6723/128<T.                                    (23)

The coefficient of s used here is legitimate because
(69/64)b-(32/41)k<9/2.

#### 4.4 N_a with D_b

For 0<=c<=b/(2k)=12/23, formula (7) and

    D_b(-c)-N_b(-c)
        =(L_b-k)(L_b-bs)/L_b>=0

reduce the result to the N_a,N_b case.
For 12/23<=c<=c0,

    D_b(-c)>=N_b(-c)-k/4.                               (24)

To check this, bs/L_b increases up to c0. At c=12/23 its square is
u^2(1-u^2/4), where u=b/k=24/23 and 1<=u^2<6/5.
This is >7/10>9/16, so bs/L_b>3/4 throughout. The negative part of
(L_b-k)(L_b-bs)/L_b has magnitude at most k/4, proving (24).
Now (20), c>=1/2, and k/4=207/64 give

    H-N_a-D_b <=T-93/23+207/64<T.

For c>=c0, any bounding-rectangle semiperimeter D_b is at least b, the
length of one triangle side. Equations (12) and N_a=k+a(c+s) give

    H-N_a-D_b <=ra-k-b+[rb-a](c+s)
                 <=(r-1)(a+b)-k<T.                     (25)

This finishes all five entries on the nonnegative half.

### 5. The complete negative-normal half

Put t=-c>=0, s=sqrt(1-t^2), and

    A=sqrt(a^2+k^2-2ak t),
    B=sqrt(b^2+k^2+2bk t),
    K(t)=r(A+B)=H(-t),
    t0=9/32,  t1=19/20.

K is decreasing and concave. Indeed a/A increases and b/B decreases, and
a/A>b/B already at zero; hence K'=rk(-a/A+b/B)<0. Also

    K(t)<=H(0)-(k/2)t.                                  (26)

Two explicit comparison values used below are

    K(t0)<(133/64)(177/4+85/4)=17423/128<137,
    K(t1)<(133/64)(34+209/8)=63973/512.                  (27)

Their square checks are A(t0)^2=498847/256<(177/4)^2,
B(t0)^2=229311/512<(85/4)^2,
A(t1)^2=1475381/1280<34^2, and
B(t1)^2=872289/1280<(209/8)^2.
In particular

    K(t1)-(a+b+k)<26885/512<T.                           (28)

#### 5.1 N_a(-t) with E_b(t)

On [0,t0] the subtracted expression is

    b+k+kt+(a+k)s.

The resulting function is convex: A^2>=a^2s^2 and B>=b give
-s^3 K''<=r(k^2/a+k^2/b)<(9/4)(4+13)<a+k.
Its zero endpoint is T. To bound its other endpoint and the next interval,
observe that on [t0,t1],

    t+s>49/40,
    N_a(-t)+E_b(t)=b+(a+k)(t+s)>54847/640.

The first inequality follows from concavity and its two endpoint checks:
sqrt(943)>151/5 and sqrt(39)>11/2. With K(t)<=K(t0)<137, the result is
less than 32833/640<T throughout this interval. It also bounds the t0
endpoint of the preceding convex interval.
For t>=t1, the subtracted expression is at least a+b+k because t+s>=1;
use (28).

#### 5.2 E_a(-t) with N_b(t)

For 0<=t<=t1, (26) gives an upper bound

    T-(b+k/2)t+(b+k)(1-s).

It is at most T since

    t/(1+s)<=19/26<71/94=(b+k/2)/(b+k).

Here s(t1)=sqrt(39)/20>3/10. Strictness holds for t>0.
For t>=t1, b t+(b+k)s>=b, so the subtracted expression
a+k+b t+(b+k)s is at least a+b+k; use (28).

#### 5.3 N_a(-t) with N_b(t)

For 0<=t<=t0 the tangent bound (26) gives

    T-(b+k/2)t+(a+b)(1-s)<=T,

because t/(1+s)<=9/62<(b+k/2)/(a+b); use s(t0)>15/16.
For t>=t0 the subtracted expression is k+(a+b)(t+s), which exceeds
or equals b+(a+k)(t+s), the expression in Section 5.1: their difference
is (b-k)(t+s-1)>=0. Thus Section 5.1 applies.

#### 5.4 D_a(-t) with N_b(t)

For t<=t0,

    D_a(-t)-N_a(-t)=(A-k)(A-as)/A>=0,

since A>=as and A>k. Use Section 5.3.
For t0<=t<=2/3,

    E_a(-t)-D_a(-t)
         <=a k^2 s^2/[2(a-k)^2]
         <=1863/529<4.                                 (29)

To see this, put Delta=A-a+kt=k^2s^2/(A+a-kt). Since A<a on this
interval, the difference is at most a Delta/A. Both A and a-kt are
at least a-k, giving (29).
On the same interval, the improvement over T in Section 5.2 is

    d(t)=(b+k/2)t-(b+k)(1-s)>4.

This function is concave. Its two endpoint lower bounds are

    d(t0)>22833/5120>4      (use s(t0)>153/160),
    d(2/3)>501/80>4        (use sqrt(5)/3>11/15).

Thus (29) cannot consume the improvement.
For t>=2/3, in fact D_a(-t)>=E_a(-t). Put u=k/a=9/32 and q=A/a.
Squaring the positive comparison

    1-ut+us >= q(1+us)

reduces it exactly to 2(t-u)>=s q^2. But q<=1,
2(t-u)>=37/48, and s<=sqrt(5)/3<3/4<37/48.
Use Section 5.2 again.

#### 5.5 N_a(-t) with D_b(t)

For all t>=0, the identities

    D_b(t)-b-ks=(B-b)(B-ks)/B,
    B>=b+kt,  ks/B<1/sqrt(2)<3/4

give

    D_b(t)>=b+ks+(k/4)t.                                (30)

For t<=t0, (26) and (30) bound the result by

    T-(3k/4)t+(a+k)(1-s)<=T,

because t/(1+s)<=9/62<27/164=3k/[4(a+k)].

For t0<=t<=4/5, the subtracted expression is at least

    J(t)=b+(a+k)s+(a+k/4)t>167/2.

J is concave; at t0 the bound s>153/160 gives J>857151/10240>167/2,
and J(4/5)=353/4. Together with K(t)<=K(t0)<17423/128,
this gives a strict upper bound 6735/128<T.

For 4/5<=t<=t1, K(t)<=K(4/5)<130, using A(4/5)<37,
B(4/5)<51/2 and r<133/64. Concavity and s(t1)>3/10 show
J(t)>311/4 on this interval, so the result is <209/4<T.

For t>=t1 use the different bound D_b>=B>=b+kt. The subtracted
expression is at least

    b+(a+k)t+a s >= a+b+k.

This last concave function has the stated lower bound at t=1, and at
t1 it is larger, using s(t1)>3/10. Formula (28) finishes the interval.

All five ownership/rectangle entries in (8) are now proved on [-1,1].

### 6. Equality in the cap theorem

The strict bounds away from c=0 force the actual separating normal to be
perpendicular to e. At c=0, N_w=E_w=w+k, whereas

    D_w(0)-(w+k)=(L-w)(L-k)/L>0,
    L=sqrt(w^2+k^2),

since w>k>0. The rectangle-minimum argument is strictly concave between
its extrema, so equality requires both square frames to align with e,n.
Equality in the circle-support inequalities then puts the relevant actual
corners at

    (-2, -sigma*9/16),
    (-3/2, sigma*23/16)

for n=sigma*(0,1). Subtracting the corresponding aligned corner offsets
gives (2), with the sign renamed. The disk radius must be r by (5).
Direct substitution verifies the converse. This proves Theorem 1.

### 7. Consequence: arbitrary physical four-plus-three projection chains

**Theorem 2.** Suppose seven actual independently oriented unit squares
can be partitioned into two projection-disjoint chains along ONE direction e,
of respective lengths four and three. Assume only actual physical interior
nonoverlap of the seven squares. Then their containing radius satisfies

    R^2>=1105/256.                                      (31)

No common separating frame for all pairs is needed.

Proof. If R>r the assertion is immediate, so suppose R<=r. Label the two
chains' endpoints M_L,M_R and B_L,B_R in increasing e order. Projection
separation and the minimum width one of every intervening unit square give

    e.(c_MR-c_ML)-h_ML(e)-h_MR(e)>=2,
    e.(c_BR-c_BL)-h_BL(e)-h_BR(e)>=1.                    (32)

Apply Theorem 1 to the actual pair (M_L,B_L) in direction e, and to the
actual pair (M_R,B_R) in direction -e. Adding gives the upper bound
2T=211/2 for the weighted left sides of (32). Their lower bound is

    2a+b=92+27/2=211/2.

Thus equality holds everywhere and R=r. If R<r each cap bound would be
strict, giving an immediate contradiction. This proves (31).

At equality, the four endpoints have the signed matched-anchor coordinates

    M_L=(-3/2,sigma_L/16), M_R=(3/2,sigma_R/16),
    B_L=(-1,-15sigma_L/16), B_R=(1,-15sigma_R/16).

The interior chain squares have projection width one because (32) is sharp,
so their frames are aligned too, and their projected centers fill the unit
gaps. Their perpendicular coordinates remain constrained by actual packing
and containment, not asserted fixed. Any other physical squares are retained
and may have arbitrary orientations.


## C. Endpoint and weak-middle consequences

### C.1. A criterion requiring four endpoints only

For four distinct originals A,D,E,G and a unit direction e define

\[
 L=e\cdot(c_D-c_A)-h_A(e)-h_D(e),\qquad
 S=e\cdot(c_G-c_E)-h_E(e)-h_G(e),\qquad
 W=46L+\frac{27}{2}S.
\]

For a packing in the Q-disk, Part B applied to the physical pair A,E in
direction e and to D,G in direction −e gives

\[
 W\le\frac{211}{2},
 \tag{C1}
\]

strictly if the containing radius is smaller than r. The proof only adds
the two inequalities and uses \(h_i(-e)=h_i(e)\). Thus the existence of
four such endpoints with \(W\ge211/2\) proves \(R\ge r\), without
any chain or separator hypotheses on those endpoints. At R=r, equality
forces both pair caps to be sharp, giving exactly the four anchor
coordinates stated at the end of Part B.

### C.2. A cone middle link between two actual outer links

Set

\[
 \eta_i=h_i+g_i-1=\frac{(2h_i-1)^2}{4h_i}\ge0.
\]

Suppose the originals A,B,C,D have actual outer projection comparisons
\(x_B-x_A\ge h_A+h_B\) and \(x_D-x_C\ge h_C+h_D\), while
\(d=x_C-x_B>0\) and \(|y_C-y_B|\le d\). Equation (A4) gives

\[
 d+h_B+h_C\ge g_B+g_C+h_B+h_C
 =2+\eta_B+\eta_C.
\]

Adding the outer comparisons therefore gives

\[
 x_D-x_A-h_A-h_D\ge2+\eta_B+\eta_C.
 \tag{C2}
\]

If three other originals E,F,G form an actual projection chain, then
\(x_G-x_E-h_E-h_G\ge2h_F\ge1\). Hence (C1)–(C2) exclude any
containing radius below r. If the middle link is genuinely weak,
\(d<h_B+h_C\), at least one of B,C has h_i>1/2: two aligned squares
would have \(g_B+g_C=h_B+h_C=1\). Thus \(\eta_B+\eta_C>0\),
and (C1) excludes even R=r. No conditions are imposed on other pairs or
on either omitted original in a nine-square packing.

### C.3. Signed surpluses are retained exactly

For any seven distinct labels A,B,C,D;E,F,G, write
\(s_{ij}=x_j-x_i-h_i-h_j\). Telescoping yields

\[
\begin{aligned}
 W-\frac{211}{2}={}&46\left(2h_B+2h_C-2+s_{AB}+s_{BC}+s_{CD}\right)\\
 &+\frac{27}{2}\left(2h_F-1+s_{EF}+s_{FG}\right).
\end{aligned}
 \tag{C3}
\]

This identity needs no cone assumption. It explains exactly what a global
caller must supply: a suitable endpoint choice with nonnegative total
weighted surplus, or another established terminal. It does not say that
an arbitrary extracted cone witness has that property.

## D. Two interior markers for a directional center cap

This part proves the individual-square input used by Part E. It
consolidates Sections 1–5 of the retained
[directional center-cap manuscript](sources/THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md).
The polynomial identity and the full interval proof are printed here;
there is no external arithmetic dependency.

Put

\[
 Q=\frac{1105}{256},\quad R=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad
 \eta=\frac{21}{20},\quad \kappa=\frac76,\quad
 \tau=\frac{499}{1000},\quad d=\kappa-\eta=\frac7{60}.
\]

### 1. The theorem and the retained slice argument

**Theorem.** Every physical unit square in the Q-disk with center
\((X,Y)\), where \(Y\ge21/20\), contains at least one of

\[
                       (-\tau,\kappa),
                       \qquad(\tau,\kappa)             \tag{1}
\]

in its interior. Thus any three interior-disjoint physical unit squares
satisfy, for every unit direction e,

\[
                          \min_{i=1,2,3}e\cdot c_i
                          <\frac{21}{20}.              \tag{2}
\]

No pairwise coordinate-separation assumption is made. The numerical
threshold is not asserted sharp.

For side-axis absolute components \(a\ge b\ge0\),
\(a^2+b^2=1\), put
\(h=(a+b)/2\), \(j=(a-b)/2\). The section at a vertical offset t
has length \(1/a\) for \(|t|\le j\), and
\((h-|t|)/(ab)\) for \(j\le|t|\le h\), when b>0. In particular
it has length at least one if \(|t|<h-ab\).

For the line at height κ, the offset below the center is bounded using
the uppermost vertex y+h≤R and

\[
 R<\frac{133}{64}<\frac{206}{99}<\sqrt2+\frac23.
\]

The first root comparison has squared reserve 9/4096. The middle
comparison has cross-product difference 17; the last uses
\(\sqrt2>140/99\), since 19602>19600. Also
\(2h-ab\ge\sqrt2-1/2\): writing z=a+b in \([1,\sqrt2]\),
the expression is z−(z²−1)/2, which decreases on that interval.
Consequently y−κ≤R−h−κ<h−ab when the center is above the line.
The offset above the center is at most

\[
 \kappa-\eta=\frac7{60}<\frac{\sqrt2-1}{2}\le h-ab.
\]

Thus this section is a closed interval of length at least one, and the
line passes strictly between the unit's extreme y-coordinates.

The last bound follows from
\(h-ab=(1+z-z^2)/2\ge(\sqrt2-1)/2\).
As the section length exceeds the marker spacing \(2\tau<1\), it is enough
to exclude a section lying entirely on or to the right of τ. Reflection
excludes the corresponding left case. One marker will then lie strictly
inside the section and hence inside the physical square.

### 2. The actual side inequality and its upward sign

Suppose that section has left endpoint at least τ. The line passes
strictly between the square's extreme y-coordinates, so a side giving
the left endpoint is not horizontal. Its inward normal points to the
right and is one of the square's actual side axes. Thus it supplies
\(n=(p,s)\), with
p>0 and \(p^2+s^2=1\), such that

\[
                       n\cdot c\ge\frac12+p\tau+s\kappa. \tag{3}
\]

The perpendicular side axis is \(m=(-s,p)\). For
\(\alpha=n\cdot c\), \(\beta=m\cdot c\), the exact maximal
corner norm is

\[
                         (|\alpha|+1/2)^2+(|\beta|+1/2)^2. \tag{4}
\]

All centers obey \(|c|<\rho\). This follows from
\(q\ge|c|^2+|c|+1/2\) and
\(\rho^2+\rho+1/2-Q=31/57600>0\).

Assume first s≥0, and put \(J=1/2+\tau p+\kappa s\).
The function \(\tau\sqrt{1-s^2}+\kappa s\) is concave. On
\([3/5,1]\) its minimum is therefore at an endpoint; adding 1/2,
the endpoint values are 1999/1250 and 5/3. Hence for s≥3/5,

\[
                         \alpha\ge J\ge\frac{1999}{1250}>\rho,
\]

which is impossible. For \(0\le s\le3/5\), we have p≥4/5>s,
α≥J>0, and

\[
 \beta=\frac{Y-s\alpha}{p}
 >\frac{\eta-(3/5)\rho}{p}=\frac7{50p}>0.             \tag{5}
\]

For fixed α, lowering Y to η decreases (4). At Y=η, half the derivative
of (4) with respect to α is

\[
                    \frac{\alpha-s\eta+(p^2-sp)/2}{p^2}>0
                    \qquad(\alpha\ge J),
\]

since \(J-s\eta=1/2+\tau p+ds>0\). Thus (4) is bounded below
by its value at \(Y=\eta,\alpha=J\). The corresponding horizontal
coordinate is

\[
                          X'=\tau+\frac{1/2+ds}{p}.    \tag{6}
\]

Set \(h=(p+s)/2\), \(j=(p-s)/2\). At that minimizing center,
the corner in (4) has coordinates \((X'+j,\eta+h)\). For a positive
lower bound v≤X', its squared norm is at least

\[
                 v^2+\eta^2+\frac12+(\eta+v)p+(\eta-v)s. \tag{7}
\]

Two simple ranges suffice:

| s range | Lower bounds used in (7) | Squared-norm lower bound | Reserve over Q |
|---|---|---:|---:|
| \([0,2/5]\) | \(X'>99/100,\ p>9/10\) | \(22093/5000\) | \(16351/160000\) |
| \([2/5,3/5]\) | \(X'>26/25,\ p\ge4/5\) | \(43561/10000\) | \(6351/160000\) |

In both rows η≥v, so the last term in (7) can be dropped. The first
row uses \(p\ge\sqrt{21}/5>9/10\) and
\(X'\ge\tau+1/2>99/100\). For the second,

\[
 X'\ge\tau+\frac12+\frac25d
 =\frac{3137}{3000}>\frac{26}{25}.
\]

The two reserves follow by putting the displayed bounds and Q over
denominator 160000. The entire nonnegative-sign case is excluded.

### 3. The downward sign and its large vertical component

Write now \(n=(p,-u)\), with p>0, u≥0, and \(p^2+u^2=1\).
Equation (3) and Y≥η give

\[
 X\ge\tau+\frac{1/2+u(Y-\kappa)}p
   \ge X_\eta(u):=\tau+\frac{1/2-du}{\sqrt{1-u^2}}.   \tag{8}
\]

For u≥18/25, the fraction in (8) increases: its derivative has
numerator u/2−d>0. Consequently

\[
 X\ge\tau+\frac{52}{5\sqrt{301}}
 >\tau+\frac{208}{347}>\frac{219}{200}.                \tag{9}
\]

Here \(\sqrt{301}<347/20\), with squared numerator comparison
\(120400<120409\), and
\(\tau+208/347-219/200=297/86750>0\). Therefore

\[
 |c|^2>\left(\frac{219}{200}\right)^2+
          \left(\frac{21}{20}\right)^2
 =\rho^2+\frac{449}{360000}>\rho^2,
\]

which is impossible.

It remains to consider \(0\le u\le18/25\). Put

\[
 h=\frac{p+u}{2},\quad j=\frac{p-u}{2}.
\]

One actual corner is \((X+h,Y+j)\). Both coordinates in the lower
bound \((X_\eta+h,\eta+j)\) are positive, so (8) gives

\[
                 q\ge (X_\eta(u)+h)^2+(\eta+j)^2.     \tag{10}
\]

This does not assume which own-frame coordinate determines the farthest
corner. A single actual corner is sufficient.

### 4. One explicit polynomial represents the remaining corner bound

Use the half-angle parameter

\[
 t=\frac{u}{1+p},\qquad
 p=\frac{1-t^2}{1+t^2},\quad u=\frac{2t}{1+t^2}.
\]

The remaining u range gives

\[
 0\le t\le\frac{18}{25+\sqrt{301}}<\frac37,           \tag{11}
\]

using \(\sqrt{301}>17\). Direct substitution yields

\[
 X_\eta=\frac{2997-700t+3t^2}{3000(1-t^2)}.
\]

Define

\[
 A(t)=4497+2300t-3700t^3+1503t^4,
\]

\[
 B(t)=4650-3000t-3000t^2+3000t^3-1650t^4.
\]

Then

\[
 X_\eta+h=\frac{A(t)}{3000(1-t^4)},
 \qquad \eta+j=\frac{B(t)}{3000(1-t^4)}.
\]

Thus the right side of (10), minus Q, is

\[
                \frac{P(t)}{36000000(1-t^4)^2},        \tag{12}
\]

where the following table specifies every coefficient of P:

| Degree | Coefficient |
|---:|---:|
| 0 | 11991411 |
| 1 | -28855200 |
| 2 | -54440000 |
| 3 | 50488800 |
| 4 | 199393178 |
| 5 | -4744800 |
| 6 | 130360000 |
| 7 | -84088800 |
| 8 | -135464589 |

For direct independent hand verification, the entire table is the single
identity

\[
             P(t)=4\bigl(A(t)^2+B(t)^2\bigr)
                   -155390625(1-t^4)^2.               \tag{13}
\]

No generated table or numerical sample is used: (13) and the next scalar
inequalities establish positivity on the whole interval (11).

### 5. A hand proof that P is positive on the whole interval

#### 5.1. P decreases up to 3/10

For \(0\le t\le3/10\), drop the negative degree-four, degree-six,
and degree-seven terms of P'. Its positive terms satisfy

\[
\begin{aligned}
 151466400t^2+797572712t^3+782160000t^5
 &<\left(152000000\frac3{10}
       +798000000\frac9{100}
       +783000000\frac{81}{10000}\right)t\\
 &<124000000t
\end{aligned}
\]

for t>0; t=0 is immediate separately. Hence

\[
 P'(t)\le-28855200+15120000t
 \le-24319200<0.                                      \tag{14}
\]

So P(t)≥P(3/10) on this first interval.

#### 5.2. Uniform strict convexity from 3/10 through 3/7

The exact second derivative is

\[
\begin{aligned}
 P''(t)={}&-108880000+302932800t+2392718136t^2
            -94896000t^3\\
          &+3910800000t^4-3531729600t^5-7586016984t^6.
\end{aligned}
\]

For \(0\le t\le3/7\), use

\[
 94896000t^3<41000000t^2,
\]

\[
 3531729600t^5\le1514000000t^4,
 \qquad7586016984t^6\le1394000000t^4.
\]

At t=0 the first displayed strict inequality is read as equality;
we use the resulting strict estimate below only for t≥3/10.
These comparisons follow respectively from

\[
 94896000\frac37<41000000,
 \quad3531729600\frac37<1514000000,
 \quad7586016984\frac9{49}<1394000000.
\]

The remaining degree-four coefficient is positive. It follows, throughout
\(3/10\le t\le3/7\), that

\[
\begin{aligned}
 P''(t)
 &>-109000000+300000000t+2350000000t^2\\
 &\ge192500000>180000000.                             \tag{15}
\end{aligned}
\]

#### 5.3. One rational anchor and a quadratic lower bound

Direct evaluation of the printed polynomial gives

\[
 P(2/5)=\frac{130272735091}{390625}>300000,
\]

\[
 0<P'(2/5)=\frac{475586408864}{78125}<7000000.          \tag{16}
\]

For an explicit check of these two evaluations, at t=2/5 one has

\[
 A=\frac{3261673}{625},\qquad B=\frac{1949850}{625},
 \qquad A'=\frac{113596}{125},\qquad B'=-\frac{547800}{125},
 \qquad1-t^4=\frac{609}{625}.
\]

Substitution in (13) gives the first numerator in (16). Differentiating
(13) gives \(P'=8(AA'+BB')+8\cdot155390625\,t^3(1-t^4)\),
which gives the second numerator. Integrating the uniform
second-derivative bound (15), or completing the corresponding
quadratic, gives for every t in \([3/10,3/7]\)

\[
\begin{aligned}
 P(t)
 &\ge P(2/5)+P'(2/5)(t-2/5)+90000000(t-2/5)^2\\
 &>300000-\frac{7000000^2}{360000000}
   =\frac{1475000}{9}>0.                              \tag{17}
\end{aligned}
\]

In particular P(3/10)>0. Equation (14) now proves positivity on
\([0,3/10]\) as well. Thus P is positive everywhere in (11).

Equations (10)--(12) contradict q≤Q. This completes the entire downward
normal case.


### 6. Directional and convex-hull consequences

The preceding argument excludes a height-κ section lying on or beyond
either marker. Its length is at least one, strictly greater than the
marker spacing, so it contains a marker strictly in its interior. Since
the slicing line is strictly between the extreme heights of the square,
that marker is interior to the physical square. This proves the theorem
in Part D.1.

It follows by the pigeonhole principle that at most two pairwise
interior-disjoint originals in the Q-disk can have center projection
at least 21/20 in one direction. Equivalently, the convex hull of any
three physical centers meets the open disk of radius 21/20. For the
latter formulation, if the hull avoided that open disk, its closest
point p to zero would satisfy |p|≥21/20. The inequality
\((z-p)\cdot p\ge0\) for all hull points z follows by differentiating
\(|p+t(z-p)|^2\) at t=0. Thus the unit direction p/|p| would place all
three center projections at least 21/20, contradicting the marker bound.
This includes collinear triples.

## E. The sharp three-square whole-half-plane cap

The proof below consolidates the retained
[sharp half-plane-cap manuscript](sources/THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md).
Its only previously proved inputs are Parts A and D of this chapter.
Its equality classification concerns these three squares only.

Put

\[
 Q=\frac{1105}{256},\quad R=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad b_0=\frac7{16},\quad
 \kappa=\frac76,\quad K=\kappa-b_0=\frac{35}{48}.
\]

### 1. The sharp physical theorem

**Theorem.** Suppose three interior-disjoint physical unit squares lie in
a centered disk of squared radius q, and each whole square lies in the
half-plane y≥7/16. Then

\[
                              q\ge\frac{1105}{256}.     \tag{1}
\]

The square frames are arbitrary. This is a genuine physical three-square
cap theorem, with no coordinate-separation premise.

The bound is attained by three aligned squares centered at

\[
                    (-1,15/16),\quad(0,15/16),\quad(1,15/16).
\]

Their lower edges are at 7/16; the outer corners
\((\pm3/2,23/16)\) have squared norm Q. Thus (1) is sharp.
The complete equality family for this three-square terminal is given in
Section 8. It does not classify unrestricted nine-square equality.

The only nonlocal step within this part is the individual-square two-point
capture established in Part D of this chapter; the elementary physical
inputs are proved in Part A.

### 2. A two-point capture statement with closed markers

We first prove that every individual physical unit square contained in
the Q-disk and entirely above y=7/16 contains at least one of the two
**closed** points

\[
                         P_-=(-1/2,\kappa),
                         \qquad P_+=(1/2,\kappa).       \tag{2}
\]

Closed containment is intentional. In the sharp aligned three-square
packing, the markers can be shared on boundaries; they are not asserted
to lie in the interiors of all captured squares.

Write the square's center as \((X,Y)\), its projection halfwidth as h,
and its side-axis absolute components as a≥b≥0, where a²+b²=1 and
h=(a+b)/2. The cap hypothesis is exactly

\[
                               Y\ge h+b_0.              \tag{3}
\]

The horizontal section at height κ has length at least one. To check
this, recall the elementary slice formula: with j=(a−b)/2, the length
at vertical offset t is 1/a for |t|≤j, and (h−|t|)/(ab) for
j≤|t|≤h when b>0. Thus |t|<h−ab suffices; the aligned case has
length exactly one.

If Y≤κ, then by (3)

\[
 \kappa-Y\le K-h<h-ab,
\]

because \(K<\sqrt2-1/2\le2h-ab\). If Y≥κ, use Y+h≤R and
\(R<\sqrt2+2/3\) to get

\[
 Y-\kappa\le R-h-\kappa<h-ab.
\]

Both inequalities are strict. The section is therefore a nondegenerate
closed interval I of length at least one, strictly between the square's
extreme vertical coordinates. If it missed both points (2), it would
have to lie strictly to the right of 1/2 or strictly to the left of −1/2.
It cannot lie between the two points while avoiding them, because that
open interval has length one. Reflection reduces us to

\[
                               \inf I>\frac12.          \tag{4}
\]

We will exclude (4).

### 3. The larger-halfwidth case follows from the center-cap theorem

If h≥49/80, (3) gives

\[
                              Y\ge\frac{21}{20}.
\]

The two-point theorem at 21/20 says the physical square contains one of
\((\pm499/1000,\kappa)\) in its interior. This is incompatible with
(4), and its reflected version. Hence all h≥49/80 squares satisfy
the desired closed-marker capture.

For the rest of the proof assume

\[
                  h<\frac{49}{80},\qquad a+b<\frac{49}{40}. \tag{5}
\]

This forces

\[
                            b<\frac{13}{50},
                            \qquad a>\frac{24}{25}.     \tag{6}
\]

Indeed b+√(1−b²) increases on [0,1/√2]. At b=13/50 it is
strictly greater than 49/40, because
\(\sqrt{2331}>193/4\), whose squared check is 37296>37249.
This proves the first bound in (6); the second follows from
\(a>\sqrt{2331}/50>193/200>24/25\).

### 4. An actual inward normal of the side missing the marker

A side bounding the left endpoint in (4) supplies an inward physical
side normal \(n=(p,s)\), with p>0 and p²+s²=1, such that

\[
                 pX+sY>\frac12+\frac p2+s\kappa.      \tag{7}
\]

The strict inequality is justified by (4). Each component magnitude of
this actual normal is a or b. We call it shallow when p=a, |s|=b,
and steep when p=b, |s|=a.

#### 4.1. A steep upward normal is impossible

If n=(b,a), then (7) and (6) give

\[
 n\cdot c>\frac12+\frac b2+\kappa a
 >\frac12+\frac76\frac{24}{25}=\frac{81}{50}>\rho,
\]

contradicting the universal center bound \(|c|<\rho\).

#### 4.2. A steep downward normal is impossible

If n=(b,−a), inequality (7) requires

\[
                  b(X-1/2)+a(\kappa-Y)>\frac12.
\]

But X<ρ, Y≥h+b0, h≥1/2, and (6) give

\[
\begin{aligned}
 b(X-1/2)+a(\kappa-Y)
 &<\frac{13}{50}\left(\rho-\frac12\right)
      +\left(K-\frac12\right)\\
 &=\frac{987}{2000}<\frac12.
\end{aligned}
\]

In taking a≤1, the factor K−h is positive by (5). This is a contradiction.

It remains to treat the two shallow signs.

### 5. A shallow upward normal gives the sharp corner bound

Write n=(p,s), with p=a>24/25 and 0≤s=b<13/50. Put

\[
 \eta=h+b_0,\qquad
 J=\frac12+\frac p2+\kappa s,
 \qquad \alpha=n\cdot c,
 \qquad\beta=(-s,p)\cdot c.
\]

By (7), α>J>0. Also β=(Y−sα)/p>0: one has Y≥15/16,
s<13/50 and α<ρ. The maximal squared corner norm is therefore

\[
                          (\alpha+1/2)^2+(\beta+1/2)^2. \tag{8}
\]

For fixed α, lowering Y to η decreases (8). At Y=η, half its
derivative with respect to α is

\[
                     \frac{\alpha-s\eta+(p^2-ps)/2}{p^2}>0,
\]

since p>s and
\(J-s\eta=1/2+p/2+s(K-h)>0\). Thus (8) is strictly greater than
its value at \(Y=\eta,\alpha=J\).

The latter center has horizontal coordinate

\[
                  X'=\frac12+\frac{1/2+s(K-h)}p\ge1.  \tag{9}
\]

Its relevant physical corner has coordinates
\((X'+j,p+s+b_0)\), where j=(p−s)/2. Compare it with
\((3/2,23/16)\), whose norm squared is Q. If the coordinate
increments are Δx,Δy, then

\[
 \Delta x\ge\frac{p-s-1}{2},\qquad
 \Delta y=p+s-1.
\]

The linear part of the squared-norm difference satisfies

\[
\begin{aligned}
 3\Delta x+\frac{23}{8}\Delta y
 &\ge\frac{35}{8}(p-1)+\frac{11}{8}s\\
 &=\frac s8\left(11-\frac{35s}{1+p}\right)\ge0.        \tag{10}
\end{aligned}
\]

Indeed s/(1+p)<13/98<11/35 by (6). Adding the nonnegative
Δx²+Δy² proves that the minimizing corner norm is at least Q.
The strict inequality α>J in (7) makes the actual norm greater than Q,
even in the aligned case s=0. This contradicts containment.

### 6. A shallow downward normal gives the same sharp bound

Write n=(p,−u), where p=a>24/25 and 0≤u=b<13/50. Equation (7)
and (3) give

\[
 X>\frac12+\frac{1/2+u(Y-\kappa)}p
   \ge X':=\frac12+\frac{1/2-u(K-h)}p.                \tag{11}
\]

The actual corner \((X+h,Y+j)\), with j=(p−u)/2, has norm strictly
greater than the corresponding norm at \((X'+h,p+b_0)\). All
coordinates used in this comparison are positive.

The increments from the same sharp corner \((3/2,23/16)\) are

\[
 \Delta x=\frac{1-p+u(p-K)}p,
 \qquad \Delta y=p-1.                                  \tag{12}
\]

This is a direct simplification of (11) using p²+u²=1 and h=(p+u)/2.
Their linear norm contribution is

\[
\begin{aligned}
 3\Delta x+\frac{23}{8}\Delta y
 &=(1-p)\left(\frac3p-\frac{23}{8}\right)
       +\frac{3u(p-K)}p\ge0.                          \tag{13}
\end{aligned}
\]

Here p≤1 gives 3/p−23/8≥1/8, and (6) gives p>K.
Adding the nonnegative increment squares again yields a norm at least Q.
The strict horizontal inequality in (11) makes the actual corner norm
greater than Q. This is impossible.

All four actual-side cases are exhausted. Hence (4) is impossible, as
is its reflection. The closed-marker capture statement (2) is proved.

### 7. Closed-marker capture proves the sharp three-square theorem

Suppose, for a contradiction, that three interior-disjoint units meeting
the cap condition fit in a disk with q<Q. Keep every frame fixed and
multiply all centers by the same factor t>1.

For every physical pair, a separating-axis inequality has the form

\[
 n\cdot(c_j-c_i)\ge H_i(n)+H_j(n)>0.
\]

After the common center expansion its left side is multiplied by t,
so each pair's chosen separator becomes strict. The closed squares are
then pairwise disjoint. The maximal corner norms vary continuously, and
for t>1 sufficiently close to one they remain below Q. We may instead
continue the expansion until the maximal corner norm equals Q; the
strict pair separations remain valid throughout.

The cap condition is preserved, since each original center has Y>0 and

\[
                  tY-h=(Y-h)+(t-1)Y\ge\frac7{16}.
\]

Thus three pairwise disjoint **closed** units would lie in the Q-disk
and in the cap. By (2), each contains at least one of two fixed closed
points. Two units must contain the same point, contradicting closed
disjointness. This proves q≥Q.

No strict-interior claim about the half-unit markers is used in this last
argument. Equality packings may share them on boundaries, as the attaining
aligned example demonstrates.

### 8. Complete equality classification for this cap

Suppose the three squares satisfy the cap hypothesis and fit in the Q-disk.
Take their horizontal sections at height kappa, and order the resulting
closed intervals as I_L, I_M, I_R. Each has length at least one, each
contains a marker from {-1/2,1/2}, and their open intervals are pairwise
disjoint. The latter follows because the slicing line lies strictly between
each square's extreme vertical coordinates.

These facts force

\[
\sup I_L=-\frac12,\qquad
I_M=[-1/2,1/2],\qquad
\inf I_R=\frac12.                                      \tag{14}
\]

Here is the complete interval argument. The first interval cannot contain
the right marker: otherwise the second must start there to meet either
marker, and its length at least one leaves no marker for the third.
Symmetrically the third cannot contain the left marker. If the middle
contains the left marker, disjoint interiors force its left endpoint and
the first interval's right endpoint to equal -1/2. Its length at least one
then forces its right endpoint and the third interval's left endpoint to
equal 1/2. If it contains the right marker, the reflected argument gives
the same conclusion.

For a nonaligned frame, the strict offset bound proved in Section 2 makes
the section length strictly greater than one: in the opposite-side regime
it equals 1/a>1, and in the adjacent-side regime it is greater than one by
|t|<h-ab. Hence the middle square is aligned. Equation (14) puts its center
at (0,t). The cap and corner-containment inequalities are exactly

\[
\frac{15}{16}\le t\le
\rho_*:=\sqrt{Q-\frac14}-\frac12
       =\frac{\sqrt{1041}-8}{16}.                       \tag{15}
\]

For the right square, (14) gives the side inequality (7) with a weak
inequality instead of a strict one. The larger-halfwidth case of Section 3
is still impossible: its section would contain an interior point with
horizontal coordinate at most 499/1000, although its left endpoint is
1/2. Both steep-normal cases remain strictly impossible by their unchanged
center bounds.

In the shallow upward case, (10) is strictly positive whenever s>0. In the
shallow downward case, (13) is strictly positive whenever u>0 because p>K.
All remaining squared increments are nonnegative. Thus a nonzero tilt would
force a corner norm strictly above Q. The right square is aligned. Its left
section endpoint fixes its center x-coordinate at 1; the cap gives Y>=15/16,
while the corner (3/2,Y+1/2) has norm at most sqrt(Q). These inequalities
force Y=15/16. Reflection gives the left center (-1,15/16).

Consequently all equality configurations for the stated cap, up to
relabeling, are precisely the three aligned squares with centers

\[
\boxed{(-1,15/16),\quad(0,t),\quad(1,15/16),
\qquad 15/16\le t\le\rho_*.}                          \tag{16}
\]

Conversely, every value in (15) gives a valid packing: the open horizontal
projections are disjoint, all lower edges meet the cap guard, the outer
squares attain Q, and the middle square is contained exactly by (15).
This proves necessity and sufficiency, including both endpoints.

### 9. Rotated form and exact scope

For any unit direction e, if three whole physical unit squares lie in
the half-plane \(e\cdot x\ge7/16\), their enclosing centered disk
has squared radius at least Q. Reflection gives the corresponding lower
cap statement. Therefore a strict subcritical nine-square packing has
at most two whole squares in each such cap.

This supplies an unrestricted physical terminal, with its complete
three-square equality family, that can be used without first proving
coordinate separation among those three squares. It does not assert that
a full nine-square configuration must contain such a triple, and it makes
no unrestricted nine-square equality-classification claim.

## F. Dependency and coverage record

The complete dependency order is:

1. Part A establishes physical support, separating axes, insets, center
   bounds, and strictification directly from square geometry and elementary
   convexity.
2. Part B uses A and elementary one-variable calculus. Its five owner
   alternatives exhaust the actual separating-axis possibilities; its
   scalar intervals cover −1≤c≤1 with their shared boundaries retained.
3. Part C uses A and B only.
4. Part D uses A, the printed horizontal-section formula, the exact
   polynomial identity, and the displayed scalar estimates. The upward and
   downward actual side normals exhaust the missed-marker possibilities.
5. Part E uses A and D. The large-halfwidth alternative and four small-
   halfwidth side-normal cases exhaust every physical square satisfying
   the whole-half-plane condition. Strictification proves the strict-radius
   exclusion; its separate interval and corner argument handles equality.

The elementary calculus used here is the mean-value consequence of a
second-derivative sign, tangent and chord bounds for concave or convex
functions, and integration of a uniform second-derivative bound. The
geometric input is Euclidean convexity, proved where used. No external
finite-poset theorem is needed for this chapter.

This chapter establishes two sharp terminal criteria: the weighted
endpoint criterion (C1), and the three-square whole-half-plane cap in
Part E. It also supplies the exact weak-middle corollary and the
unrestricted directional center guard. A proof that every hypothetical
nine-square packing below r reaches one of these terminals is a separate
mathematical obligation; none of the tables in this chapter supplies that
all-nine implication.
