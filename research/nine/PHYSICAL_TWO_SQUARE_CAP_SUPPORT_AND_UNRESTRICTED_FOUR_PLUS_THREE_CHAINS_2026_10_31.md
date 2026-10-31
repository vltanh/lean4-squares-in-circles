# A physical two-square cap inequality and an unrestricted four-plus-three chain terminal

October 31, 2026. **Complete hand derivation; separate positive-half and
negative-half/equality hand reviews passed.** The latter found one integer
transcription error in B(19/20)^2; it is corrected in these bytes. The
top-level physical reduction and chain application also received a third
independent hand check. No formal verification is claimed.

This manuscript removes the common-coordinate-separation assumption from the
existing four-plus-three projection-chain terminal. It does not assert that
every nine-square packing contains such chains. The unrestricted nine-square
theorem, its original coarse parents, and global equality remain open until
that extraction or another complete caller is proved.

No mathematical exclusion program, numerical interval cover, Lean, or CI is
used below. The finite scalar table consists of displayed rational estimates
whose proofs are included.

## 1. The two-square theorem

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

## 2. Reduction to a scalar support inequality

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

### 2.1 A three-direction rectangle lemma

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

## 3. Constants and reusable scalar estimates

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

### 3.1 The only convexity table

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

### 3.2 Two other convex functions

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

### 3.3 A diagonal-frame loss bound for the large weight

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

## 4. The complete nonnegative-normal half, 0<=c<=1

### 4.1 N_a with E_b, and N_a with N_b

The first entry in (8) is exactly (18), so its convex endpoint bound proves
it. The second is G on [0,c0], handled by (20). For c>=c0 it is at most

    r a-k+[rb-a-b](c+s) <=(r-1)(a+b)-k<T,

by (12), since rb<a+b and c+s>=1.

### 4.2 E_a with N_b

On [0,c0] this is F, so (16) applies. For c>=c0 the subtracted expression
is a+(b+k)(c+s). By (12) the result is at most

    (r-1)a+[rb-b-k](c+s).

Here c+s<5/4 on [c0,1]. Using r<25/12 bounds this by

    299/6+(27/16)(5/4)=9973/192<T.                       (22)

### 4.3 D_a with N_b

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

### 4.4 N_a with D_b

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

## 5. The complete negative-normal half

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

### 5.1 N_a(-t) with E_b(t)

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

### 5.2 E_a(-t) with N_b(t)

For 0<=t<=t1, (26) gives an upper bound

    T-(b+k/2)t+(b+k)(1-s).

It is at most T since

    t/(1+s)<=19/26<71/94=(b+k/2)/(b+k).

Here s(t1)=sqrt(39)/20>3/10. Strictness holds for t>0.
For t>=t1, b t+(b+k)s>=b, so the subtracted expression
a+k+b t+(b+k)s is at least a+b+k; use (28).

### 5.3 N_a(-t) with N_b(t)

For 0<=t<=t0 the tangent bound (26) gives

    T-(b+k/2)t+(a+b)(1-s)<=T,

because t/(1+s)<=9/62<(b+k/2)/(a+b); use s(t0)>15/16.
For t>=t0 the subtracted expression is k+(a+b)(t+s), which exceeds
or equals b+(a+k)(t+s), the expression in Section 5.1: their difference
is (b-k)(t+s-1)>=0. Thus Section 5.1 applies.

### 5.4 D_a(-t) with N_b(t)

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

### 5.5 N_a(-t) with D_b(t)

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

## 6. Equality in the cap theorem

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

## 7. Consequence: arbitrary physical four-plus-three projection chains

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

## 8. Exact global scope

This is a direct physical seven-square terminal. It extends
SIGNED_MATCHED_CHAIN_STRESS.md by proving the required cap restriction from
actual square separation, rather than assuming vertical projection separation
of matched endpoints. Even the earlier endpoint-interlocking lemma is not
needed for the new argument.

It applies to any nine-square configuration containing these two disjoint
chains, independent of the selected stress, clear branching, chord patterns,
or orientations of the remaining two units. Both the standard sharp witness
and NO_GLOBAL_ORTHOGONAL_FRAME.md satisfy it, including the latter's oblique
pair of extra squares. A five-square cross has too few squares; the existing
exact eight-body cross has a four-chain but does not supply a disjoint
three-chain in that direction, so no false exclusion is implied.

### Full-degree transmission-path caller

In any one unchanged physical force-and-torque certificate, take two
vertex-disjoint actual paths A--U--V--B and C--W--D. Suppose U,V,W have
zero total circle load and true full positive degree two. Their unchanged
force equations propagate a common signed normal along each path. If the
two propagated normals are parallel, orient both paths consistently along
one direction e. The actual support equalities give precisely a four-square
projection chain and a disjoint three-square projection chain. Theorem 2
then proves R>=r, with its full equality information.

The endpoint degrees, endpoint loads, positive chords elsewhere in the graph,
actual application means, all physical zero-weight circle corners, and the
remaining two units are unrestricted. No edge is deleted to make U,V,W have
degree two. Parallelism is an explicit premise; crossed chains are not
covered. This caller applies unchanged within one or two cyclic blocks and
does not require a simple whole positive component.

**Still required for the unrestricted theorem:** prove a structural extraction
of such chains or a complete alternative terminal for every remaining
nine-square minimizer. No such extraction is asserted here. Until complete
original callers are joined, new original fine/coarse closures are zero.

### Review sources

- REVIEW_PHYSICAL_CAP_POSITIVE_NORMAL_AND_RECTANGLE_REDUCTION_INDEPENDENT_2026_10_31.md
- REVIEW_PHYSICAL_CAP_NEGATIVE_HALF_AND_EQUALITY_ENDBLOCK_2026_10_31.md
- REVIEW_PHYSICAL_CAP_REDUCTION_AND_CHAIN_APPLICATION_ANNULAR_2026_10_31.md

The reviews reconstruct the operative formulas, hand comparisons and complete
physical chain application. None uses numerical sampling, external mathematical
scripts, Lean, or CI.
