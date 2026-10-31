# Two S-tip triangles cannot have an aligned nonparallel S articulation

Date: October 27, 2026.

**Status: accepted complete whole-interface hand exclusion after full
root and separate independent reviews in
REVIEW_TWO_S_ALIGNED_NONPARALLEL_AND_TILTED_PW_ROOT_2026_10_27.md and
REVIEW_TWO_S_TIP_TRIANGLES_ALIGNED_NONPARALLEL_TRIANGLE_BRIDGES_2026_10_27.md.**
This closes every original high-radius
S/S configuration of the final C2.33.b2 attachment in which at
least one genuine S root is aligned with its leaf and has
nonparallel triangle normals. The other root retains every actual
frame, contact owner and physical circle mask.

## 1. Original graph, origin-interior hub and an aligned S root

Keep the original positive graph

    HA, AB, BH, HC, CD, DH, AL, CM,

with genuine S leaves L,M, actual degrees H4,A3,C3,B2,D2,L1,M1,
and the same two arbitrary completion squares. The earlier
high-radius reductions give

    O in int H,
    H,A,C physically circle-clear,
    B,D loaded,
    both actual triangle cycle moments nonzero.

Here

    ell=sqrt(R^2-1/4)-1,
    delta=ell-1,
    0<delta<1/60,
    r=R-sqrt(2)>129/200,
    103/50<R<21/10.

These are TWO_S_TIP_TRIANGLES_HIGH_RADIUS_HUB_CLEARANCE.md and
TWO_S_TIP_TRIANGLES_HUB_ORIGIN_INTERIOR.md. In particular all
external aggregate identifications below occur after H's physical
clearance, and retain its four original pair forces.

Assume A is aligned and its triangle normals are nonparallel.
Rotate L east and reflect vertically to put B at the upper of
the two actual left vertices. The complete local A-star cover is

    A=[delta,delta+1] x [-w,h],       h+w=1,
    P=(delta,h) in A intersect B,
    Q=(delta,-w) in A intersect H,
    0<h,w<1.

The original compatible A-star determinant selection makes both
normals neighbor-owned, with P and Q in the relative interiors
of their actual B and H sides. This is the prelisted degree-three
aligned S star of
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md, Section 1;
its determinant uses no equation or load assumption at H. Keep

    n=(-b,a),       v=Jn=(-a,-b),
    m=(-d,-c),      k=Jm=(c,-d),
    a,b,c,d>0,      a^2+b^2=c^2+d^2=1,
    K=ad+bc>0,      L=bd-ac,

where n points A to B and m points A to H. The leaf magnitude
is normalized to one. A's unchanged force and torque equations
are exactly

    mu=c/K,        nu=a/K,
    h=ad/K,        w=bc/K,
    n=L m-K k,     v=K m+L k.                           (1)

Let g be the actual B-to-H normal and gamma>0 its magnitude.
Put N=F_D+F_M, the whole original opposite branch resultant.
The full B and H equations are

    F_B=mu n-gamma g,        N=nu m+gamma g.             (2)

## 2. All preliminary frame estimates concern only the actual A,B,H triangle

Define the actual H coordinates of Q by

    q_m=Q.m=-delta d+w c,
    q_k=Q.k=delta c+w d>0.                              (3)

Because O is in int H and Q minimizes m on H,

    -delta<q_m<0.                                      (4)

The boundary body B contains P, so |P|>=r. The exact comparison

    (129/200)^2-1/3600>(16/25)^2

gives h>16/25.

The complete local B-mask calculation in Sections 3--4 of
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md applies with
(4) supplied directly by origin-interior H. None of those
calculations uses its later intact opposite petal. For clarity,
the exact facts and bounds used here are recalled next.

Put

    p_n=P.n=-delta b+h a,
    B_0=-P.v=delta a+h b>0.

Since p_n<1<ell, B is not radial along its owned axis n;
its transverse and negative radial axes are impossible from
B_0>0 and its positive center n-coordinate. Thus B has a unique
physical circle corner. A parallel B force pair would make that
unique circle vector parallel to its actual owned side axis n,
which is impossible. Its genuine proper concurrence is therefore
a positive multiple of that unique corner and has advance

    A_B=X B_0/Y-p_n>=0,
    X=1+p_n,
    Y=B_0+rho,
    0<rho<1,
    X^2+Y^2=R^2.                                       (5)

In particular its exact radial-advance inequality implies

    p_n(R-|P|)<=|P|.                                   (6)

The original scalar comparisons establish

    L>0,          a^2<h,          a<19/20,
    b>sqrt(39)/20>3/10.                               (7)

Here is the arithmetic scope of those comparisons. If L<=0,
then a^2>=h, p_n>=h sqrt(h)-delta sqrt(1-h), and
|P|<h+1/4608. Concavity gives
sqrt(h)(103/50-h)>=53/50 on [16/25,1]. The left side
minus right side in (6) is consequently greater than

    24/625-71/5000-1/2304=34223/1440000>0,

a contradiction. If a>=19/20, the already proved a^2<h
gives h>361/400, b<5/16, p_n>19h/20-1/192 and
|P|<h+1/6400. The corresponding lower difference in (6) is
the concave quadratic

    (19h/20-1/192)(103/50-h-1/6400)-h-1/6400.

Its values at h=361/400 and h=1 are respectively
1069997/12800000 and 2407/2048000, both positive. This proves
all of (7) using only the real B body and its original equations.

## 3. Both complete mutual-owner cases and their actual means

Since B owns n and H owns m, the physical triangle side-normal
lemma gives

    n.g<=0,              m.g>=0.                       (8)

With K,L>0, a B-owned mutual normal can only be g=v, and an
H-owned mutual normal can only be g=k. A free mutual normal is
removed by the already compatible GENERAL_FIXED_TIP_NORMAL_SELECTION:
B is physically unique, its AB application P is fixed in its
owned side interior, and a free BH application would be a distinct
B vertex. The original finite prelist permits arbitrary H degree
and masks. No extracted point normal is reselected.

Keep the full actual frames

    B=P+[0,1]n+[-rho,1-rho]v,
    V=1-rho in (0,1),
    H=Q+[0,1]m+[-sigma,1-sigma]k,
    0<sigma<1.                                         (9)

Every original BH mean is retained. The complete contact identities
are as follows.

If g=v, its actual application is

    T=P+t n+V v=Q-sigma k,       0<=t<=1,
    t=(c-KV)/L,
    sigma=(b-V)/L.                                     (10)

If g=k, its actual application is

    T=P+V v=Q+j m-sigma k,       0<=j<=1,
    j=KV-c,
    sigma=d-LV.                                        (11)

These are just the two physical contact-coordinate identities;
the endpoints t,j=0,1 have not been removed. In both cases (2)
and (1) give

    N.m>0,       N.k>0.                                (12)

Indeed g=v=Km+Lk in (10), while g=k in (11).

## 4. A small neighbor forces every common H face to have small height

We use a general local observation at the actual origin-interior
H. Suppose a genuine triangle pair has resultant S, nonzero
common cycle moment and proper concurrence q=-tau S, tau>0.
Suppose both actual H ports lie on the same actual H face,
whose outward axis is e and whose height is A>0. Then each
actual port support is at least A.

To prove this, use e as first coordinate. Both outward normal
e-components are nonnegative, and S.e>0. Properness from
q.e=-tau S.e<0 to the face e.x=A makes both components strictly
positive. Write the original ports as (A,y_i) and normals n_i.
Zero origin moment gives

    S_y/S_x = positive weighted mean of y_i/A.

The exact proper-line slope is

    (n_i)_y/(n_i)_x
      =(y_i+tau S_y)/(A+tau S_x).

At an upper endpoint the weighted mean is at most y_i/A;
at a lower endpoint it is at least y_i/A. For an owned face
normal the transverse component is zero. Multiplying by the
correctly signed transverse component yields in every case

    p_i.n_i>=A/(n_i)_x>=A.                             (13)

The actual S root C contains its genuine point delta e_M.
For its original H-to-C normal n_C, the true separating support
therefore satisfies

    h_H(n_C)<=n_C.(delta e_M)<=delta.                  (14)

Consequently, if C is one of the two neighbors on the common
face in this observation, that face has height A<=delta.
There is no boundary or degree-two assumption at C.

## 5. The whole opposite triangle forces H's upper k-face below delta

Let

    p_k=q_k+1-sigma>q_k>0                              (15)

be the actual maximum k-coordinate of H. The other H face
in the positive m direction has height 1+q_m>1-delta.

Apply the complete physical triangle root-feature cover to the
original H,C,D triangle. Its pair sum is exactly N and its
nonparallel concurrence is a negative multiple of N, with every
proper port retained. A parallel pair cannot occur here: by
(12) its common direction would strictly expose H's unique
maximum-m/maximum-k vertex, making the common cycle moment zero.

Unless the two H normals are perpendicular H-owned axes, the
two applications lie on one actual H face. This is the pure
triangle feature cover: an owned axis and a strict vertex lie
on that axis face; two strict distinct vertices must be adjacent;
coincident strict ports are impossible here. Indeed their genuine
concurrence would be their common point p=-tau N, whereas
O in int H gives p.N=sum_i mu_i h_H(n_i)>0, contradicting
p.N=-tau|N|^2<0.
By (12) the common face can only be the positive-m face or the
positive-k face. The former has height 1+q_m>1-delta>delta and
is impossible by (13)--(14). The latter gives p_k<=delta.

In the exceptional perpendicular H-owned case, (12) makes the
two axes exactly +m,+k. C cannot use +m because that actual
support is 1+q_m>delta. Thus C uses +k, and (14) again gives

    0<q_k<p_k<=delta.                                 (16)

This covers the perpendicular exception directly, without applying
the two-loaded-tip perpendicular theorem to the genuine degree-three
S root C.

## 6. Both actual owner formulas put the B contact too near one side endpoint

Equations (3)--(4) and (16) give

    w c<delta d,         w d<delta.                    (17)

Since c^2+d^2=1, these imply w<sqrt(2)delta<1/40 and
h>39/40. From (1),(7),

    c/d=w a/(h b)<10/117<1/11,
    d>99/100.

Now w d<delta improves the bound to

    w<5/297<1/59,      h>58/59,
    c/d<5/87<1/17,    c<1/17.                         (18)

By (15)--(16), sigma>1-delta>59/60. In case (10),

    V=b-L sigma
      =b(1-d sigma)+a c sigma
      <delta+(1-d)+c
      <1/60+1/289+1/17
      =1369/17340<2/25.                               (19)

Here 1-d=c^2/(1+d)<c^2 was used. In case (11),

    L=b d-a c>(3/10)(99/100)-1/17>7/30,
    V=(d-sigma)/L<delta/L<1/14<2/25.                  (20)

Thus the same strict bound V<2/25 holds for every original
contact owner and every actual BH mean.

## 7. The genuine B circle corner lies outside the containing circle

The actual unique B circle corner in (5),(9) is

    z=P+n-rho v=P+n-v+V v.

Since P=(delta,h), n=(-b,a) and v=(-a,-b),

    P+n-v=(delta+a-b, h+a+b).

Using a+b>=1, h>39/40 and the reverse triangle inequality,

    |P+n-v|
      >=sqrt((a-b)^2+(h+a+b)^2)-delta
      >=sqrt(h^2+2h+2)-delta
      >11/5-delta.

The last strict comparison follows already from
(39/40)^2+2(39/40)+2=7841/1600>121/25.
Equations (19)--(20) now yield

    |z|>=|P+n-v|-V
        >11/5-1/60-2/25
        =631/300>21/10>R.                             (21)

But z is an original physical circle corner and has norm exactly R.
This contradiction excludes the whole aligned nonparallel A case.
Exchanging A,B,L with C,D,M gives the same conclusion for C.

Every original force, graph degree, contact normal, side mean,
physical circle mask and completion square remains unchanged.
The proof uses the other triangle only through its full original
equations, nonzero cycle moment, and its genuine S root's small
point. It imports no intact-petal pressure, loaded-tip degree at C,
or sampled geometric pose. The aligned parallel and tilted S-root
alternatives remain separate original obligations.
