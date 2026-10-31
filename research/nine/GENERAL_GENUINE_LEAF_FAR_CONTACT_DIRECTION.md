# A far contact with an origin-free genuine leaf root identifies a shallow own face

Date: October 27, 2026.

**Status: complete proposed geometric theorem, frozen for full root and
independent review.** No leaf-root force equation is shortened. No
original graph label or ledger is changed.

Keep the same actual interior-disjoint unit squares in

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Let H contain O openly. Let X be an origin-free actual root of a
genuine S leaf L, with original radial leaf direction e. X may have
arbitrary additional positive forces and any true degree. The real
leaf is

    L=[d,d+1]e+[-1/2,1/2]Je,
    c_L=(d+1/2)e.                                    (1)

Let p be an actual contact point or unchanged shared-side application
between H and X, and let n be the actual unit separating normal from
H to X. Thus p maximizes n on H and minimizes n on X. Assume

    |p|>=3/8.                                        (2)

**Far-contact theorem.** There is an actual outward own normal u of H
whose face contains p and has positive height at most epsilon, such
that

    |e-n|<1/5,
    |n-u|<1/10,
    |e-u|<3/10.                                      (3)

The face normal u is a geometric choice among actual incident H
faces. The physical normal n and actual application p are unchanged.

**Two-leaf consequence.** Suppose H has actual contacts of this scope
with two distinct origin-free genuine S leaf roots X,Y, with two
distinct real leaves. If both actual applications satisfy (2), then
H has two adjacent actual own faces whose positive heights a,b both
satisfy

    0<a,b<=epsilon.                                  (4)

Their common actual vertex S therefore satisfies |S|<=sqrt(2)epsilon.
No physical contact between X and Y, degree-two equation, or force
balance at either root is assumed.

## 1. The positive support is automatically small

The complete genuine-leaf geometry gives dist(O,X)<=epsilon. Choose
an actual x in X with |x|<=epsilon. Since n supports H below X,

    0<h:=p.n=h_H(n)<=n.x<=|x|<=epsilon.               (5)

Strict positivity uses O in int H. This is independent of all X
force equations, and holds for every actual mean on a shared side.

We record a simple consequence of (2) for later use:

    9/64-(1/60)^2>(11/30)^2.                          (6)

Thus whenever one own coordinate of p has magnitude at most epsilon,
the magnitude of its other coordinate is strictly greater than 11/30.

## 2. The entire physical genuine-S root frame cover

The two following actual charts are the geometric part of the
genuine-leaf classification, independently of the number of nonleaf
forces. They may also be read directly from the true radial support
point d e on X and the actual leaf inner side.

### 2.1. Strictly tilted root

Reflect and exchange X's actual own axes so that

    e=(c_e,-s_e), c_e>=s_e>0, c_e^2+s_e^2=1,
    X=[delta,1+delta] x [-beta,1-beta],
    d e=(1+delta,-beta).

Because X avoids O, d c_e>1: the other own component d s_e is
less than one, so otherwise O would belong to X. Consequently

    0<delta<epsilon, 0<beta<11/60,
    c_e=(1+delta)/d>60/61,
    b:=1-beta>49/60.                                 (7)

The beta bound follows from beta^2=d^2-(1+delta)^2<d^2-1<121/3600.
This uses only the real leaf geometry and origin avoidance of X.

The minimum-n support in (5) is positive. The far x-face and either
horizontal own face cannot realize it: their inward normal supports
are respectively negative, -beta<=0, and -b<0. At the far two
vertices the same coordinate signs make every inward normal support
nonpositive. Thus only the near side and its two vertices remain.

The lower near vertex S_X=(delta,-beta) is too small for (2), since

    |S_X|^2<(1/60)^2+(11/60)^2<9/64.

At a relative point of the near side, n=e_x. At the upper near
vertex N_X=(delta,b), every remaining normal has the form

    n=(c_n,-s_n), c_n>0, s_n>=0,
    delta c_n-b s_n>0.

Hence

    s_n/c_n<delta/b<1/49<11/60,
    c_n>60/61.                                      (8)

The near-side axis is included by s_n=0. Both e and n lie in the
same fourth-quadrant angular interval with cosine greater than 60/61.
The absolute difference of their angles is strictly smaller than the
width of that interval. Therefore

    e.n>60/61,
    |e-n|^2=2(1-e.n)<2/61<1/25.                      (9)

This treats all actual vertex-normal endpoints and near-side means.
No positive-proper concurrence at X has been assumed.

### 2.2. Aligned root, including both transverse endpoints

Now the actual chart is

    e=e_x,
    X=[epsilon,d] x [-beta,1-beta], 0<=beta<=1.        (10)

The transverse zero lies on or within X's actual leaf-contact side.
As before, a strictly positive minimum support excludes every far
face/corner and both horizontal inward axes. Only the near side and
its endpoints remain. At a relative near-side point n=e_x and (9)
holds directly.

At a near vertex p=(epsilon,t), (2) and (6) give |t|>11/30. The
normal has positive x component and transverse sign opposite to t.
Writing n=(c_n,-sign(t)s_n), c_n>0, s_n>=0, the positive support is

    epsilon c_n-|t|s_n>0.

Thus

    s_n/c_n<epsilon/|t|<1/22<11/60,
    c_n>60/61,
    |e-n|^2<2/61<1/25.                               (11)

This includes beta=0, beta=1 and the side-axis endpoint s_n=0.
A corner at transverse zero cannot satisfy (2), so no division by
zero has occurred. Equations (9) and (11) prove the first bound in
(3) for the entire physical S-root cover.

## 3. The actual shallow own face at a far H application

At a relative-side H application, the actual n is the corresponding
own normal. Take u=n; (5) gives the required positive height, and
the middle bound in (3) is immediate.

At an H vertex, let u,v be its two incident outward own normals, and
write the unchanged actual normal as

    n=alpha u+gamma v,
    alpha,gamma>=0, alpha^2+gamma^2=1.

Set a=p.u and b=p.v. Both are positive because O is open in H.
Since alpha+gamma>=1 and h<=epsilon,

    min(a,b)<=h<=epsilon.

Relabel the incident actual faces so a is the smaller height. Then

    0<a<=epsilon,
    b^2=|p|^2-a^2> (11/30)^2,
    gamma<=h/b<1/22.                                 (12)

Consequently

    |n-u|^2=2(1-alpha)
            =2 gamma^2/(1+alpha)<=2 gamma^2,
    |n-u|<sqrt(2)/22<3/44<1/10.                       (13)

The chosen actual face contains the same original p and has height
a. This covers zero normal coefficients as well as strict vertex
normal cones; it does not modify the stress direction. Combining
(9) or (11) with (13) gives |e-u|<3/10, completing (3).

## 4. Two far-contact leaf roots force adjacent shallow H faces

Apply the theorem separately to H-X and H-Y, obtaining actual outward
H own normals u_X,u_Y with heights at most epsilon.

They cannot coincide. If u_X=u_Y, (3) gives

    |e_X-e_Y|<3/5.

The two actual S leaves have the same radial center distance d+1/2
by (1), including all original physical corner weights. Hence

    |c_LX-c_LY|=(d+1/2)|e_X-e_Y|
                <(91/60)(3/5)=91/100<1.

That contradicts the disjoint open incircles of the two distinct
actual leaves. It is not a sampled angular bound or an assertion
about a virtual leaf force point.

They cannot be opposite own normals either: the two opposite own
face heights sum to the actual width one, while both are at most
epsilon and 2epsilon<1/30<1.

The two distinct nonopposite own normals of a square are adjacent.
Their common vertex therefore has the two positive own heights in
(4), proving the stated two-leaf consequence.

## 5. Scope and useful caller distinction

All sections above are physical geometry. The only force-based datum
is that L_X and L_Y are genuine S leaves, so their actual radial
shape and common d are the true ones. The leaf roots may retain any
number of nonleaf forces. No positive radial intersection is assigned
as a shared concurrence to different edges of a higher-degree root.

If an original positive H-X application is instead small, |p|<3/8,
the same estimate (5) and the elementary incident-own-face minimum
give an actual H face through p of height at most epsilon. Beside a
genuine terminal Q0, the complete af48 outside-path theorem then
applies to the actual H-X-L path. This last sentence is a separate
caller using that theorem; the purely physical far-contact theorem
and its two-leaf consequence do not need Q0.

No conclusion about the full H resultant or the whole original
two-private-leaf diamond follows from this file alone. Those original
force and graph joins are supplied in a separate complete source.
