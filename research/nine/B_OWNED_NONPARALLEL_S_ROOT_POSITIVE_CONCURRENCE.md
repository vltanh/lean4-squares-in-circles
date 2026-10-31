# Positive concurrence at a B-owned nonparallel S root

Date: October 27, 2026.  
Author: rooted_final_review.

**Status: complete fresh analytic theorem, pending a complete independent
review.** This manuscript supplies the positive-concurrence premise of the
fresh genuine-neighbor normal form. It is a new proof from present original
inputs, not a claimed byte restoration of the missing earlier manuscript
at pin d563e080.

The new local argument is broader than that original application. It uses
the true B3 and two genuine occupied S leaves, but no force equation at H
or K, no boundary or mask premise at K, and no side-owner premise on BK.
All other physical bodies, contacts, forces and shared means remain. There
is no computational exclusion certificate.

## 1. Full local domain and conclusion

Let H, B and K be distinct, interior-disjoint unit squares in the original
disk centered at zero. They physically touch on all three pairs HB, BK
and HK. Both H and B have genuine occupied radial S leaves. In particular
their actual radial leaf applications are d e_H and d e_B, respectively,
where the e's are unit outward support directions of the corresponding
root and

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,
    epsilon = max(d-1,0) < 1/60.                         (1)

At B the actual positive forces are precisely its genuine leaf force,
HB and BK. Keep this true B3, its real positive magnitudes and its actual
force and moment equations. H and K can have arbitrary other forces and
degrees. The physical HB intersection is a singleton owned by B in the
original strict physical-normal convention. The actual B-to-H and
B-to-K normals are **nonparallel**. This is an explicit premise.

No BK owner, physical intersection type, circle contact or circle mask
is assumed. Every real BK mean, including an endpoint mean on a shared
segment, is retained.

**Theorem 1.1.** The actual three force lines at B concur at a strictly
positive point of its genuine radial leaf line. More precisely, one
whole-packing rotation/reflection gives

    d=1+delta, 0<delta<1/60,
    B=[h,h+1] x [-b,1-b],
    p_B=(1+h,-b), |h|<=delta, 0<b<31/120,
    (1+h)^2+b^2=d^2,
    P_HB=(h,-t), 0<t<b,
    q_B=sigma*p_B, sigma=t/b in (0,1).                    (2)

The actual BK normal is strict northwest or E2. Its actual force line
has positive direction from q_B to its real B application. In the strict
northwest row q_B is strictly inside B. In the vertical row its horizontal
coordinate can equal h; no strict-interiority claim is made at that real
endpoint.

The proof retains the nonparallel premise. It does not assert a whole
parallel-tip exclusion or change any original gate.

## 2. A support-height lemma for any unit square and every support type

**Lemma 2.1.** Let T be any unit square, let

    m=(-c,s), c>=0, s>0, c^2+s^2=1,

and let Q be any actual minimum-m support point of T. Then

    min { Z_y : Z in T } >= Q_y-c.                        (3)

This covers a strict vertex, a whole support side and every possible
position of Q on that side. It has no load, owner, degree or circle premise.

**Proof.** First suppose m has two nonzero components on T's orthonormal
side axes. Orient these axes e,f inward at the unique minimum-m vertex Q.
Then

    T=Q+[0,1]e+[0,1]f,
    m.e>0, m.f>0.

Both e_y and f_y cannot be negative: in the expansion

    m=(m.e)e+(m.f)f

that would make m_y<0. If both are nonnegative, (3) is immediate. If,
say, e_y<0, then m.e>=0 implies e_x<0 and

    s*(-e_y) <= c*(-e_x).

For c=0 no such e can exist. For c>0, squaring this inequality and using
e_x^2+e_y^2=1 and c^2+s^2=1 gives

    e_y^2 <= c^2.

The other axis has nonnegative height component. Moving anywhere in the
actual square can therefore lower the height by at most -e_y<=c.

If one component of m on the square's side axes is zero, T has a whole
minimum-m side. Take its inward normal axis to be m and its downward
tangential axis to be e=(-s,-c). For some actual tau in [0,1],

    T=V+[0,1]e+[0,1]m, Q=V+tau*e.

Thus min_T y=V_y-c=Q_y-(1-tau)c>=Q_y-c. This includes tau=0, tau=1 and
c=0. Those cases exhaust every square support face. QED.

In particular, the later height estimate will not replace a genuinely
free BK contact by an owned one or choose a new shared mean.

## 3. The actual triangle and genuine B3 determine the entire B chart

The genuine S-leaf theorem and the inward-unit-segment lemma give an
actual point of each root in the closed epsilon disk. If d<=1 the radial
segment contains zero; if d>1 its inner endpoint is (d-1)e. Both roots
are physically circle-clear, because every point in either root has norm
at most epsilon+sqrt(2), and

    epsilon+sqrt(2)<1/60+17/12=43/30<79/40<=R.             (4)

Thus no circle atom is omitted from the actual B3 law. No equation at H
is needed.

Let n be the actual B-to-H normal and m the actual B-to-K normal. Since
B owns n and H,B,K physically form a triangle, the physical side-normal
obstruction gives n.m>=0. With strictly positive magnitudes, the true
force law is

    lambda*e_B + mu*n + nu*m=0.                          (5)

Its n component gives lambda*(e_B.n)=-mu-nu*(n.m)<0. Rotate the whole
packing so n=-E1. Then (e_B)_x>0. Write B's minimum-x support as x=h.
H is on the other side of this same support line. The actual near-origin
points in H and B give

    -epsilon<=h<=epsilon.

The genuine radial support application lies on B's right side, so

    d*(e_B)_x=1+h.                                      (6)

If d<1, then epsilon=h=0 and (6) is impossible. At d=1 it forces
e_B=E1; the vertical component of (5) would make m horizontal, contrary
to the actual nonparallel premise. Consequently d=1+delta with
0<delta<1/60 and |h|<=delta. The same force equation excludes a horizontal
e_B anywhere in the remaining domain.

Reflect the whole packing vertically so (e_B)_y<0. Since (e_B)_x>0 and
(e_B)_y<0, its actual radial support is B's lower-right vertex. Therefore

    B=[h,h+1] x [-b,1-b], p_B=d*e_B=(1+h,-b),
    (1+h)^2+b^2=d^2,
    0<b<=2sqrt(delta)<31/120.                            (7)

Here b^2<=4delta follows from 1+h>=1-delta>0, and the final strict
comparison follows from

    (31/120)^2-1/15=1/14400>0.

The physical singleton HB is owned by B, so its actual point P lies in
the relative interior of B's left side and is a strict maximum-x vertex
of H. This is the original physical convention: a vertex/vertex singleton
uses a normal strictly inside both vertex cones, so its normal cannot be
B's side axis. A coframed singleton is likewise vertex/vertex and cannot
be substituted here. Write

    P=(h,p), -b<p<1-b.                                  (8)

The genuine radial line at B and the actual horizontal HB line meet at

    q_B=sigma*p_B, sigma=-p/b.                          (9)

This is a finite intersection because b>0. The actual torque equation
about q_B makes the unchanged BK force line pass through q_B: the leaf
and HB moments about that point vanish, and nu>0. This is the actual
three-force concurrence, not a newly selected point or normal.

Finally, n.m>=0 gives m_x<=0. The vertical component of (5) gives
m_y>0. The entire possible m range is strict northwest or E2.

## 4. Every nonpositive concurrence gives the same small HB point

Suppose for contradiction that sigma<=0, equivalently p>=0. Keep the
actual contact types and all real applications.

If m=(-c,s) is strict northwest, B's unique maximum-m support is its
actual upper-left vertex

    Q=(h,1-b), c,s>0, c^2+s^2=1.

The vertical component of Q-q_B is 1-b-p>0 by (8). Since Q-q_B is
parallel to the actual upward m, the proportionality is positive. Its
negative horizontal component gives

    (1+h)p < -h*b.                                     (10)

This is valid regardless of which body owns BK, and also if its normal
is free. If m=E2, the actual BK mean must instead be

    Q=(sigma*(1+h),1-b).

Its membership in B's real top side gives Q_x>=h, hence

    (1+h)p <= -h*b.                                    (11)

The non-strict endpoint is retained. This covers both singleton and
shared BK, using its unchanged actual mean.

Since 1+h>0 and p>=0, both rows imply h<=0. Put a=-h in [0,delta].
Equations (10)--(11) give the common necessary interval

    0<=p<=a*b/(1-a).                                   (12)

For a>0, every division is safe because 1-a>59/60. The uniform bound is

    b/(1-a)<(31/120)/(59/60)=31/118<1/3,
    0<=p<a/3<1/180.                                    (13)

No root force ratio, angle or side mean has been optimized to obtain
this interval.

## 5. The zero endpoint and the full genuine H-leaf cover

If a=0, (12) gives p=0, so the actual strict rightmost H vertex is the
origin. Write H=[0,1]u+[0,1]v in its inward orthonormal axes. Any genuine
radial support application d*e in H has nonnegative coordinates. Each
strictly positive component of e forces the corresponding coordinate of
d*e to be one, while a zero component gives coordinate zero. If precisely
one component is positive, d=1; if both are positive, d=sqrt(2). Both
contradict 1<d<61/60<sqrt(2). This excludes a=0 without dividing by a.

Now take a>0. Since P=(-a,p) is a strict maximum-x H vertex, its actual
inward axes have the form

    u=(-alpha,beta), v=(-beta,-alpha),
    alpha,beta>0, alpha^2+beta^2=1,
    H=P+[0,1]u+[0,1]v.                                 (14)

The actual own-coordinate bound is

    P.u=alpha*a+beta*p>0.                              (15)

Every H point has u projection at least P.u. The genuine radial
application d*e_H therefore has e_H.u>0. Consequently it must use H's
maximum-u face. This conclusion does not use an H3 law or remove any
other force at H.

The opposite vertex P+u+v cannot be that radial application. Indeed
(13), a<1/60 and the triangle inequality give

    |P|<=a+p<4a/3<1/45<1/30,
    |P+u+v|>=sqrt(2)-|P|>7/5-1/30=41/30>61/60>d.       (16)

There are now exactly three possible signs of e_H.v:

* If e_H.v>0, the actual support is P+u+v, excluded by (16).
* If e_H.v<0, the actual support is P+u. Its v coordinate is
  P.v=d*(e_H.v)<0.
* If e_H.v=0, the genuine radial application lies somewhere on the
  actual whole maximum-u side P+u+[0,1]v. Its v coordinate is zero,
  so P.v<=0. Both side endpoints are retained.

This exhausts every genuine H radial vertex and every aligned radial
side mean. It yields the necessary inequality

    P.v=beta*a-alpha*p<=0,
    beta/alpha<=p/a<1/3,
    beta<1/3.                                         (17)

At p=0 the first inequality already contradicts beta*a>0; retaining the
common upper bound below does not discard that endpoint. Every point of
the entire actual H has height at most

    max_H y=p+beta<1/180+1/3=61/180.                   (18)

Thus the real leaf alone forces the whole root low under the contrary
concurrence sign, with no restriction on H's other contact types.

## 6. Both actual BK directions force the whole K above H

In the vertical row m=E2, K lies above the real B support side, so

    min_K y=1-b>89/120>43/60.                           (19)

For a strict northwest m=(-c,s), the same real Q and q_B used in (10)
give the exact ratio

    c/s=[a-(1-a)*p/b]/[1-b-p].                          (20)

The numerator is positive and at most a. The denominator is strictly
positive; more explicitly, (7) and (13) give

    1-b-p>1-31/120-1/180=53/72>2/3.

It follows that

    0<c/s<(3/2)*a<1/40,
    0<c<1/40.                                         (21)

Q is an actual minimum-m support point of K, whatever its physical
owner type. Apply the complete support-height Lemma 2.1. It retains the
entire actual K and yields

    min_K y>=Q_y-c=1-b-c
           >1-31/120-1/40=43/60.                       (22)

In particular a free BK normal or an endpoint shared mean supplies no
unexamined exception. No K circle point, force, mask or degree enters
this bound.

Equations (18), (19) and (22) strictly separate the physical squares H
and K, since

    43/60-61/180=17/45>0.

This contradicts the required actual HK contact. Hence the entire
nonpositive alternative is impossible: sigma>0.

## 7. The precise positive chart and the fresh original-domain join

With t=-p, equations (8)--(9) and sigma>0 give

    0<t<b, sigma=t/b in (0,1).

These are the exact positive-concurrence conclusions in Theorem 1.1.
For a strict northwest BK, the real point Q=(h,1-b) and m_x<0 give
q_Bx>h; sigma<1 gives q_Bx<h+1. Also -b<q_By=-t<0<1-b. Thus q_B is
strictly inside B, and both real nonleaf force applications lie strictly
outward from it along their actual normals.

For vertical BK the actual mean is Q=(q_Bx,1-b). It has q_Bx>=h, with
equality allowed, and q_Bx<h+1. The actual BK application is still strictly
above q_B; HB can have q_B=P at the left endpoint of the real shared-BK
mean. No strict-interiority conclusion is imported into this endpoint.

In the original hub-tip graph

    HK, HB, BK, HC, CK, HL_H, BL_B,

retain all H4/K3/B3/C2 forces, both genuine S leaves and all three extra
physical units. On the B-owned singleton-HB subfamily, the present result
supplies the positive-concurrence premise of

`POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md`,

at pin 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce.
Its whole eight-section independent acceptance is pinned below. That
source has the same actual nonparallel premise, the same original radius
range, the same real root/leaf and singleton conventions and the same
true B3. Its separate original BK side-owner input remains necessary for
its later detailed K-owned oblique chart; the present sign theorem itself
does not need it.

Therefore the complete genuine-neighbor normal form can now be applied
on its stated original B-owned/nonparallel domain without a separately
assumed sign of the B concurrence. This is an exhaustive analytic removal
of one starting hypothesis, not a claim that the original parallel-B
family, physical C-mask reduction or central-singleton theorem has been
recovered. Those exact original-adoption obligations remain separate.

## 8. Exact present inputs and verification boundary

The complete local proof uses only these three present original inputs:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine occupied S leaves, true radial support applications and whole inward unit segments |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual B3 force and moment equations, original strict singleton convention, unchanged shared means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | The physical triangle sign n.m>=0 at B's actually owned HB side |

The separate full original-domain join in Section 7 uses:

| Source or complete review | SHA256 |
| --- | --- |
| POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md | 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce |
| REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md | 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d |

Every new estimate is proved on its complete continuous domain. The
support lemma includes every actual vertex and side support; the H-leaf
argument includes every genuine aligned side mean; the B force-line
argument keeps both physical BK directions and their real endpoints.
The positive result uses no owner selection at BK, no K2 or H3 law, no
C equation, no circle mask at K, no angle subdivision and no finite
computational exclusion packet.

Exact rational and coordinate checks accompany the source. They check
the displayed identities and fixed reserves, not a list of numerical
poses. All older frozen source bytes remain unchanged. No original gate,
ledger, remote source, Lean file or CI workflow is changed.
