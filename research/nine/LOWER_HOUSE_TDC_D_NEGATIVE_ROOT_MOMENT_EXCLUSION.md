# Complete negative-root-moment half of the thin lower-house TDC.D family

Date: October 28, 2026 UTC. Author: thin_d continuation.

**Status: complete proposed hand exclusion of the whole stated original
moment-sign domain, submitted for full root and independent review. The
positive-root-moment alternative remains open; no whole original fine
or coarse checkbox is changed by this source alone.**

This proof uses the actual C--D contact in addition to the complete
unloaded A3 star. It excludes every original side mean, original contact
owner, radial leaf slider, boundary mask and zero circle weight in its
domain. There is no numerical exclusion certificate or angle partition.

## 1. Exact physical domain and sign convention

Keep the original lower-house graph

    AT, DT, AD, AB, BC, CD, BL,

with a genuine D leaf L at B, positive block circle loads exactly T,D,C,
and true degrees B3,A3,D3,T2,C2,L1. All nine physical squares remain.
Use the actual canonical upper shallow B chart from the accepted thin
support reduction:

    B=[-s,r] x [-b,a0],
    r=R-sqrt(2), s=1-r,
    0<a0<=epsilon<1/60, b=1-a0>59/60,
    d=sqrt(R^2-1/4)-1=1+epsilon>1,
    R<=sqrt(1105)/16.

The genuine leaf is on the East side, with original B force alpha_L*East
at (r,0), alpha_L>0. The actual B-to-A normal n has positive y-component
and satisfies |n_x|<1/20 and 0<h_B(n)<=epsilon. No axis is subsequently
reflected to change the following sign:

    m_BA=det(p_BA,n)<0.                                (1)

The complete reduction
`LOWER_HOUSE_TDC_D_FULL_MOMENT_AND_NONRADIAL_RETURN_REDUCTION.md`
gives the following literal actual A properties. A avoids O, is clear,
and in a positively oriented own frame (e,f), f=Je, has

    A=[a,A0]e+[b0,c]f,
    A0=a+1, 0<a<=epsilon, b0<=0<=c, c-b0=1.            (2)

Its original AB moment is positive, and both original AT and AD moments
are strictly negative. All three forces remain. Its exceptional original
A-to-B feature is either West, with actual positive-height mean, or
Northwest at a*e+c*f. In the latter case write the normal (-u,v) in
this own frame, with u,v>0, u^2+v^2=1 and

    c*v<a*u.                                          (3)

The present source proves that the entire domain (1) is impossible.
The full positive-moment domain m_BA>0 is not identified with it by
a reflection: such a reflection changes which side holds the real leaf.

## 2. Three elementary physical support facts

The actual containing disk gives every actual center C the bound
|C|<M=91/60. An actual unit beyond a unit-normal support f.z>=h has
C.f>=h+1/2, so h<=d. Each point of an actual unit is within 1/sqrt(2)
of its center. Distinct actual centers are at least one apart.

### 2.1. A high support occupies one narrow cap

If h>1 and a support normal has own-frame coordinates

    n=(x,y), x>60/61, |y|<11/61,

then the neighbor's actual center satisfies

    C_x>K=3501/2440,
    |C_y|<1/2.                                        (4)

The first bound follows from C.n>3/2 and
|C.Jn|<sqrt(181)/60<27/120. The second follows from
M^2-K^2<1/4. The squared diameter of a containing rectangle is

    (M-K)^2+4*(M^2-K^2)=52124381/53582400<1.

Thus at most one actual unit can occupy this cap. Every East normal
with support greater than one is included. These are physical bounds
on the actual neighbor, without a change of its selected force normal.

### 2.2. A unit wholly beyond x>1 has a uniform transverse strip

Let E be any actual contained unit with every point satisfying x>=h>1.
Then every point of E satisfies

    |y|<61/100.                                       (5)

To prove this for its complete orientation range, let k=min_E x>1.
Choose signs of its actual own axes, reflecting the transverse coordinate
if needed, so its inward axes from a minimum-x vertex have x-components
C,S, where C>=S>=0 and C^2+S^2=1. Its x width is C+S. The actual
center bound gives

    C+S<2*M-2=31/30.

The function sqrt(1-S^2)+S is increasing for 0<=S<=1/sqrt(2).
At S=1/25 it is greater than 1-S^2+S=649/625>31/30. Thus
S<1/25 and C>499/500. Two adjacent actual vertices have x-coordinate
at least k+C>999/500, so containment gives absolute y-coordinate
strictly below 57/100. The exact squared comparison is

    1105/256-(999/500)^2 < (57/100)^2.

Each other vertex differs in y from one of these two by S<1/25.
Hence all four vertices, and by convexity the whole actual square,
satisfy |y|<57/100+1/25=61/100. This also includes the parallel
orientation and every minimum-support side endpoint.

### 2.3. Height estimates at an actual support point

Suppose P is an actual minimum-normal support point of a unit E.
If its inward normal is (-u,-v), 0<=u<v and u^2+v^2=1, then

    max_E y <= P_y+u,
    (c_E)_y <= P_y-(v-u)/2.                            (6)

For a vertex support, its two inward orthonormal axes w_1,w_2 have
nonnegative dot products with (-u,-v). At most one can have positive
y-component, and that component is at most u: the normal inequality
gives v*w_y<=u*sqrt(1-w_y^2). This proves the first bound. For the
center write q_i=(-u,-v).w_i>=0. Then q_1^2+q_2^2=1,
q_1+q_2>=1, and |q_1-q_2|<=1. Resolving w_1+w_2 along the normal
and its perpendicular bounds its y-component by -v+u, proving
the second bound. At an owned-side mean,
c_E-P=(1/2)(-u,-v)+t*J(-u,-v), |t|<=1/2, and the same two
estimates follow from the whole actual tangent interval of length one.

We will also use the simpler bound

    (c_E)_y >= P_y-1/2                                 (7)

whenever the inward normal at P has nonnegative y-component. At a
vertex, the same q_1+q_2 and q_1-q_2 decomposition bounds the center's
vertical displacement below by -|n_x|/2>=-1/2. At a side mean its
vertical displacement is n_y/2+t*n_x>=-1/2. Thus (7) holds for every
actual minimum-support feature and original mean.

## 3. The actual B3 equation confines the whole boundary C low in the disk

Write n=(-k,eta) for the B-to-A normal. Equation (1) forces

    0<=k<1/20, eta>399/400.                            (8)

Indeed a positive n_x would expose the upper-right B vertex (r,a0),
whose moment r*n_y-a0*n_x is strictly positive. For n_x=0 the
actual North-side mean in (1) has negative x-coordinate. For n_x<0
the actual point is the upper-left vertex. The quantitative eta
bound follows from |n_x|<1/20 and |n|=1.

The original full B3 force and torque equations give the actual C
normal a strictly negative vertical component and its original B
moment a strictly positive sign. Write the normal as (p,-v), v>0.
If p>0, its point is (r,-b), and positive moment requires p/v>r/b.
But full B3 force balance, with unchanged positive magnitudes gamma
on BA and beta on BC, gives gamma*eta=beta*v and

    alpha_L+beta*(p-v*k/eta)=0,

so p/v<k/eta<1/19. This is impossible because strict high radius
gives r>16/25. Thus p<=0.

For p=0 the actual C support is on the bottom B side. For p<0 put
p=-u, u>0; its point is (-s,-b), and positive origin moment gives

    s*v-b*u>0,
    0<u/v<s/b<108/295<3/8.                            (9)

Here s<9/25 follows from R>sqrt(17)/2>103/50 and sqrt(2)<99/70,
which give r>113/175>16/25. In particular u<v. Also (9) gives
u<108/sqrt(98689)<7/20. The South case has u=0,v=1 and satisfies
the same subsequent bounds.

Apply (6) at the actual point on y=-b. Since

    v-u>5/sqrt(73)>7/12,

the actual C satisfies both complete physical bounds

    (c_C)_y < -59/60-7/24 = -51/40,
    max_C y < -59/60+7/20 = -19/30.                    (10)

The inequality 5/sqrt(73)>7/12 has squared reserve
3600-49*73=23>0. Nothing here uses a two-force equation at C:
its full actual loaded C2 system remains intact and is unnecessary
for these purely B-star/physical inequalities.

## 4. The full A3 star has exactly one high-support return

Use the actual own chart (2). Call a negative-moment return exceptional
if it is an East-axis force at (A0,Y) with Y>0, or a Northeast force
(f,t), f,t>0, at (A0,c) with

    A0*t<c*f.                                         (11)

Every such return puts its actual neighbor in (4). For the East case
the support is A0>1. In (11), the support is at least A0/f>1/f;
h<=d gives f>1/d>60/61 and t<11/61. Thus at most one of the two
distinct actual T,D returns can be exceptional.

There must be at least one. Otherwise all negative-return features
are West, South, Southwest or Southeast. For a West AB force, full
vertical balance would force all returns West, and horizontal balance
would fail. For a Northwest AB force (-u,v), full torque about
(A0,b0) gives v>=u. Negative exceptional support then gives a>c.
Full torque about (a,c), together with full horizontal balance, supplies
an actual Southeast return (f,-t) with f>=t>0. Its strictly negative
origin moment requires

    t/f>(1-c)/A0>59/61.

Its support is strictly greater than cos(theta)+(59/60)sin(theta),
where theta=atan(t/f) is in [atan(59/61),pi/4]. This concave function
has endpoint values 7141/(60*sqrt(7202)) and 119/(60*sqrt(2)); both
exceed 61/60. That contradicts its actual support h<=d.

Therefore exactly one return occupies the cap. Call its actual unit V,
and call the other W. The physical V--W contact is the original TD.
The owned-axis triangle theorem and the opposite-vertex support-span
theorem give the entire remaining feature list:

* If V has an East normal, W is South at an actual mean (x,b0),
  a<=x<=A0, or strict Southeast at (A0,b0).
* If V is strict Northeast at (A0,c), W is strict Southeast at
  (A0,b0). West and South contradict the actual owned-axis triangle
  dot product; Southwest at (a,b0) is an opposite-vertex contact
  whose outer unit is closed-disjoint from V.

This is the full continuous feature cover, with every original mean.
No extra contact, chosen normal, or artificial two-force equation is used.

## 5. Relating the actual A frame to the fixed canonical B frame

For a West AB force put u=1,v=0. For Northwest keep u,v from (3).
Then the actual B-to-A normal is

    n=u*e-v*f,
    e=u*n+v*Jn, f=Je.

By (8),

    e_x=-u*k-v*eta<=0,
    e_y=u*eta-v*k.                                    (12)

The quantity e_y is strictly positive. This is immediate for West.
For Northwest, the unchanged application a*e+c*f lies on the actual
upper B side or vertex, so its global height is

    a0=a*e_y+c*e_x>0.

Since a>0,c>=0,e_x<=0, this forces e_y>0.

Put kappa=v/u. When kappa<=1,

    e_y >= (eta-k)/sqrt(2)
         >379/(400*sqrt(2)) > 2/3.                    (13)

The last squared reserve is 1137^2-2*800^2=12769>0.

If V is strict Northeast, necessarily kappa<1. A West AB force
already has kappa=0. For Northwest let the actual V normal be (f,t)
and W normal (s,-w), with original magnitudes mu,nu. Full torque
about (a,c) gives mu*t+nu*(s-w)=0. Full vertical balance therefore
gives lambda*v=nu*w-mu*t=nu*s, whereas horizontal balance gives
lambda*u=mu*f+nu*s>lambda*v. This proves kappa<1 without deleting
any A force.

Thus the only kappa>=1 alternative to consider beyond (13) has V
East and AB strictly Northwest. In it (3) gives c<a<=epsilon.
The AB application has norm below sqrt(2)*epsilon<1/3<s, so it
cannot be the upper-left B vertex. Equation (8) therefore makes
n exactly North. Consequently

    e=(-v,u), f=(-u,-v), v>=1/sqrt(2),
    0<=c<epsilon, b0=c-1.                             (14)

These are actual frame deductions. They are not a reflection exchanging
the original sign domain with its unproved companion.

## 6. Every kappa<=1 return center lies strictly above one sixth

First suppose kappa<=1. For the cap unit V, (4),(12),(13) give

    (c_V)_y = e_y*(c_V)_e + e_x*(c_V)_f
             > (2/3)*(7/5)-1/2 =13/30>1/6,           (15)

using K>7/5 and |(c_V)_f|<1/2.

If W is Southeast, its actual application Q=A0*e+b0*f has

    Q_y=A0*e_y+b0*e_x>2/3,

because A0>1,b0<=0,e_x<=0. Its inward W normal s*e-w*f has
strictly positive global y-component s*e_y-w*e_x. The full actual
support-point bound (7) gives (c_W)_y>2/3-1/2=1/6.

If W is South, this can occur only when V is East. W lies in its
own coordinate half-plane y<=b0, hence (c_W)_f<=b0-1/2<0. The
actual V--W contact contains a point with e-coordinate at least A0,
so (c_W)_e>=A0-1/sqrt(2)>1/4. Equations (12),(13) give

    (c_W)_y=e_y*(c_W)_e+e_x*(c_W)_f>1/6.              (16)

Thus both actual T and D centers lie above 1/6. But (10) puts C's
center below -51/40. The original D--C contact would require center
distance at most sqrt(2), whereas their vertical distance is strictly
greater than

    51/40+1/6=173/120>sqrt(2).

The last squared reserve is 173^2-2*120^2=1129>0. This excludes
the entire kappa<=1 domain, including all West exceptional stars.

## 7. The remaining East-cap/kappa>=1 domain is also impossible

Use (14). The actual East-cap unit V lies in own x>=A0>1, so the
whole-square transverse theorem (5) applies. Every actual Z in V has

    Z_y=u*Z_e-v*Z_f > -61/100.

Indeed u>0, Z_e>1 and |Z_f|<61/100, while 0<v<=1. But every
point of C has height less than -19/30 by (10), and
-19/30<-61/100. Therefore V and C are closed-disjoint. The actual
D cannot be V, since D--C is an original physical contact.

For the other return W, either its South mean (x,b0) or its
Southeast point (A0,b0) has global height

    u*x+v*(1-c) > (59/60)/sqrt(2) > 2/3,

where x>=a>0 and (14) is used. In both features its inward actual
normal has positive global y-component. Bound (7) gives
(c_W)_y>1/6. If D=W, the same strict center separation from C
in Section 6 contradicts D--C contact.

The two actual alternatives D=V or D=W are exhaustive. Thus this
last whole domain is excluded as well. The weak kappa=1 endpoint
was included in both valid estimates and is not left to a limit.

## 8. Scope and exact remaining original alternative

Sections 1--7 prove the entire original lower-house TDC.D domain
with m_BA<0 in the canonical shallow-top, leaf-East chart. The
original AB moment cannot be zero by the preceding complete moment
reduction. Therefore the whole remaining original family now has only

    m_BA>0                                            (17)

in that same fixed physical chart. This source does not prove (17)
impossible and does not reflect it to (1). In (17) the actual C normal
may have a substantially larger West component, so the low-center
bound (10) is not asserted there.

The complete local tools in Section 2 apply independently of this
house: the narrow whole-square transverse cap and the exact normal/
support-point height estimates require no force, graph, degree or load
premise. The A-star feature and tilt reductions likewise retain the
whole actual three-force star and its real triangle contact.

All six component units, the three original completion squares, every
positive force, original application and normal, true degree, physical
mask and zero weight remain. No computational exclusion certificate,
numerical pose, angular sampling, scalar table, normal reselection,
mean replacement, Lean build, CI, workflow, remote operation or
original checklist mutation is used.

## 9. Direct mathematical dependencies

| Source | SHA256 | Exact scope used |
| --- | --- | --- |
| LOWER_HOUSE_TDC_D_FULL_MOMENT_AND_NONRADIAL_RETURN_REDUCTION.md | 51ecccadb6cebf8cfd0b2d6c6707c9b4387150d47b9be200def1df858e993edd | Actual A strip, strict opposed original A3 moments, nonzero AB/AD, all true forces and retained original domain |
| UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md | 008acc8485e591b34604bf3e0b0cdcb03b7220aa249fc8e49552a065770ca129 | Canonical shallow-top B chart, strict high radius, actual small BA support and normal cone |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete actual owned-axis dot-product and strict opposite-vertex support-span consequences |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Original D root/leaf geometry and unchanged radial leaf force |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Original house edge and load labels, true degrees and all nine physical units |

All new whole-interval geometric estimates and full-star identities are
proved above. The stated source hashes pin the versions read for this
proof; historical accepted sources are not rewritten.
