# No unit in a nine-square packing has seven physical boundary neighbors

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem, pending full root
and separate independent review.** No original gate or ledger is changed.

Let nine actual unit squares have pairwise disjoint open interiors and
lie in a common disk centered at O of radius

    R<=sqrt(1105)/16.

A boundary unit means a square physically touching that containing
circle; no positive multiplier or stress is required.

**Theorem.** No actual unit H can physically touch seven distinct
boundary units of this packing.

The proof uses only actual centers, physical contact, containment and
the previously proved same-nine geometric obstructions. It does not
assume an order of positive edges, a connected boundary path, a force
equation, or a common square frame.

## 1. Uniform center bounds and the central quarter-disk obstruction

NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md gives R>2 for the same nine
actual squares. Every boundary unit has center z satisfying

    |z|>=R-1/sqrt(2)>2-17/24=31/24=:r_0.              (1)

Every contained unit center has norm strictly less than

    M=91/60.                                          (2)

Indeed its farthest-corner squared radius is at least
|z|^2+|z|+1/2, whereas

    M^2+M+1/2-1105/256=31/57600>0.

The exact central-disk theorem
CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md says that
no actual unit can contain the closed disk D_(1/4). In H's actual
own axes, a center with both absolute coordinates at most 1/4
would give precisely that containment. Therefore H's actual center c
satisfies

    q:=|c|>1/4.                                       (3)

In particular c is nonzero. All nine units, including H and every
possible zero-stress boundary unit, remain in these premises.

## 2. Every boundary neighbor lies in one fixed angular interval

If H touches a boundary unit of center z, choose any actual common
point p. Both center-to-point distances are at most 1/sqrt(2), so

    |z-c|<=sqrt(2).

Write r=|z| and let theta be the minor angle between z and c.
The cosine law gives

    cos(theta)>=(q^2+r^2-2)/(2qr).                     (4)

We claim the right side is strictly greater than -5/12 throughout
the actual domain q>1/4, r>r_0.

If q>=sqrt(2), its numerator is positive, so the claim is immediate.
If q<sqrt(2), the function

    f(q,r)=(q^2+r^2-2)/(2qr)

is strictly increasing in r>0, since

    partial_r f=(r^2+2-q^2)/(2q r^2)>0.

At r=r_0 it is strictly increasing in q>0, because r_0^2<2 and

    partial_q f(q,r_0)=(q^2+2-r_0^2)/(2r_0 q^2)>0.

Hence in the latter case

    f(q,r)>f(1/4,r_0)
          =[(1/4)^2+(31/24)^2-2]/[2(1/4)(31/24)]
          =-5/12.                                    (5)

Put alpha=acos(-5/12), with pi/2<alpha<pi. Equations (4)--(5)
show that every physical boundary neighbor center has a unique
angular lift relative to c in the single open interval

    -alpha<arg(z)-arg(c)<alpha.                       (6)

Thus all such directions lie in an arc of width 2alpha<2pi.

## 3. Exact separation of every pair of boundary center directions

Set

    C_0=6481/8281=1-1/(2M^2),
    theta_0=acos(C_0),              0<theta_0<pi/3.     (7)

We prove that the minor angular separation of two distinct actual
boundary centers is strictly greater than theta_0.

The centers of any two interior-disjoint unit squares are at distance
at least one, because their open radius-1/2 incircles are disjoint.
Suppose two boundary-center radii r,s and minor separation theta
instead satisfy theta<=theta_0. Then

    |z_1-z_2|^2
       =r^2+s^2-2rs cos(theta)
       <=r^2+s^2-2rs C_0.                            (8)

The last expression is separately convex in r and s. On the closed
rectangle [r_0,M]^2 its maximum is attained at a corner. The complete
corner values obey

    2M^2(1-C_0)=1,
    1-[M^2+r_0^2-2M r_0 C_0]=14229/145600>0,
    1-2r_0^2(1-C_0)=9099/33124>0.                    (9)

Both actual radii lie strictly between r_0 and M by (1)--(2).
Separate convex interpolation between the four corner values therefore
makes the right side of (8) strictly less than one. This contradicts
the actual center separation. Consequently

    theta>theta_0                                    (10)

for every pair of distinct physical boundary units.

## 4. Seven centers cannot fit in the permitted interval

The triple-angle formula at the exact rational C_0 gives

    cos(3theta_0)=4C_0^3-3C_0
                 =-244407836159/567869252041,

and the comparison with (5) has the exact positive reserve

    -5/12-cos(3theta_0)
        =93547773703/6814431024492>0.                 (11)

Since 0<3theta_0<pi and cos(alpha)=-5/12, strict monotonicity
of cosine on (0,pi) yields

    3theta_0>alpha,          6theta_0>2alpha.         (12)

Suppose H had seven distinct boundary neighbors. Order their unique
lifts from (6) as

    t_1<t_2<...<t_7.

Each consecutive difference exceeds theta_0. If it is at most pi,
this is (10) directly; if it exceeds pi, it automatically exceeds
theta_0<pi/3. Thus

    t_7-t_1=sum_(i=1)^6 (t_(i+1)-t_i)
              >6theta_0>2alpha.

But all seven lifts lie in the interval of width 2alpha in (6),
so t_7-t_1<2alpha. This is a contradiction, proving the theorem.

Every comparison is a whole-domain center or angular inequality.
There is no discretization of orientations or contact locations.

## 5. Exact whole-graph consequence for the prospective C3.335 bouquet

Consider a positive component made of two intact triangles at the
same actual root H and a five-body fan whose hub is also H.
The fan is H joined to the four-vertex path 1-2-3-4. The two
intact petals give four distinct actual circle-loaded neighbors of H.

In this terminal fan the path endpoints have their true degree two
and touching neighbors, so they are loaded. Each interior path vertex
has its true degree three and two positive edges among its neighbors;
NO_UNLOADED_DIAMOND_HUB.md therefore makes it loaded as well. Extra
forces attach only at H and do not change any of these degrees.
Thus H has eight distinct actual boundary neighbors: four petal
tips and four fan vertices.

The theorem excludes this entire bouquet, with the full H force
system and all nine original bodies retained. It uses neither an
isolated-fan equation nor a pressure-only replacement of either petal.
The other rooted five-body graph types and the remaining block-cut
layouts of C3.335.b0 are separate obligations; this source does not
declare that whole coarse cell closed.

No force selection, physical motion, numerical pose, Lean compilation,
CI, remote mutation or shared-ledger edit is used.
