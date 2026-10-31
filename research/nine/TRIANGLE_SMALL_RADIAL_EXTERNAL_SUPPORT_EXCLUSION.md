# A triangle root cannot have a small outward radial external support

Date: October 27, 2026.

**Status: accepted complete hand proof at its full stated original scope; root and separate independent full-source/scope reviews passed.**

Accepted reviews: REVIEW_TRIANGLE_SMALL_RADIAL_EXTERNAL_SUPPORT_LEAF_PAIR_2026_10_27.md and
REVIEW_TWO_TRIANGLE_FOUR_BRIDGES_AND_OPPOSITE_D_ROOT_ROOT_2026_10_27.md.
Source pins in those reviews precede this acceptance-only header update. No original gate or central ledger is changed.

Retain the original physical units and common compatible certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    M=91/60.

Let A,B,C be an actual positive unit-square triangle. At every body keep
its complete external force system and assume its origin moment is zero.
There is no degree or circle-load assumption at B or C. Suppose A's
complete external resultant is alpha e with alpha>0 and |e|=1, and
the actual A has the physical radial support

    p=x e in A,       A subset {z:e.z<=x},
    0<=x<=1/60.                                        (1)

The point p may be an original bridge application, but the theorem
only needs its stated actual geometric support property. All original
forces, common means, physical masks, zero weights and remaining units
are retained.

**Theorem.** This entire local configuration is impossible.

The proof uses only A's full triangle-pair equation, the actual triangle
proper-port facts and physical containment of its two distinct neighbors.
It does not require either neighbor to be a degree-two or loaded tip.

## 1. Complete original concurrence and center bounds

Direct the two actual A-to-neighbor triangle normals n_1,n_2, with
positive magnitudes mu_1,mu_2. The complete original A equation is

    mu_1 n_1+mu_2 n_2=-alpha e.                         (2)

If the pair is nonparallel, its genuine intersection has the form

    q_A=q e, q>=0,
    P_i=q_A+ell_i n_i, ell_i>=0.                       (3)

For a nonzero common cycle moment, this is the full positive-concurrence
statement recalled in `TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md`,
Section 2, applied to A's complete external alpha e. For zero common
cycle moment both actual nonparallel lines pass through O, so q=0;
the proper-port assertion is the purely physical triangle fact and
still applies. Thus (3) includes both moment alternatives and all
zero proper-length and actual mean endpoints.

Every actual unit center c satisfies |c|<M. This follows from its
farthest-corner inequality |c|^2+|c|+1/2<=R^2 and the exact positive
reserve 31/57600 at M and R^2=1105/256. Also every actual outward
support height h of A at a contained neighbor satisfies

    h<=d.                                               (4)

Indeed the neighbor center has normal projection at least h+1/2,
and its norm is at most d+1/2. Any two distinct unit centers must
be at distance at least one, because their open radius-1/2 incircles
are disjoint.

We use the two complete degree-free physical-triangle facts throughout:
an A-owned side normal has nonnegative scalar product with the other
A triangle normal; two strict opposite A vertices cannot be the two
contacts of neighbors that physically touch. These are the original
owned-normal and opposite-vertex support-span implications, without
additional force assumptions at the neighbors.

## 2. The complete parallel pair is already impossible

Parallel outward normals at a physical unit triangle have the same
sign. Equation (2) makes that sign -e. A's actual width in direction
e is at least one, so both neighbors lie in

    e.z<=min_A e.z<=x-1<=-59/60.

Their centers consequently have e projection at most -89/60 and
norm less than 91/60. In the (e,Je) frame they lie in a rectangle
of longitudinal width less than 1/30 and transverse width less than
2sqrt(10)/10. Its squared diameter is less than

    (1/30)^2+4(1/10)=361/900<1.

This contradicts the two disjoint open incircles. No concurrence,
side ownership, distinct application assumption or root frame was
needed for this complete parallel exit.

## 3. Every aligned nonparallel root puts its neighbors in one small cap

Suppose e is an A side axis. Rotate e east and use the original p:

    A=[x-1,x] times [h-1,h],     0<=h<=1,
    a=1-x>=59/60.

A vertical owned triangle normal would make the other normal's
vertical component have the same weak sign, by the owned-normal fact,
contradicting the zero vertical component in (2). A horizontal normal
would make the other horizontal by (2), contrary to the present
nonparallel alternative. Thus both normals strictly expose vertices.
Their vertical components have opposite signs. If either contact were
a right vertex, (2) would put the other at the strict opposite left
vertex, forbidden by the physical triangle. Therefore the two actual
ports are the two left vertices.

Using (3) and reversing the neighbor names if necessary gives

    0<h<1,
    P_1=(-a,h),       P_2=(-a,h-1),
    t=a+q>=a,
    n_1=(-t,h)/sqrt(t^2+h^2),
    n_2=(-t,h-1)/sqrt(t^2+(h-1)^2).                     (5)

For either y=h or h-1, its actual support is

    H(y)=(at+y^2)/sqrt(t^2+y^2)>=a.                    (6)

Squaring the positive quantities proves the last inequality: the
surplus is y^2(a(2t-a)+y^2)>=0. Every original coefficient in (5)
is proper and nonzero because the left port's first coordinate is
negative while q>=0.

### 3.1. The genuine intersection has t>5

At least one of |h|,|h-1| is at least 1/2. For fixed a>0 and t>=a,
H(y) increases with |y|, and for fixed |y| it decreases with t>=a.
It also increases with a when t,|y| are fixed. If t<=5, the port
with |y|>=1/2 would therefore satisfy

    H(y)>=(5*(59/60)+1/4)/sqrt(25+1/4)
         =31/(3sqrt(101))>61/60>d.                    (7)

The strict rational squared comparison in (7) has numerator
961*3600-3721*909=77211>0. This contradicts (4). Hence t>5.

### 3.2. The two actual centers have distance less than one

The angle between the two normals in (5) is

    arctan(h/t)+arctan((1-h)/t)<1/t<1/5.              (8)

Let c_i be the genuine neighbor center. By (6),

    c_i.n_i>=H(y_i)+1/2>=89/60,
    89/60<=|c_i|<91/60.

Its direction is therefore within angle beta=arccos(89/91) of n_i.
We have the exact convenient bound beta<3/14. Indeed, for 0<=z<=1,
cos(z)<=1-z^2/2+z^4/24, and at z=3/14

    89/91-[1-(3/14)^2/2+(3/14)^4/24]
       =3569/3995264>0.

Since cosine is decreasing there, this proves the angle bound.
Together with (8), the two actual center directions differ by less
than 2*(3/14)+1/5=22/35. Their radii differ by less than 1/30.
Separating the radial difference and the chord at the smaller radius
and using 2sin(theta/2)<=theta gives

    |c_1-c_2|
      <1/30+(91/60)*(22/35)=74/75<1.                  (9)

This contradicts their open unit incircles. The whole aligned
nonparallel alternative is excluded.

## 4. Every tilted root reduces to two perpendicular far-side contacts

Now e is not an A side axis. Its unique maximum-e point is p=x e.
Write the unchanged square with inward orthonormal axes u,v as

    A=p+[0,1]u+[0,1]v,
    u.e=-a, v.e=-b,
    a,b>0, a^2+b^2=1.                                 (10)

If q>x, both own coordinates of q_A relative to p are strictly
negative. Every proper vector P_i-q_A would have both own components
strictly positive, so both normals would strictly expose the same
far vertex. Two nonparallel lines through that same port could only
intersect there, contrary to q_A outside A. Thus

    0<=q<=x<=1/60.

Put delta=x-q. The actual q_A has relative own coordinates
(delta a,delta b), each between zero and 1/60. The right side of
(2), in these own axes, has strictly positive components alpha a,
alpha b.

An owned near-face normal -u or -v is impossible: its physical
nonobtuse companion would have the same nonpositive component,
contrary to (2). A strict near-vertex normal has both components
negative; its companion would then have both components positive,
so their ports would be strictly opposite vertices, also impossible.

At the far vertex W=p+u+v, a proper actual port would have support

    W.n=|W-q_A|+q_A.n
        >=sqrt(2)*(1-1/60)-1/60
        >34/25>d,                                     (11)

contrary to (4). Hence no far-vertex normal occurs.

The only remaining strict vertices are P=p+u and Q=p+v. They are
opposite and cannot both occur. A P normal has positive u and
negative v component; pairing it with an owned +u normal cannot
give the positive v component in (2), and pairing it with owned
+v violates their nonnegative scalar product. The Q cases are the
exchanged statements. A repeated remaining P or Q vertex also cannot
give the present nonparallel pair: q_A has both relative own coordinates
at most 1/60, whereas that vertex has one coordinate equal to one.
Thus q_A differs from the vertex, and properness forces both normals
to be the same ray from q_A to it, with coincident lines. These
alternatives also include the
axis endpoints, which are in the owned-face cases.

Thus the complete surviving pair is precisely the two actual owned
normals u and v. Its genuine ports, in own coordinates about O, are

    P_u=(1-xa,-qb),       P_v=(-qa,1-xb).              (12)

The two neighbors lie beyond the actual perpendicular supports
u.z>=1-xa and v.z>=1-xb. Because they physically touch, they share
an actual point Z with both those inequalities. In particular the
neighbor T across the u face contains both its unchanged P_u and
a point Z satisfying

    Z_v>=1-xb>=59/60.                                  (13)

## 5. The actual neighbor at the first far side cannot span to the other one

Write H_u=1-xa>=59/60. The center c_T of the actual unit T has

    (c_T)_u>=H_u+1/2>=89/60,
    |c_T|<91/60,
    |(c_T)_v|<sqrt(10)/10<1/3.                         (14)

If u is a side axis of T, its v interval has length one. Equation
(13) gives (c_T)_v>=59/60-1/2=29/60, contradicting (14). This
includes a genuine side-interior mean and either endpoint of it.

Otherwise P_u is T's actual unique minimum-u vertex. Its inward
orthonormal axes have nonnegative u components. After naming the
upward one first, its full unchanged chart is

    T=P_u+[0,1](s,t)+[0,1](t,-s),
    s,t>=0, s^2+t^2=1.

The maximum v increment from P_u is t. Equations (12)--(13) force

    t>=1-xb+qb=1-delta b>=59/60,
    s<=sqrt(119)/60<11/60.

Since (P_u)_v=-qb>=-1/60, its actual center satisfies

    (c_T)_v=-qb+(t-s)/2
             >-1/60+(59/60-11/60)/2=23/60,

again contradicting (14). Every actual minimum-support feature
of T has been covered. Thus the two far-side neighbors cannot
physically touch, excluding the last tilted alternative.

Sections 2--5 exhaust parallel/nonparallel and aligned/tilted A,
including zero common cycle moment and zero proper-length endpoints.
They prove the theorem using the unchanged original triangle.

## 6. Whole original pendant-two-edge-arm consequence

Suppose A belongs to an actual triangle and its only outside positive
pair edge is the genuine pendant arm A--U--L, with U true unloaded
degree two and L a genuine S/D leaf. A's other two triangle vertices
keep arbitrary complete zero-origin-moment external systems. The
actual arm application is

    p=(r_L-w)e,
    r_L in {r,d}, w in {1,sqrt(2)},
    A subset {z:e.z<=r_L-w}.

The D/diagonal combination is forbidden by the original off-origin
strict nonradial point-only vertex/vertex selection. In the other
three complete arm alternatives, the existing exact estimate in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Section 1, gives
|r_L-w|<31/60<r. Thus the actual point proves A physically clear,
with every original circle mask retained until this conclusion.
Its full external resultant is now exactly the actual arm alpha e.

The closed triangle external-ray theorem forces r_L-w>=0. The only
possible original arm type is therefore S/side and

    r_L-w=d-1 in [0,1/60).

All hypotheses of the theorem hold, giving the contradiction.
This excludes the entire sole-two-edge-arm triangle interface at
arbitrary true degrees of its other vertices. It includes a root
joined to any other cyclic block or bridge system through those
vertices, with all original external moments justified by its real
private branch sums.

No leaf is deleted, no boundary tip is invented, and no neighboring
equation is lowered to degree two. All remaining physical squares
stay present. No physical motion, normal reselection, changed mean,
numerical pose, Lean compilation, CI or remote action is used.
