# Every physically enclosed unit has center radius strictly below three fifths

Date: October 31, 2026 UTC. Author: physical-two continuation.

**Status: complete new uniform hand theorem, frozen for separate clean
noncontributor review.** The proof strengthens the existing enclosed-center
bound from 5/8 to 3/5 for every finite physical contact ring in the original
disk. It keeps a whole actual outgoing-ray witness, every witness frame,
both owners of a square separating axis, all normal signs, and the entire
tangential clipping alternative. There is no stress or boundary-load
premise, no center-diameter hypothesis, and no restriction on ring size.

The proof does not assert the old whole-corner target on a silently
enlarged coordinate sector. Instead it proves a complete actual-witness
contradiction on the entire critical domain |c|>=3/5. A direct whole-sector
estimate handles the previously difficult S-owned vertical-to-diagonal
sector; the other sectors have complete corner or monotonicity proofs.

Put

    Q=1105/256,
    M=91/60,
    kappa=3721/7200,
    epsilon=kappa-1/2=121/7200.                      (1)

## 1. Full physical theorem and exact enclosure contract

Let S_0,...,S_(m-1) be any finite physical contact ring of distinct
actual closed unit squares with pairwise disjoint open interiors,
all contained in the same disk D_R about the unchanged origin O=0,
where R^2<=Q. Consecutive units have actual contact points, and the
closed center/contact walk is contained in the actual occupied ring.

Let E be a further actual unit square, contained in the same disk
and interior-disjoint from every ring square. Assume that the physical
contact walk has nonzero winding about every point of int(E).
Retain the original weak-junction convention: an arbitrarily small
physical Jordan routing may converge to the contact walk, provided
every compact subset of int(E) stays on its bounded side and a
positive distance from the closed occupied ring. Winding is then
stable there. No simple or convex limiting center polygon is assumed.

**Uniform enclosed-center theorem.** The actual center c_E satisfies

    |c_E|<3/5.                                      (2)

Its already accepted own-coordinate bounds also remain valid:

    |c_E.v_1|<kappa, |c_E.v_2|<kappa,                (3)

for that same actual E's own orthonormal side axes v_1,v_2.
No square is rotated independently or moved to obtain (2).

This theorem can be applied to any original completion unit whose
same physical enclosure has been proved. It does not assign enclosure
to an exterior occupant, transmitter or hub, and it does not replace
any original winding or allocation proof.

## 2. Actual ring-center entry and the real outgoing witness

For any actual contained unit of center c and own axes u,v, a
farthest physical corner has squared norm

    |c|^2+1/2+|c.u|+|c.v|
       >= |c|^2+|c|+1/2.

At rho=M,

    M^2+M+1/2-Q=31/57600>0.

The scalar expression rho^2+rho+1/2 is strictly increasing for
rho>=0. Therefore every actual ring center has norm strictly
below M, including at the original closed disk endpoint R^2=Q.
This conclusion needs neither positive circle load nor an actual
circle contact of that ring unit.

Apply the complete finite-ring own-coordinate theorem in Section 1
of C7_INNER_SIDE_CORNER_RESTRICTIONS.md, SHA256 b9329b7a, with this
strict same-ring center bound. Its complete shallow/steep radial-tail
proof, supplied by CENTER_COVER_PIERCING.md and sharpened there,
gives precisely (3). Its filename does not restrict that theorem
to seven bodies. The entire operative proof and the precise ring
entry have been read; their current complete audit is identified
in Section 10.

Suppose for contradiction that |c_E|>=3/5. In particular c_E!=0.
Use only an origin-fixing orthonormal coordinate description of
the entire actual configuration, with signs and exchange of E's
own axes chosen so

    T=E=(a,b)+[-1/2,1/2]^2,
    0<=b<=a<kappa,
    z=(a,b), L=a^2+b^2>=9/25.                     (4)

Follow the actual ray {tau*z:tau>=1} from the center of E.
It must encounter an actual ring square after leaving E. Otherwise
the physical contact walk would be avoided on a path from a point
where its winding is nonzero to infinity where it is zero. Every
point of int(E) avoids every closed ring unit: an open neighborhood
of a point in a closed square meets that square's open interior.
Thus the ray's ring encounter is beyond E's open interior and
belongs to a whole original ring unit S.

This S is contained in the same D_R, interior-disjoint from T,
and meets the actual outgoing radial line y=(b/a)x. It is not an
independently placed point, an auxiliary hull edge, or a unit chosen
to have a convenient frame, degree, load or contact mean. At a weak
junction the same argument applies to compact interior portions;
the stated stable-winding hypothesis is exactly what is needed.
No center-diameter-below-three assertion is used from the ring
convention source.

## 3. The complete critical coordinate domain and the horizontal target

The whole domain (4) supplies the quantitative bounds needed below.
First, b<=a gives

    a>=3/(5*sqrt(2))>3/8,
    a<kappa<13/25<21/40.                            (5)

If b<=a/2, then L<=5a^2/4<=5kappa^2/4, whereas

    9/25-5*kappa^2/4=1084079/41472000>0.

Therefore the full critical domain necessarily has

    a/2<b<=a.                                      (6)

There is no remaining unbalanced critical sector. Also

    b^2=L-a^2>=9/25-kappa^2,
    9/25-kappa^2-(38/125)^2
       =642839/1296000000>0,

so

    b>38/125>1/4.                                  (7)

For these same actual a,b define the scalar corner targets

    F_R=(a+3/2)^2+[b*(1+1/(2a))]^2,
    F_U=(b+3/2)^2+[a*(1+1/(2b))]^2.                (8)

All denominators are strictly positive. Expanding with L=a^2+b^2,

    F_R=L+2a+L/a+L/(4a^2)+2.                       (9)

For fixed L>=9/25 the right side decreases strictly in a throughout
0<a<=13/25, because its derivative is

    2-L/a^2-L/(2a^3)
       <=-2687/4394<0.                             (10)

It also increases with L. Consequently throughout (4)--(7),

    F_R >= [9/25+2*(13/25)+(9/25)/(13/25)
                       +(9/25)/(4*(13/25)^2)+2]
         =Q+23523/216320>Q.                        (11)

Weakening a<13/25 to a<=13/25 in this scalar comparison only
enlarges the domain; it is not a movement of T or S.

The upward target is never smaller. Put rho=a/b>=1. Direct
expansion, with no upper restriction on rho, gives

    F_U-F_R
      =b*(rho-1)^3/rho
       +(rho-1)*(rho+1)*(rho^2+1)/(4*rho^2)>=0.     (12)

We will contradict actual S containment for every possible owner,
normal and frame of a separating axis between T and S.

## 4. Every T-owned rightward separator, with both actual witness frames

The separating-axis theorem for two actual squares supplies a
separating normal perpendicular to a side of one of them, including
support ties. Direct it from T toward S. Ray membership forces its
scalar product with z to be positive: otherwise the ray cannot
cross T's strictly positive support halfwidth in that direction.
For a T-owned normal, only the positive horizontal or positive
vertical direction is therefore possible. Separation need not be
contact; a positive separating gap only strengthens the inequalities.

First let the normal be rightward and put

    X=a+1/2, q=b/a, g=q*X=b*(1+1/(2a)).

The entire original scalar domain gives

    7/8<=X<21/20,
    1/2<=q<=1,
    g>0.                                           (13)

Here q=1/2 is a harmless closed enlargement of the strict (6).
The actual S lies in x>=X and meets y=q*x. Write its actual
center (C_x,C_y). Choose signs and interchange its own axes
only as a frame description, so its frame angle has

    u=cos(phi), v=sin(phi), 0<=phi<=pi/4,
    h=(u+v)/2, j=(u-v)/2.

Both reflected actual orientations are treated below; no common
frame with T or motion of S is assumed. In either orientation,

    C_x>=X+h.                                      (14)

### 4.1. First actual orientation

Its leftmost and topmost vertices relative to its center are
(-h,j) and (j,h). If v/u<=q, the maximum of y-qx on S is at
the leftmost vertex, with the full connecting side retained at
equality. Ray membership gives

    C_y-q*C_x+j+q*h>=0,
    C_y>=g-j.

The actual topmost vertex therefore has coordinates at least
(X+u,g+v), both positive. Its squared norm is at least F_R,
because

    (X+u)^2+(g+v)^2-[(X+1)^2+g^2]
       =2*X*v*[q-v/(1+u)]>=0.                     (15)

Indeed v/(1+u)<=sqrt(2)-1<1/2<=q. The aligned v=0
endpoint is included, with equality in this corner comparison.

If v/u>q, then v/u>1/2 and phi>atan(1/2). Since u+v
increases on [0,pi/4],

    u+v>3/sqrt(5)>4/3,
    9/5-16/9=1/45>0.

The actual rightmost vertex has first coordinate greater than
X+4/3. Its squared norm is greater than F_R even without using
its second coordinate, because g<=X and

    (X+4/3)^2-[(X+1)^2+X^2]
       =-X^2+(2/3)*X+7/9>0.                       (16)

The last quadratic is concave on the entire interval in (13).
Its values at 7/8 and 21/20 are respectively 343/576 and
1351/3600, both positive. This is one whole interval argument,
not a sampled witness orientation.

### 4.2. Reflected actual orientation

Here the topmost and rightmost vertices relative to the center
are (-j,h) and (h,j). Since q*v<=v<=u, the maximum of y-qx
is attained at the topmost vertex, with every equality tie allowed.
Consequently

    C_y-q*C_x+h+q*j>=0,
    C_y>=g-h+q*v.

The actual rightmost vertex has coordinate lower bounds

    (X+u+v, g-(1-q)*v).                             (17)

Both are positive: g>=7/16, while (1-q)*v<=1/(2*sqrt(2))<3/8,
so the second exceeds 1/16. Its squared lower bound minus F_R
is exactly

    v*[2*u+2*X*(1-q+q^2-v/(1+u))+(1-q)^2*v]>=0.    (18)

Use 1-q+q^2>=3/4 and v/(1+u)<1/2 to see the bracket is
nonnegative throughout the entire actual frame interval. The
aligned endpoint is retained. Equations (15)--(18) prove
R^2>=F_R>Q for every rightward T-owned separator, impossible.

## 5. Every T-owned upward separator, including the full support transition

For an upward separator exchange the two displayed coordinates
only in this proof calculation. The actual scalar data become

    X=b+1/2>0,
    q=a/b>=1,
    g=q*X,
    F_U=(X+1)^2+g^2.                                (19)

Both arbitrary actual witness orientations are again retained.
In the first orientation, v/u<=1<=q, so the leftmost-vertex
case of Section 4.1 always applies. Its actual corner lower
bound gives R^2>=F_U by (15).

In the reflected orientation, if v/u<=1/q, the maximum of
y-qx is at the topmost vertex. Exactly as in Section 4.2,
the actual rightmost vertex has coordinates at least

    (X+u+v, g+(q-1)*v).

These dominate (X+1,g), because u+v>=1 and q>=1. Hence its
squared norm is at least F_U.

If instead v/u>1/q, the maximum of y-qx is at the actual
leftmost vertex (-h,-j). Its ray inequality is

    C_y-q*C_x-j+q*h>=0,
    C_y>=g+j.

The actual topmost vertex (-j,h) therefore has coordinates
at least (X+v,g+u), both positive. Its squared lower bound
satisfies

    (X+v)^2+(g+u)^2-[(X+1)^2+g^2]
       =2*X*(v+q*u-1)>=0,                         (20)

because q>=1 and u+v>=1. The support-transition equality
belongs to the preceding weak case; either formula is valid
there. Thus this whole remaining orientation is covered by
an actual corner, without imposing a sampled tilt or dropping
the transition.

Every upward T-owned separator gives R^2>=F_U>=F_R>Q by
(11),(12). This completes the full T-owned part, retaining
both owned axes, both reflected frames, all ties and endpoints.

## 6. S-owned separators retain the whole farthest corner and clipping

Suppose the chosen separating unit normal n is owned by S,
directed from T toward S. Let m be its perpendicular actual own
axis. Put

    z_n=n.z, z_m=m.z,
    H=z_n+(|n_x|+|n_y|)/2.

The actual ray witness tau*z in S has tau>1. If z_n<=0,
then tau*z_n<=z_n<H, contradicting its separation from T.
Thus

    z_n>0, H>0, lambda=H/z_n>1.                   (21)

The actual S own-side strips and separating halfplane give

    n.C_S>=H+1/2,
    tau>=lambda,
    |m.C_S|>=max(tau*|z_m|-1/2,0).

Its actual farthest corner has squared norm

    (|n.C_S|+1/2)^2+(|m.C_S|+1/2)^2.

Consequently, with L=a^2+b^2 from (4),

    R^2 >= (H+1)^2+max(lambda*|z_m|,1/2)^2
         >= L*lambda^2+2*H+1 =: F(n).             (22)

The max expression retains the entire tangential clipping branch,
including z_m=0 and its strict 1/2 corner term. The final weak
inequality only drops a nonnegative part of that actual corner
bound; it does not replace S by a point or by a center-only
witness. No contact owner of the ray encounter is required.

We now prove F(n)>Q on every original allowed normal sector.

## 7. Whole positive quadrant: one concave sector and one direct strict bound

Set

    A=a+1/2, B=b+1/2, delta=a-b>=0.

These are scalar abbreviations, unrelated to any named packing
unit. The full critical domain gives b>=a/2 and a<1, so

    B-(2/3)*A>= (1-a)/6>0.                        (23)

### 7.1. Horizontal axis to the diagonal

Write the actual n=(1,t)/sqrt(1+t^2), with 0<=t<=1, and
D=a+b*t>0. Then

    lambda=1+(1+t)/(2*D),
    H=(A+B*t)/sqrt(1+t^2),
    lambda'=delta/(2*D^2),
    lambda''=-b*delta/D^3,
    (lambda^2)''
       =delta*[delta-4*b*lambda*D]/(2*D^4).       (24)

If delta=0, the last derivative is zero. Otherwise delta<=a/2,
b>=a/2 and lambda*D=D+(1+t)/2>=a+1/2 give

    4*b*lambda*D>=2*a*(a+1/2)>a/2>=delta.

Thus lambda^2 is concave throughout this entire sector. The
numerator of H'' is

    -A+2*A*t^2-3*B*t
       <= A*(-1+2*t^2-2*t)<=-A<0,                (25)

where (23) and 0<=t<=1 are used. Hence F=L*lambda^2+2H+1
is concave on the whole closed interval. Its minimum is at
one of the two actual intrinsic endpoints.

At the horizontal endpoint n=e_x, the expression in (22) is
exactly F_R, which exceeds Q by (11). At the diagonal endpoint,
the following whole-sector estimate applies and also exceeds Q.
Therefore F(n)>Q throughout this first sector, including both
endpoints and a=b.

### 7.2. Vertical axis to the diagonal: direct whole-sector estimate

Write n=(t,1)/sqrt(1+t^2), 0<=t<=1. Then

    D=b+a*t>0,
    lambda=1+(1+t)/(2*D),
    H=(B+A*t)/sqrt(1+t^2).

Because a>=b, lambda is nonincreasing and

    lambda>=lambda(1)=1+1/(a+b).                  (26)

Also A>=B>0 gives H>=B on the entire interval. This follows
directly by positive squaring:

    (B+A*t)^2-B^2*(1+t^2)
       =2*A*B*t+(A^2-B^2)*t^2>=0.                (27)

Since a+b<=sqrt(2*L), equations (22),(26),(27) yield the
uniform entire-sector lower bound

    F(n)>=L*(1+1/(a+b))^2+2*B+1
         >=(sqrt(L)+1/sqrt(2))^2+2*B+1
          =L+sqrt(2*L)+2*b+5/2.                   (28)

The critical radius and complete own-coordinate cap supplied
L>=9/25 and b>38/125 in (7). Moreover

    sqrt(2)>140/99,
    2-(140/99)^2=2/9801>0,
    sqrt(2*L)>=3*sqrt(2)/5>28/33.

Thus the full sector, with no derivative sign subdivision, has

    F(n)>9/25+28/33+76/125+5/2
         =Q+83/1056000>Q.                         (29)

This includes the vertical axis, the diagonal, every intermediate
normal, all witness strip endpoints and all clipping values from
(22). It resolves the whole sector in which the old balanced
one-turn derivative argument did not extend to b>=a/2.

Sections 7.1--7.2 exhaust the full positive normal quadrant.

## 8. Both complete mixed-sign normal sectors

For n=(1,-t)/sqrt(1+t^2), (21) requires 0<=t<a/b. Put
D=a-b*t>0. All original allowed t, including values above one,
remain. The scalar formulas are

    lambda=1+(1+t)/(2*D),
    lambda'=(a+b)/(2*D^2),
    H=[a+1/2+(1/2-b)*t]/sqrt(1+t^2).

Since D<=a, L>=a^2, lambda>=1+1/(2a), and b>=a/2,

    2*L*lambda*lambda'
       >=(a+b)*(1+1/(2a))
       >=(3/2)*(a+1/2).                            (30)

The complete derivative of H and b<=kappa=1/2+epsilon give

    2*H'>=-2*epsilon-(4/5)*(a+1/2),                (31)

because t/(1+t^2)^(3/2)<=2/(3*sqrt(3))<2/5 for every
t>=0. This last maximum follows by differentiating: its
derivative has the sign of 1-2t^2. The strict comparison
2/(3*sqrt(3))<2/5 is equivalent to 25<27.

Consequently

    F'>=(7/10)*(a+1/2)-2*epsilon>0.                (32)

For example, a>=3/8 and 2*epsilon<1/25 give the uniform
positive lower bound 229/400. Thus F is increasing on its
entire original positive-projection interval, from F(e_x)=F_R>Q.

For n=(-t,1)/sqrt(1+t^2), (21) requires 0<=t<b/a. Interchange
a,b in the same formulas. Now a+b>=2b, while the parameter
entering the negative derivative error is a<=kappa. Therefore

    F'>=(6/5)*(b+1/2)-2*epsilon>0.                 (33)

The full bound b>1/4 from (7) gives, for example, a positive
reserve greater than 43/50. Its initial value is F(e_y)=F_U,
and F_U>=F_R>Q by (11),(12). Both entire mixed-sign sectors
are therefore impossible under (22).

Normals with both components nonpositive have z_n<=0 and were
already excluded by (21). Positive axes are included in the
closed endpoints above. This is the exhaustive original S-owned
normal cover; there is no omitted sign, tilt, tie or clipping case.

## 9. Whole-ring conclusion and literal original use

An actual separating axis of the real interior-disjoint T and S
must be owned by T or S. Sections 4--5 contradict R^2<=Q for
every T-owned possibility. Sections 6--8 contradict the same
whole-square containment for every S-owned possibility. Thus
the actual outgoing witness supplied in Section 2 cannot exist
if L>=9/25 and both original own-coordinate caps hold.

Physical enclosure supplies that witness for every nonzero
actual center. The contradiction therefore excludes the whole
closed range |c_E|>=3/5, including its equality endpoint, and
proves (2). The zero center satisfies (2) immediately. The
proof has kept the closed disk endpoint R^2=Q throughout.

This is a force-free theorem for any finite physical contact
ring. It permits arbitrary independently oriented ring units,
arbitrary ring size, nonconvex contact walks, genuine shared
segments, side endpoints, weak junctions and the stated stable
winding convention. No positive-stress or circle-load condition
is added. The own-coordinate estimate (3) remains the same
accepted strict estimate in the actual enclosed unit's own frame.

For any original nine-square caller, the same actual central
completion unit now satisfies |c_E|<3/5 after its original ring
enclosure has been established. All nine squares, original
positive forces, full stars, actual normals, applications, full
shared means, physical circle masks and individual zero circle
coefficients remain. An unloaded or loaded N keeps its original
equation; this proof uses neither a substituted transmitter nor
a deleted circle resultant.

The conclusion does not itself supply a missing central/exterior
allocation, a pocket-occupancy fact or a simultaneous completion
capacity. It must be joined only to the actual unit whose original
winding premise holds. No whole D02 family, global sharp theorem,
equality case or original fine/coarse count is closed by this
reusable geometric improvement alone.

## 10. Complete inputs, provenance and exact review requirement

All complete operative geometric sources below were read, together
with the entire current center-entry audit. Their current bytes
and complete physical scopes are retained.

| Complete source | SHA256 | Exact operative use |
| --- | --- | --- |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Only its complete finite-ring Section 1 strict own-coordinate theorem, with the actual strict ring-center bound derived in Section 2 above |
| CENTER_COVER_PIERCING.md | 029d7142b140e8ffe10e5beebf54223b04f7e0722605b9a6b9098a914ce41a29 | Complete original shallow/steep actual radial-tail and witness support proof supporting that own-coordinate theorem; no false unconditional center-cover claim is imported |
| SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md | 10d0ed2343f23c51e7ab165542aad6fd3ce72405c78a002511633c2a958b6a03 | Only its complete actual winding/weak-junction convention and outgoing physical ray consequence; no center-diameter or capacity-one premise is assumed here |

The full accepted balanced source
ENCLOSED_UNIT_BALANCED_WHOLE_CORNER_RADIAL_TAIL.md,
SHA256 7ff506e4b3562e106ffbc0dc22400f961dbf84e4e552630d3b278b19aedfbbc2,
was also read. Its mathematical body is identical to the reviewed
original at SHA256
05d0c4c68603ef90dbfec3b7a00cd2ea17a83fa9abe53d2632cc6f40256b002f.
That exact acceptance-header reconciliation is established by
REVIEW_ENCLOSED_CENTER_OWN_COORDINATE_ENTRY_AND_EXACT_ACCEPTANCE_HEADER_RECONCILIATION_2026_10_31.md,
SHA256 29a02ccbac5c36176119a6dbbecb6490c4f0065985d285dd5eae960007afbb80,
whose complete source entry, physical ray contract and literal
central-ring join were read.

The former balanced theorem claimed its full target only for
b>=2a/3. It is not cited as if that conclusion had been proved
for b>=a/2. The present source prints the complete new critical-
domain proof: the extended T-owned cases including (20), the
horizontal-sector concavity (24)--(25), the direct entire vertical
sector estimate (26)--(29), and both original mixed-sign intervals
with their new complete constants (30)--(33). The full whole-
witness inequality (22) retains every actual clipping branch.

The new exact frozen source requires a clean noncontributor
full-source review of all these arguments and of every literal
caller join. Existing acceptance of 5/8 or of the smaller balanced
sector does not automatically review the new 3/5 theorem.

All new computations are exact norm/strip identities, continuous
whole-interval concavity or monotonicity, positive-square comparisons
and printed rational reserves. There was no pose or numerical
parameter search, angle grid, numerical packing certificate,
coefficient packet, invented witness, changed normal or mean,
deleted unit or force, Lean/Lake invocation, CI/workflow,
GitHub write, metadata mutation, remote adoption, merge or
original inventory/count change.
