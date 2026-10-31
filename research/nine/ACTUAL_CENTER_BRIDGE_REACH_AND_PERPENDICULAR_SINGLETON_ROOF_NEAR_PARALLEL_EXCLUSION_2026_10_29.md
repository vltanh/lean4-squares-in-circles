# A complete center-reach obstruction removes the near-parallel singleton roof

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed uniform hand theorem, submitted for full
independent review.** A single actual-center reach inequality excludes every
return owner and every original exterior mean in the physical-two
West/strict perpendicular-singleton roof whenever the actual nonowning
hub side has vertical component at most 1/8. It uses the original
one-unit B--N--C path and applies to both the unloaded-N and loaded-N
rows. No two-force transmitter equation is assigned to a loaded N.

The result closes a whole continuous end of both previously retained
opposite-vertex and side-return rows. It does not close either whole
original D02 load row.

## 1. A force-free reach inequality for actual units

Let B,C,N be three distinct actual unit squares. Suppose N physically
touches both B and C. The degrees, loads, circle masks, orientations and
other contacts of these units are arbitrary.

Let h,e be any positively oriented orthonormal frame. Let K in B and
L in C be actual minimum-support points or actual support-side means
for respective unit directions f,g, with

    f.e>=0, g.e<=0.

No contact owner is prescribed. Denote the actual centers by c_B,c_C,c_N.
Then the following necessary inequality holds:

    e.(K-L)
      +(1/2)*(f.e-|f.h|-g.e-|g.h|) <= 2sqrt(2).       (1)

This is a statement about the given squares, points and directions.
The points are not moved to endpoints, and the frame is only a proof
coordinate system.

### Proof of the center-offset bound

Let E be an actual unit square, X an actual minimum-f support point
or mean, and delta=c_E-X. In its actual orthonormal own frame,

    f.delta=(|f.u|+|f.v|)/2>=1/2,
    |delta|<=1/sqrt(2).

The first formula is its actual half-width. The second holds for every
actual point of the closed square, including every support-side mean.
Write delta=A f+B Jf. Then A>=1/2 and

    |B|<=sqrt(1/2-A^2)<=1/2.

If f.e>=0, therefore

    delta.e=A*(f.e)+B*(Jf.e)
            >=(1/2)*(f.e)-(1/2)*|f.h|.             (2)

Apply (2) to B, and apply its reflected version with -e to C. This gives

    (c_B-c_C).e
      >=e.(K-L)+(1/2)*(f.e-|f.h|-g.e-|g.h|).        (3)

At an actual B--N intersection point, both centers are within
1/sqrt(2) of that same point. Thus |c_B-c_N|<=sqrt(2).
The same argument at the actual C--N intersection gives
|c_C-c_N|<=sqrt(2). These two actual contacts imply

    |c_B-c_C|<=2sqrt(2).                            (4)

Finally (c_B-c_C).e<=|c_B-c_C|. Equations (3)--(4) prove (1).
Every weak corner, shared-side endpoint and side mean is included.
No containing-circle or force assumption is needed for this lemma.

## 2. Entire original perpendicular-singleton chart

Keep the exact full chart of

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md

at SHA256

    f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

All nine actual squares, original positive forces, means and circle data
remain. The original radius interval and radial parameter are

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60.

The full positive stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A and D are unloaded true3. V is loaded true2 with two PHYSICAL
circle corners. The original West/strict roof is

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c),
    c,s>0, c^2+s^2=1.

The original A-to-V normal is the A-owned h, of magnitude mu>0.
D-to-V is East, of magnitude nu>0. AD is a genuine singleton,
owned by A alone in its perpendicular direction -e, of magnitude
gamma>0. The full original geometric entry gives

    A=P+[-1,0]h+[-l,1-l]e,
    W=P-xh-le,
    0<l<1, 0<x<1.

The actual D roof point Q and AD point W are strict adjacent D
vertices. Write

    v=W-Q=-a h+b e=(-u,v_y),
    a=H s+x>0, b=H c-l>0,
    a^2+b^2=1,
    u=a c-b s>0, v_y=a s+b c>0,

    w=-b h-a e=(-v_y,-u),
    D=Q+[0,1]v+[0,1]w.                            (5)

The symbol v denotes the vector, and v_y its scalar world vertical
component. The relation u^2+v_y^2=1 follows from (5).
No D frame has been imposed independently; these are the actual edges.

For the present result assume additionally only that there is an actual
unit N, distinct from B,C, physically touching both B and C. No
degree or load premise on B,C,N is needed beyond the full A,D,V
stars already printed.

**Theorem.** The complete setting above is impossible whenever

    0<v_y<=1/8.                                    (6)

All original D exterior-support owners and all original D-side means
are included in this statement.

## 3. A single full D3 equation retains every exterior-support feature

The complete unloaded A3 force equation gives

    F_B=-mu h+gamma e,
    K=P-h+(1-l)e.                                  (7)

Both own components are strict, so K is the actual A support vertex
for the original AB force. It is an actual minimum-support point
of the retained B in direction

    f=F_B/|F_B|=(-h+r e)/sqrt(1+r^2),
    r=gamma/mu>0.                                 (8)

No force equation at B has been used.

The complete unloaded D3 force equation gives

    F_C=-nu East-gamma e,
    F_C.v=nu u-gamma b,
    F_C.w=nu v_y+gamma a>0.                        (9)

Its actual support on D therefore lies on the entire far-w face:

    L=Q+w+zv, 0<=z<=1.                            (10)

If the v component in (9) is negative, the actual z is zero.
If it is positive, the actual z is one.
If it is zero, z is the full original side point or shared-side mean.
Equation (10) retains the actual selected z, including both endpoints
before any torque consequence. It does not choose a new mean.

The full original D torque about Q includes its force toward A at
W=Q+v, its roof force at Q, and its exterior force at L. In the
positively oriented actual (v,w) frame it is exactly

    -gamma a -(nu u-gamma b)
        +z*(nu v_y+gamma a)=0.

Put q=gamma/nu>0. Rearrangement gives the single identity

    q*[b-(1-z)a]=u-z v_y.                           (11)

This equation covers every row in (10) at once. At z=0 it is the
previous adjacent-return identity; at z=1 it is the opposite-vertex
identity. The original side row is included without setting z to an
endpoint or shortening the star.

The original physical-two V2 also retains all three of its equations:

    mu c+nu=k(d+1),
    mu s=-k eta,
    nu t=mu*(d s+c/2),
    k>0, -1/2<=eta<=1/2.                           (12)

In particular, since d,s,t are positive and t<=1/2,

    nu/mu=(d s+c/2)/t>c.                           (13)

The closed eta interval keeps both individual-zero circle coefficients.
The proof has not reclassified either such endpoint as a unique physical
circle corner.

## 4. The whole tilt interval (6) forces both returns almost opposite

The positive original b has a useful exact interpretation:

    b=c v_y-s u>0.                                (14)

Squaring the positive inequality s u<c v_y and using the two unit
identities gives s^2<v_y^2. Hence

    s<v_y, c>u.

Also b=c v_y-s u<v_y, and so a>u. From (6),

    a>u>=sqrt(63)/8>99/100,
    c>u>99/100,
    0<b<v_y<=1/8.                                (15)

The displayed rational comparison follows from

    63/64-(99/100)^2=171/40000>0.

In particular u>v_y. For the original z in [0,1], the right-hand
side of (11) is at least u-v_y>0. Since q>0, its denominator
b-(1-z)a is strictly positive and is at most b. Thus (11) yields

    q >= (u-v_y)/b
        > (u-v_y)/v_y
        =u/v_y-1
        >=sqrt(63)-1
        >27/4.                                   (16)

Here sqrt(63)>31/4 because 63-(31/4)^2=47/16>0.
All inequalities remain strict when v_y=1/8. If an original endpoint
z were incompatible with (11), it has been excluded by that full moment
rather than removed from the domain beforehand.

Equations (13),(15),(16) give

    r=q*(nu/mu)>(27/4)*(99/100)
                     =2673/400>20/3,              (17)

where 2673/400-20/3=19/1200>0.

In the actual (h,e) frame the unit direction from D into C is

    g=F_C/|F_C|
      =[-c h-(s+q)e]/sqrt(c^2+(s+q)^2).            (18)

It satisfies g.e<0. Also

    (s+q)/c>q>27/4>20/3.                          (19)

These direction estimates used the complete D3 and V2 equations.
No fourth force was omitted, and no unloaded-N premise has entered.

## 5. Actual return separation contradicts the one-unit bridge

The exact e coordinates of the two original exterior applications give

    e.(K-L)
       =1-l+H c+a-zb
       =1+a+(1-z)b
       >=1+a>199/100.                            (20)

This calculation keeps the actual z throughout its original closed
interval. It does not require adjacent or opposite C applications.

Define the scalar function

    F(x)=(x-1)/sqrt(1+x^2), x>0.

Its derivative is (1+x)/(1+x^2)^(3/2)>0, so it increases on the
entire positive interval. Equations (8),(18) give exactly

    f.e-|f.h|=F(r),
    -g.e-|g.h|=F((s+q)/c).

By (17),(19), both expressions are strictly greater than

    F(20/3)=17/sqrt(409)>21/25.                    (21)

The final comparison is a positive square comparison:

    (17/sqrt(409))^2-(21/25)^2=256/255625>0.

Apply the actual-center inequality (3) to the actual B and C at
K,L. Equations (20)--(21) show that their actual centers obey

    (c_B-c_C).e
       >199/100+(1/2)*(21/25+21/25)
       =283/100>2sqrt(2).                         (22)

The last strict square reserve is

    (283/100)^2-8=89/10000>0.

But the actual N touching both B and C gives (4). This contradicts
(22). It proves the theorem over the whole closed tilt interval (6),
for every original C-side mean, every contact owner and every permitted
physical circle mask.

The proof uses the *actual* centers only as geometric quantities.
It has not reconstructed squares from centers, substituted an incircle
packing, or generated a new packing certificate.

## 6. Literal original D02 joins and the exact residual

In both original callers retain precisely

    A=0, V=1, D=2, C=3, N=4, B=5,

the rim A--V--D--C--N--B--A, and chord AD. A,D are unloaded true3,
while V,B,C are loaded true2. N is unloaded true2 in D02.L135 and
loaded true2 in D02.L1345. Their two original positive edges BN,CN
supply the actual physical B--N--C bridge needed above in both rows.

No force or circle coefficient at B,C,N is discarded. In particular
the loaded N in L1345 is never used as a transmitter. The three
actual additional units remain in the packing, although the local
center-reach contradiction does not need to place them.

The earlier complete perpendicular-singleton source already excludes
every adjacent D return and every return with c<=3/4. The new
theorem adds the full v_y<=1/8 domain in every D support row.
Consequently any survivor of this same exact original feature must
satisfy

    c>3/4, v_y>1/8,

and must be one of the unchanged two rows:

* Opposite D vertex, with original C point Q+v+w and
  nu*(u-v_y)=gamma b>0.
* D-owned exterior side, with original C point Q+w+zv, initially
  0<=z<=1, and nu u=gamma b together with
  z*(nu v_y+gamma a)=gamma a.

The latter full torque still deduces 0<z<1. These are necessary
surviving domains, not claimed realizable configurations.

Whole-data reflection transports the original labels, points, forces,
circle coefficients and frame together. It provides the same exclusion
for the reflected perpendicular-singleton chart. No independent exchange
of a unique-circle-adjacent and opposite tip vertex is invoked.

Other physical-two roof features, the unique-physical-circle features
and both entire original D02 load rows remain outside this theorem's
closure claim. No original identifier, fine flag, coarse flag or
inventory denominator is changed.

## 7. Sources and verification boundary

The complete chart source in Section 2 was read, and the new full
D3 identity (11), center-offset estimate and bridge contradiction
are independently derived above. The original physical force and
mean convention is PHYSICAL_CONTACT_STRESS.md at SHA256

    d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.

The literal graph/load source is
SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md at SHA256

    cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1.

The complete bridge inequality (1) is force-free and radius-free.
Its roof application keeps the existing conditional common-selection
domain of the original physical chart. It adds no selector and repairs
no missing global extraction premise.

The proof covers continuous intervals and exact algebraic endpoints.
The printed rational reserves are elementary corroborating arithmetic,
not an orientation search or a numerical exclusion certificate.
A full separate independent review is required before adoption.

No original square, positive force, selected normal, original mean,
circle mask, individual coefficient or true degree was changed. No
pose search, angle mesh, packing certificate, Lean/Lake build,
CI/workflow, metadata edit, remote mutation or merge was used.

