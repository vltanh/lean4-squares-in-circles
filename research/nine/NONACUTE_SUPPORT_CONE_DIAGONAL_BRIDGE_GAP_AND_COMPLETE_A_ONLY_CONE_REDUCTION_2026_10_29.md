# A non-acute support-cone gap theorem for every actual diagonal bridge

Date: October 29, 2026 UTC. Author: Type II A-owner continuation.

**Status: complete proposed generic hand theorem and exact whole-row
cone reduction, awaiting independent review.** The theorem removes the
acute-dot-product premise from the earlier diagonal support-cone
argument. It gives an exhaustive three-alternative description, including
every original support-axis tie and every full side mean. It applies at
arbitrary endpoint degrees and loads.

For the entire Type II A-only h owner, the unchanged A/D equations imply
the required positive-cone condition and a support separation greater
than two. Thus every original diagonal return in that row must satisfy
one of the two remaining alternatives printed below. This is a complete
necessary reduction, **not an exclusion of the whole A-only owner**.
Its side-return alternative, remaining diagonal alternatives, loaded-N
case and nine-square completion remain open here.

## 1. Original physical hypotheses and notation

Let B,C,N be distinct actual unit squares with disjoint open interiors.
Let Q_B be any actual minimum support of B in unit direction b, and
let Q_C be any actual minimum support of C in unit direction -c, where
c is unit. Either support can be a strict vertex, an original side
point, a full shared-side mean, or either endpoint of that mean's
original interval. Put

    Delta = Q_B-Q_C = lambda*b+eta*c,
    lambda,eta >= 0, lambda+eta > 0.                 (1)

There is **no hypothesis on the sign of b.c**. The parallel and
antiparallel cases, and zero cone coefficients, remain in the theorem.

Retain the entire original star at N: it has zero total circle load
and exactly two positive body-pair forces, toward B and C, at the
original actual applications T in B and U in C. Its full force and
torque equations hold. Suppose this original transmission is diagonal.

Retain the same initial incident-diagonal avoidance used by the earlier
support-cone theorem: at a physical point-only vertex/vertex contact,
the unchanged selected strict common normal is not a diagonal of either
incident square. This premise belongs to the original common selection,
before multipliers. No normal is changed after extraction.

The full unloaded two-force system implies that, for an actual unit
direction d,

    T-U = sqrt(2)*d.                                (2)

Both applications are opposite vertices of the actual N. Its normal d
is not an N side axis, so neither contact has positive shared length.
The retained diagonal avoidance excludes a vertex in the other square
at either endpoint. Therefore T and U are relative-side-interior in B
and C respectively, and both actual endpoint squares own d.

Choose a unit w perpendicular to d, so that (d,w) is oriented. The
unchanged endpoint squares have the full descriptions

    B = T + [0,1]*d + [-beta,1-beta]*w,
    C = U + [-1,0]*d + [-chi,1-chi]*w,
    0 <= beta,chi <= 1.                             (3)

Actual relative interiors give strict beta,chi, but this proof permits
their closed enlargement. Every support mean still ranges over its
entire original support face within these same actual squares.

Define the original normal components

    b_d=b.d, b_w=b.w, c_d=c.d, c_w=c.w.

The d coordinates of the two supports give exactly

    Delta.d = sqrt(2)+xi_B+xi_C,
    0 <= xi_B,xi_C <= 1,                            (4)

where xi_B=Q_B.d-T.d and xi_C=U.d-Q_C.d.

## 2. The full tangent bound needs no acute assumption

First b_w and c_w cannot have the same strict sign.

If both are positive, the minimum-b support Q_B is on the minimum-w
side of B, whereas Q_C, being a maximum-c support of C, is on the
maximum-w side of C. Consequently (3) gives

    Delta.w = -beta-(1-chi) = chi-beta-1 <= 0.

But (1) gives Delta.w=lambda*b_w+eta*c_w>0, a contradiction.
If both components are negative, the same supports give

    Delta.w = (1-beta)-(-chi) = 1-beta+chi >= 0,

whereas (1) gives a strictly negative value. Hence

    b_w*c_w <= 0.                                  (5)

Here is the entire sign-and-tie cover of (5):

* If b_w>0,c_w<0, both Q_B and Q_C are their squares' minimum-w
  supports, so Delta.w=chi-beta in [-1,1]. If b_w<0,c_w>0,
  both are maximum-w supports, with the same difference chi-beta.
* If b_w=0,c_w>0, retain Q_B's entire original coordinate
  v_B in [-beta,1-beta]. Then Delta.w=v_B-1+chi<=1,
  and (1) gives Delta.w=eta*c_w>=0. If b_w=0,c_w<0,
  then Delta.w=v_B+chi>=-1, and (1) gives Delta.w<=0.
* If c_w=0,b_w>0, retain Q_C's entire original coordinate
  v_C in [-chi,1-chi]. Then Delta.w=-beta-v_C<=1,
  and (1) gives Delta.w=lambda*b_w>=0. If c_w=0,b_w<0,
  then Delta.w=1-beta-v_C>=-1, and (1) gives Delta.w<=0.
* If b_w=c_w=0, (1) gives Delta.w=0.

Thus every original mean, each zero cone coefficient, every axis tie
and both enlarged side endpoints satisfy

    |Delta.w| <= 1.                                 (6)

No step in this tangent proof uses b.c>0.

## 3. An exhaustive original d-component classification

Because Q_B is a minimum-b support in (3),

    b_d>0 => xi_B=0,
    b_d<0 => xi_B=1,
    b_d=0 => xi_B is its full original value in [0,1].

Because Q_C is a maximum-c support in (3), the same alternatives hold
for c_d and xi_C. A zero component is a genuine original support side;
its coordinate is not replaced by an endpoint.

Both b_d and c_d cannot be nonpositive: (1) would then give
Delta.d<=0, contradicting (4). Therefore the complete cover is exactly:

1. **Both are strictly positive.** Then xi_B=xi_C=0, so

       Delta.d=sqrt(2), |Delta|^2<=3.                 (7)

2. **One is strictly positive and the other strictly negative.**
   Then {xi_B,xi_C}={0,1}, so

       Delta.d=1+sqrt(2),
       (1+sqrt(2))^2 <= |Delta|^2
         <= (1+sqrt(2))^2+1.                         (8)

3. **One is strictly positive and the other zero.** If b_d=0,
   then b=+w or b=-w because b is unit, and (6) gives

       |Delta.b|<=1,
       Delta.d=sqrt(2)+xi_B,
       0<=xi_B<=1.                                  (9)

   The other case c_d=0 gives |Delta.c|<=1 and the analogous
   whole original xi_C interval.

The three cases exhaust every sign endpoint. In particular, two zero
components and a negative component paired with zero were already
excluded by the positive d coordinate in (4).

## 4. Generic gap theorem and precise endpoint consequence

Combining (7)--(9) proves:

**Non-acute diagonal support-cone gap theorem.** Under the entire
original hypotheses of Section 1, at least one of the following holds:

    |Delta| <= sqrt(3);
    |Delta| >= 1+sqrt(2);
    |Delta.b| <= 1;
    |Delta.c| <= 1.                                 (10)

The stronger exact classification (7)--(9) is also part of the theorem.
It follows that the four strict inequalities

    sqrt(3) < |Delta| < 1+sqrt(2),
    |Delta.b| > 1, |Delta.c| > 1                     (11)

exclude every actual diagonal unloaded bridge, without an acute
assumption, radius estimate, endpoint load equation or endpoint degree
restriction.

More precisely, throughout the entire intermediate separation interval
sqrt(3)<|Delta|<1+sqrt(2), any surviving diagonal bridge must have
**one original endpoint support normal perpendicular to the actual
channel d**, the other normal having positive d component. The tied
endpoint owns both perpendicular axes: it already owns d from the actual
N contact, and it owns b or c from the exact zero component. Its full
original support mean satisfies the corresponding bound in (9).

No boundary of (10) is discarded: equality at either norm endpoint,
or at a projection value one, is included in its displayed alternative.

The earlier acute theorem is recovered exactly. Indeed (5) and b.c>0
would give b_d*c_d=b.c-b_w*c_w>0. Both d components must then be
strictly positive, so only (7) remains. Thus this extension retains the
entire earlier conclusion wherever its original acute hypothesis holds.

## 5. The whole original Type II A-only h row lies in this cone

Keep all nine actual squares and the entire original Type II chart
from the singleton-West domain source. In particular the stars remain

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3 and V is loaded true2. The full B,C,N stars,
physical circle masks, individual zero circle coefficients, selected
normals, positive forces and all original support applications remain.
The prior simultaneous common-selection entry remains an explicit
conditional input; the following algebra makes no new selection.

Use the actual A frame

    h=(c0,-s), e=(s,c0), c0,s>0, c0^2+s^2=1,

and the actual D frame

    nD=K*h+H*e, tD=-H*h+K*e,
    K=-k<0, H>k>0, H^2+k^2=1.

For this entire genuine A-only h owner, alpha>pi/4 gives s>c0.
The complete original interfaces and full moments are

    A=R-[0,1]*h-[0,1]*e,
    D=P-[0,1]*nD+[-t,1-t]*tD,
    R=P+omega*North,
    W=R-z*e=P+(1-t)*tD,
    0<omega,t,z<1,
    z=omega*S/H, t=1-omega*s/H,

    rho*(1-z)=mu*(s-c0),
    nu*t=rho*(H-k),                              (12)

with the unchanged positive original magnitudes mu,nu,rho. The full
V equations also remain, in particular

    (mu/nu)*(1-omega)=S-C>0.                        (13)

No independent force ratio is substituted for these equations.

Write

    u=1-z in (0,1), x=s-c0>0,
    p=H-k>0, L=1+H+k>2,
    r=rho/nu=t/p>0.                               (14)

Since H,k>0 and H^2+k^2=1, H+k>1, proving the strict L bound.
The original exterior supports are forced strict A and D vertices:

    Q_B=R-h-e=W-h-u*e,
    Q_C=P-nD-t*tD=W-nD-tD.

Therefore their exact difference, with no origin translation of the
disk, is

    Delta=Q_B-Q_C=-L*h+(p-u)*e.                     (15)

The unchanged original inward forces at B,C are

    F_B=-(mu*c0+rho)*h-mu*s*e,
    F_C=(rho+nu*k)*h-nu*H*e.                      (16)

Let b=F_B/|F_B| and c=-F_C/|F_C|, exactly as in Section 1.
Positive scaling and the original A moment in (12) allow the raw vectors

    b0=-(x+c0*u)*h-s*u*e,
    c0vec=-(r+k)*h+H*e,
    b=b0/|b0|, c=c0vec/|c0vec|.                    (17)

These are the same original directions, not newly assigned normals.
Set A0=x+c0*u>0 and B0=s*u>0. Their determinant is

    det(c0vec,b0)=(r+k)*B0+H*A0>0.                 (18)

The first cone numerator is

    det(c0vec,Delta)=H*L-(r+k)*(p-u)>0.             (19)

If p-u<=0, strictness is immediate. If p-u>0, then p-u<p and
the entire original D moment rp=t gives

    H*L-(r+k)*(p-u)
      >H*L-(r+k)*p
       =1+H-t>0,

using t<1. This covers every original p-u sign and its zero boundary.

For the other cone numerator,

    det(Delta,b0)=L*B0+(p-u)*A0>0.                 (20)

If p-u>=0, this is immediate. If p-u<0, then p-u>-u because
p>0, so

    L*B0+(p-u)*A0
      >L*s*u-u*(x+c0*u)
       =u*[s*(H+k)+c0*(1-u)]>0.

Equations (18)--(20) give a strictly positive representation

    Delta=lambda0*b0+eta0*c0vec,
    lambda0=det(c0vec,Delta)/det(c0vec,b0)>0,
    eta0=det(Delta,b0)/det(c0vec,b0)>0.

Multiplying these coefficients by the positive vector lengths gives
exactly (1) for the original unit directions b,c. Thus the **entire
A-only h owner**, without an added acute premise, satisfies the
positive-cone input. Its actual support separation also has

    |Delta|>=L>2>sqrt(3).                          (21)

## 6. Exact original load consequence and remaining alternatives

Retain the original labels

    A=0,V=1,D=2,C=3,N=4,B=5,
    rim A--V--D--C--N--B--A, chord AD.

In D02.L135, N is exactly the original unloaded true2. If it transmits
diagonally, Sections 1--5 apply literally. The small-separation
alternative of (10) contradicts (21). Consequently every surviving
diagonal in the whole A-only h owner must satisfy

    |Delta|>=1+sqrt(2),
    or |Delta.b|<=1,
    or |Delta.c|<=1.                               (22)

Whenever sqrt(3)<|Delta|<1+sqrt(2), the surviving contact is the
actual perpendicular endpoint tie of Section 4, with its original full
support mean. This is not a replacement of that tie by a strict vertex.

The original side-transmitting N is outside the diagonal hypothesis;
it still requires an exit. In D02.L1345, N has positive total circle
load and is not assigned an unloaded equation. All three completing
actual squares remain in both callers. No whole Type II owner, D02
parent, global sharp radius theorem or equality classification is
declared closed here.

## 7. Complete inputs and verification boundary

All four complete operative sources were read at the pinned PR head
3722e033d108293b679a0b23ea05504181e4c3fe:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original unloaded true2 force and torque; actual diagonal transmission and support points |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Same retained initial incident-diagonal avoidance and its endpoint-owner consequence |
| ACUTE_RETURN_SUPPORT_CONE_DIAGONAL_BRIDGE_BOUND_AND_TYPE_II_PERPENDICULAR_SIDE_ONLY_REDUCTION_2026_10_29.md | ae0ecc5190c6b92116c6f52ee8fccb375598e9152a5385cdc29ade149cfac528 | Earlier acute theorem; the entire non-acute extension is proved here, including all original tangent means |
| UNIQUE_CIRCLE_TYPE_II_SINGLETON_WEST_COMPLETE_HUB_OWNER_AND_EXTERNAL_RETURN_DOMAIN_2026_10_29.md | e63a1e1d14c50363a244dae4d8927b2113a4222ca1064777660a366b092f351c | Complete original A-only h chart, every positive V/A/D force and moment, both load callers and all nine actual units |

This proof uses no numerical pose search, angle mesh, packing certificate,
changed normal, replaced mean, shortened star, altered physical mask,
removed square, Lean/Lake compilation, CI/workflow, remote write or merge.
The new exact support cover is finite and complete, but its necessary
alternatives are not mislabeled as already excluded packing families.

