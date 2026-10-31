# Independent complete review of the full North hub-chord barrier exclusion

Date: October 28, 2026. Reviewer: recovery_audit.

**Verdict: PASS, complete for the whole original open-origin,
root-owned-singleton HX, North XA interface in roof ABC.S.** I read
the entire frozen source and independently rederived its two general
chord lemmas, both actual H-row identities, full continuous gap bound,
all original mean ranges and exhaustive B-frame cover. No source edit
was required. This is a fresh complete review of the exact new bytes.

Reviewed source:

    OPEN_ORIGIN_S_ROOT_NORTH_COMPLETE_HUB_CHORD_BARRIER_EXCLUSION.md
    bytes: 13266
    SHA-256: 89834bfea0e1ce1ff439f680cb5989583618d05929fc71de07ad72db726fd0e7
    Git blob: a037c43c0aff20f88d3e451edeb7d8c2a05d6561

This closes the entire stated North interface. The whole roof ABC.S
family, other original root interfaces and all original fine/coarse
ledger flags remain outside this source's own conclusion.

## 1. Complete geometric clearance lemma, including weak corner contact

Let the actual H be [A-1,A]x[Y-1,Y], and let actual B contain P,V
with P_x>=A, Y-1<P_y<Y, V_x<A-1/2 and V_y>Y-1.
No point of the closed B can lie in int(H): approximation by B's
interior points would violate interior disjointness. Consequently the
entire actual segment PV must avoid int(H), even if it lies on a B
side rather than in int(B).

If P_x=A, a short initial segment toward V enters int(H), since P's
height is strictly inside H's vertical interval. This whole endpoint
is already impossible. Otherwise P_x>A. At x=A the segment's height
is strictly above Y-1, because both endpoint heights are. A height
below Y would yield a subsequent open subsegment in int(H). Therefore
the crossing height is at least Y. This forces V_y>P_y and

    (V_y-P_y)/(P_x-V_x)>=(Y-P_y)/(P_x-A).

The proof correctly permits equality at H's actual top-right corner.
It never assumes a positive clearance from H where only nonoverlap
was available.

If P_x-A<(Y-P_y)/3, this inequality forces
V_y-P_y>3(P_x-V_x)>3/2>sqrt(2), impossible for two points of
the same actual unit. This is the entire first force-free lemma,
with no frame, degree, mask or force premise at B.

For the second lemma suppose Y-P_y>6/25 and ell=|P-V|<=1.
The direction from P to V is (-c,s), c,s>0 and c^2+s^2=1.
Writing ell c=P_x-V_x, the same clearance inequality is exactly

    (P_x-A)/c>=(Y-P_y)/s,
    ell>=(A-V_x)/c+(Y-P_y)/s
          >(1/2)/c+(6/25)/s.

This explicitly splits the actual segment into the portion needed
to reach H's top and the remaining horizontal travel past its outer
side. I checked the algebra; it does not sum independent distances
without this common-segment justification.

Cauchy's inequality gives

    (1/2)/c+(6/25)/s
      >=(sqrt(1/2)+sqrt(6/25))^2/(c+s)
      >=[37/50+2sqrt(3)/5]/sqrt(2)
       >71/(50sqrt(2))>1.

The two strict comparisons use sqrt(3)>17/10 and
71^2-2*50^2=41. They contradict ell<=1 over the complete continuous
direction interval. Both lemmas concern points of the same real B,
not a substituted test segment or a free-region diameter.

## 2. Both original H rows in one actual physical frame

I separately read and fully reviewed the exact prior unique-A source
74fa5a6f and all-mask transverse source e97a9639, including their
operative original chart, genuine degrees, masks and means. The
present source retains those literal hypotheses and all nine units.

In the actual orthonormal (v,u) coordinates, the whole H is exactly

    H=[a_H,A_0]v+[-c_0,1-c_0]u,
    A_0=1+a_H>1,
    0<=c_0=c_H<t<b<31/120.

The side row has auxiliary zeta=0 and d=A_0. The opposite row keeps
its actual zeta with 0<zeta<=c_0/A_0. In both cases

    L=sqrt(1+zeta^2),
    n=(v-zeta u)/L, e=(u+zeta v)/L,
    d=(A_0+c_0 zeta)/L.

The auxiliary zero in the side row is not a change to its actual HC
mean. Its physical shared HC interval and original mean remain exactly
as supplied by the operative source.

C keeps its full physical radial mask and its complete actual CB
support cover: inner upper corner P_0=d n+e/2 for g.n<0, or the
full side mean P=r n+e/2, d<=r<d+1, for g=e. Both original C
circle coefficients remain independent, including either zero value.

Every original AB point is

    V=h j+K w,
    h=1-J in(0,1/2), K=W+y>0, 0<=y<=1.

The actual frame identities are j.u=-w.v=q_H>0 and
j.v=w.u=p_H>0. The first is immediate from the original positive
alpha,beta,C_A,S_A. For the second, j.n>0 and j.e>0 from the
retained actual C chart, together with v=(n+zeta e)/L, suffice.
Therefore the whole original AB mean interval has

    V.v=h p_H-K q_H<1/2,
    V.u=h q_H+K p_H>0.

This proof includes every y endpoint and imposes no new B equation.

## 3. Full strict C-vertex return exclusion

For the original strict return point P_0=d n+e/2, define the
auxiliary scalar rho=1/2+(c_0-A_0 zeta)/L>=1/2. I substituted the
exact physical radial support relation and independently obtained

    P_0.v=A_0+zeta rho/L,
    P_0.u=-c_0+rho/L.

Thus the actual horizontal gap beyond H is zeta rho/L and its
actual top deficit is 1-rho/L. The auxiliary rho is not identified
with the original HC side mean or the transverse C2 concurrence
parameter, including when zeta=0.

The exact continuous polynomial estimate is valid throughout the
whole printed range c_0<4/15, A_0>=1, 0<=zeta<4/15:

    L^2-(L/2+c_0-A_0 zeta)(1+3zeta)
      >7/30-(13/10)zeta+(15/4)zeta^2-(3/4)zeta^3
      >=7/30-(13/10)zeta+(71/20)zeta^2
      >=487/4260>0.

I checked the first expansion using L<=1+zeta^2/2 and c_0<4/15.
The cubic bound uses zeta<4/15; it remains weakly valid at zeta=0.
The quadratic minimum is at zeta=13/71 and is exactly
7/30-169/1420=487/4260. Since Lrho=L/2+c_0-A_0 zeta, division
by positive L gives 3zeta rho<L-rho.

Consequently P_0 is strictly above H's bottom and below its top.
For zeta>0 its horizontal gap is less than one third of its top
deficit. For zeta=0 it lies directly on H's outer side, strictly
inside the height interval. The complete first chord lemma applies
to the unchanged actual P_0,V in the same B, with the actual H
rectangle. It gives a contradiction in both rows.

This excludes every g.n<0 return for every physical B mask, original
normal inside that cone and original AB mean. It requires no B force
or degree premise beyond the earlier legitimate derivation of the
entry chart. The actual H and B need not have a positive graph edge;
their physical interior disjointness is sufficient.

## 4. Exact full C-side mean interval and endpoint bookkeeping

The independently complete transverse feature exits give the original
vector G=gamma j, gamma>0. The whole-domain bounds are
n=pj-qw, e=qj+pw, 0<q<1/4, p>29/30 and W>4/5.
The only remaining C feature is g=e with unchanged mean
P=r n+e/2, d<=r<d+1.

By the original support directions, V is a minimum-j point of B and
P is a minimum-e point of B. In the real H frame,

    P.v=P_0.v+(r-d)/L>=A_0,
    P.u=(1/2-zeta r)/L<=1/2,
    P.u+c_0=[rho-zeta(r-d)]/L>0.

For full endpoint precision, the source's strict intermediate comparison
with (1/2-zeta)/L is immediate for zeta>0 because r-d<1 and
rho>=1/2. At zeta=0 the real side row has its original sigma>0
and sigma<=c_H, hence c_0>0 and rho=1/2+c_0>1/2. Thus that
strict comparison is also literal there. Even the weak comparison
would suffice for the final positive bound, since zeta<4/15<1/2.
No side mean is silently reinterpreted in this endpoint check.

It follows that P's height is strictly inside H's height interval,
with top deficit

    (1-c_0)-P.u>=1/2-c_0>29/120>6/25.

The exact final rational reserve is 1/600. These inequalities hold
for the entire original r interval, including r=d and all physical
shared CB means. Together with the full original V bounds they give
every coordinate premise of the second chord lemma.

## 5. Complete all-mask, all-frame B cover

There are exactly the three printed frame possibilities.

If B is parallel to A, its original minimum-j side is j=h<1/2.
The vector e=qj+pw has both components strictly positive, so its
actual minimum point is the unique minimum-j/minimum-w B corner.
Hence P.j=h<1/2. But its real C-side coordinates give
P.j=rp+q/2>=dp+q/2>29/30, a contradiction. This keeps every
actual AB side mean, including physical shared contact.

If B is parallel to C, its original minimum-e side is e=1/2.
The vector j=pn+qe has both components positive, so its actual
minimum is the unique minimum-n/minimum-e B corner. Thus V.e=1/2.
Its unchanged real coordinates give V.e=qh+pK>=pW>58/75, another
contradiction. The whole original CB side-mean interval remains.

If B is parallel to neither frame, neither incoming j nor e is a B
axis. Each has a unique actual minimum-support vertex, respectively
V and P. They are distinct because V.v<1/2 while P.v>=A_0>1.
If they were opposite vertices, the two nonaxis normal vectors would
have opposite signs in both B-own components and strictly negative
dot product. Their actual dot product is j.e=q>0, so this is impossible.
They are therefore adjacent actual B vertices, and |P-V|=1 exactly.

The second chord lemma now contradicts this last frame alternative
using the already established entire mean-range bounds. This step
uses the true side length of the same real B; it does not infer a
distance-one relation between arbitrary contacts or borrow an endpoint
owner from A or C. No new normal selector is used in this frame cover.

The three possibilities cover both physical B masks, all individual
zero coefficients, all physical shared contacts and all nonparallel
frames. No load condition is added at H or circle coefficients equated.

## 6. Exact original conclusion and source pins

The strict C-vertex and full C-side alternatives exhaust the original
CB cover. The prior complete positive/negative G.w exits reduce the
remaining side proof to the real G=gamma j law; their hypotheses are
the actual full A3/B2/C2 systems already reviewed. Thus the whole
original open-origin, root-owned-singleton HX, North XA interface of
roof ABC.S is excluded across both complete H3 rows.

Both direct pins match the exact current files:

| Source | SHA-256 |
| --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 |
| OPEN_ORIGIN_S_ROOT_NORTH_ALL_MASKS_NEGATIVE_TRANSVERSE_RETURN_EXCLUSION.md | e97a96393322d9a680677314069017a9eb3d6a6204187f13c1cc7d8b20f61fdf |

Their separate complete review records are
REVIEW_NORTH_RADIAL_RETURN_UNIQUE_A_CORNER_RECOVERY_AUDIT_2026_10_28.md
and REVIEW_NORTH_ALL_MASKS_NEGATIVE_RETURN_RECOVERY_AUDIT_2026_10_28.md.
The latter explicitly reviews the pinned positive-return and two-radial
prerequisites too. No historical review is transferred to the new source
without this fresh full rederivation.

The result is a full interface closure, not a declaration that the
entire roof ABC.S fine family or a coarse parent closes. All other
root domains retain their exact original obligations. All nine actual
squares, complete true forces and torques, original selected normals,
applications, means, physical masks and individual zero weights remain.

No numerical pose search, finite exclusion packet, invented neighbor,
false two-force equation, original mean replacement, Lean compilation,
CI, metadata edit or remote action was used in this hand review.
