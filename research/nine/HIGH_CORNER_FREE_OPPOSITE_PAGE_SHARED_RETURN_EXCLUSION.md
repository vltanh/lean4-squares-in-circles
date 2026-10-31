# A free opposite-corner page cannot share its boundary return

Date: October 27, 2026.  
Author: cert_final_review.

**Status: complete new analytic candidate, pending separate full independent review.**
This is a local physical and true-C2 theorem. It covers the entire
shared-return interval and the actual free normal cone. It does not
use a force equation, a prescribed positive degree, or a unique
physical circle mask at the central boundary unit K.

The source is freshly saved after the workspace rollback. It is not
a claimed restoration of an earlier manuscript. Its two complete
original inputs are present and pinned in Section 7.

## 1. Complete local domain

Let H,K,C be interior-disjoint physical unit squares contained in
the origin-centered disk of radius R, where

    R^2>=17/4.

Let

    H=[h-1,h] x [G-1,G],
    -1/60<h<=0, 89/120<G<=1,
    R_0=(h,G), F=(h-1,G).

The actual HK contact is a singleton owned by K, at H's upper-right
vertex R_0. Write its complete actual K frame and strict actual
side position as

    m=(-c,s), t=(s,c),
    c,s>0, c^2+s^2=1,
    K=R_0+[-ell,1-ell]m+[0,1]t,
    0<ell<1.

Thus the actual H-to-K normal is t. K physically touches the
containing circle. Its other contacts, forces, degree and physical
circle mask are arbitrary.

Assume HC is a physical singleton at the opposite upper H vertex F,
with an actual free normal n directed from H to C. In the physical
certificate, this means F is also a C vertex and n is strict in
both corresponding vertex cones. Assume CK is physically shared
with positive overlap. C has exactly one physical circle corner z_C,
a positive circle load, and exactly the two positive pair forces
HC and CK. All actual shared-side means and force magnitudes are
retained.

**Theorem 1.1.** No such configuration exists.

No H leaf, B unit, additional edge, or force equation at H or K is
needed. The boundary point h=0 and height G=1 are included.

## 2. All four shared translations

A positive shared CK forces C and K to have the same side frame.
Use m,t coordinates relative to R_0. Then

    K=[-ell,1-ell] x [0,1],
    F=(c,-s).

The four signed side translations exhaust every coframed unit square
with a positive shared segment.

Across the maximum-t side, C has t-coordinate at least one, so it
does not contain F. Across the minimum-m side, C has m-coordinate
at most -ell<0, while F has m-coordinate c>0. This also misses F.

Across the minimum-t side, C's t interval is [-1,0]. The coordinate
-s is strictly inside that interval, so F cannot be a C vertex.
That placement cannot be the actual free HC feature in the theorem.
It is not silently converted to an owned HC contact.

Across the maximum-m side, the full possible placement is

    C=R_0+[1-ell,2-ell]m+[zeta,zeta+1]t,
    -1<zeta<1.

For F to be a vertex, its coordinate c<1 must be the lower m
endpoint; the upper endpoint 2-ell is greater than one. Thus
ell=1-c. Similarly -s must be the lower t endpoint. Choosing the
upper endpoint would give zeta=-s-1<-1, contrary to positive
physical shared overlap.

Consequently the entire remaining physical feature is exactly

    ell=1-c, zeta=-s,
    C=F+[0,1]m+[0,1]t,
    w_CK=-m.

No force mean has been assigned a chosen value. The actual CK mean
may be anywhere in its true shared interval.

## 3. The actual C circle is fixed by its genuine force

Since HC is free at C's minimum-m/minimum-t vertex F, its unchanged
actual normal satisfies

    n.m>0, n.t>0.

Let omega,gamma>0 be the actual HC,CK magnitudes. The true unique
circle C2 force is

    kappa_C z_C=omega n-gamma w_CK
              =omega n+gamma m,
    kappa_C>0.

Both own coordinates of the actual circle vector z_C are therefore
strictly positive. Containment of a unit square makes a positive
own coordinate of a circle corner belong to the maximum side in
that coordinate. Thus its actual unique circle corner is

    z_C=F+m+t.

This uses the real free normal and the real C2 force. No new normal
selection, shared-side application, or two-force equation at K is
introduced.

## 4. The two minimum-t K corners are inside

The two minimum-t corners of K are each at distance less than one
from R_0. Also

    |R_0|^2<=1+h^2<1+1/3600<(61/60)^2.

Their norms are therefore strictly less than 121/60. The exact
radius comparison is

    17/4-(121/60)^2=659/3600>0.

Neither of these two corners can touch the containing circle.
It remains to compare both maximum-t corners; there is no need
to decide which K corner could otherwise carry a physical circle
contact or circle force.

## 5. C's circle strictly dominates both remaining K corners

Using ell=1-c, the two actual maximum-t corners are

    z_+=R_0+c m+t,
    z_-=R_0-(1-c)m+t.

Direct expansion, with c^2+s^2=1, gives

    |z_C|^2-|z_+|^2
      =-2h(c+s^2)+2Gs(1-c)+2c+(1-s)^2.

Every term is nonnegative and 2c>0. Hence z_+ has norm strictly
less than the actual C circle radius R over the entire angle
interval, including h=0 and G=1.

The second exact difference is

    |z_C|^2-|z_-|^2
      =-2h(1+2c-c^2)+2Gs(2-c)
         +1+4c-c^2-2s.

Here 1+2c-c^2>0, so the first term is nonnegative. The constant
part 1+4c-c^2 is greater than one. The remaining vertical part
satisfies

    2Gs(2-c)-2s
       >=2s(G-1)>=-2(1-G)>-31/60.

The non-strict middle inequality retains G=1. The final strict
inequality follows from G>89/120. Thus in every case

    |z_C|^2-|z_-|^2>29/60>0.

Both actual maximum-t K corners are strictly inside the disk whose
radius is |z_C|=R.

## 6. Whole contradiction and scope

All four actual K vertices have norm strictly below R. A convex
combination of those vertices also has squared norm strictly below
R^2, so K has no physical point on the containing circle. This
contradicts its boundary premise and proves Theorem 1.1.

The proof retains the entire actual free HC cone, every shared CK
mean and endpoint, all K masks and all other forces. The maximum-t
K circle was not chosen in advance: both candidates are dominated
by the actual C circle. No three-force concurrence or K2 equation
is used. There is no numerical sample, angle subdivision or
computational certificate.

An original caller must establish the displayed actual central
chart, h<=0, the height interval, unique loaded true C2, and the
free opposite-upper HC application. A general page or an arbitrary
central normal is not covered without that chart. This local proof
does not by itself close an original graph gate or change a ledger.

## 7. Present exact original inputs

| Complete input | SHA256 | Scope used |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual vertex/vertex free normal convention, strict K-owned singleton side position, complete positive C2 force, unchanged shared means |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Unique physical circle-corner own-coordinate signs and containing-circle point geometry |

Both complete inputs are present under current_pr11/research/nine
and were read and rehashed. The geometric translation cover and
both norm comparisons are proved completely above. No missing
recent continuation source is a logical prerequisite.
