# A K-owned northwest central return has no top boundary page

Date: October 27, 2026.  
Author: rooted_final_review.  
Original comparison head: 50c0cd616eb494ade100f055ad518cdbd33c7275.

**Status: complete analytic candidate, pending a separate full
independent review and restoration of the complete original input
bundle.** The whole singleton top page is excluded by its unchanged
C2 proper ray and one actual K-side identity. The whole shared top
page is excluded by a concave quadratic on the full real contact
interval. Both genuine B leaves remain. No computational certificate,
K2 equation, H3 equation or new selected normal is introduced.

## 1. Full actual chart and exact claim

Retain the same original nine-unit S/S hub-tip graph

    HK, HB, BK, HC, CK, HL_H, BL_B,

with true H4/K3/B3/C2, both occupied genuine radial S leaves,
positive K/C circle loads, all actual selected normals and positive
magnitudes, every original singleton point and shared-side mean,
and the three other physical units. Keep the original containing
circle and its origin. The original whole-mask theorems make K
and C physically unique.

Use the entire H-owned HB / K-owned HK / northwest BK chart
stated and derived in Sections 1--2 of the exactly recovered source

    SS_HUB_TIP_H_OWNED_SINGLETON_K_OWNED_NORTHWEST_PAGE_EXCLUSION.md
    SHA256 b6975fe44d944a6a202fc350d6a2bd64378fe15e7e1d61f1b6f6d2793ac8e1a7.

The necessary actual data are reproduced here:

    d=1+delta, 0<delta<1/60,
    R^2=(d+1)^2+1/4, 17/4<R^2<=1105/256, R<25/12;
    alpha,beta>0, alpha^2+beta^2=1, beta<1/2;
    h=alpha x_B-beta u_B, |h|<=delta, x_B<=delta;
    L=beta x_B+alpha u_B>0, u_B=alpha L-beta h;
    X=1-h, X^2+A^2=d^2;
    H=[h-1,h] x [-A,G], G=1-A;
    0<L<A<=2sqrt(delta)<31/120, 89/120<G<1.       (1)

The two unchanged genuine B rows are

    vertex: (1+x_B)^2+u_B^2=d^2, 1+x_B>0,
            0<u_B<2sqrt(delta),
            r_B=u_B/(beta+L);

    aligned: x_B=delta, 0<u_B<1,
             actual leaf direction (alpha,-beta),
             r_B=u_B/beta.                      (2)

The full actual K chart is

    m=m_BK=(-c,s), t=(s,c),
    c,s>0, c^2+s^2=1,
    K=S+[0,1]m+[0,1]t,
    R_H=P_HK=(h,G)=S+ell m, 0<ell<1,
    Q=P_BK=S+theta t, 0<theta<1,
    beta=ell c+theta s,
    k_B=c/s, r_B=beta+alpha k_B,
    A=L+(1-alpha)+beta k_B-ell/s.                (3)

In particular the actual central normal is H-to-K=t, owned by K.
HK and BK are physical singletons at the displayed actual points.
No force on H or K is deleted.

Put z=1-ell in (0,1). The complete degree-independent physical
corner lemma in Section 2 of the recovered source gives, before
any HC owner assumption,

    z_K=R_H+t+z m=(h+s-zc,G+c+zs),
    |z_K|=R.                                    (4)

That lemma retains all actual side positions and uses the original
cubic B-angle bound. Its conclusion is a fact about every physical
K circle point, not a K force or concurrence assertion.

**Theorem 1.1.** In this entire original chart, H cannot own its
actual HC normal E2. Both physical HC types, all original shared
means, and every CK physical type and owner are included.

This is the complementary top-page feature to the recovered
northwest-page exclusion. Section 9 records the exact original
union and the still-required independent review/recovery boundary.

## 2. A conditional root sign from both entire genuine B leaves

We need h<0 only when c<1/4. It is not a global premise.
In that angle interval k_B<1/sqrt(15)<4/15. Both actual rows
in (2) satisfy u_B>=beta r_B>beta^2. Combining x_B<=delta
and h>=-delta therefore gives

    beta^3<delta(1+alpha)<1/30,
    beta<1/3, alpha>14/15, alpha^2>8/9.           (5)

Set epsilon=1-alpha, t_0=beta/(1+alpha), and define only the
auxiliary scalar

    b_*=L+epsilon+beta k_B=A+ell/s>A.            (6)

The complete actual two-leaf calculation gives

    (1+h)^2+b_*^2<d^2.                          (7)

For clarity we reproduce it instead of importing any central-owner
or page premise from another exclusion. On the genuine vertex row,
use u_B=(beta+alpha k_B)(beta+L)=alpha L-beta h and its real
radial equation. Exact elimination gives

    d^2-(1+h)^2-b_*^2
      =2t_0(1-k_B)L
       +epsilon[2beta-epsilon
           +2(alpha-beta)k_B-(1+alpha)k_B^2].   (8)

The first term is positive, epsilon<beta, and

    2(alpha-beta)-(1+alpha)k_B
       >2(14/15-1/3)-2(4/15)=2/3>0.

Thus (8) is positive on the full actual vertex interval.

For the aligned row put r=r_B=beta+alpha k_B. Keep its own
actual coordinates h=alpha delta-beta^2r and
L=beta delta+alpha beta r. Expansion gives

    [d^2-(1+h)^2-b_*^2]/beta^2
       =2delta[(1-beta)/(1+alpha)-k_B]+F,
    F=2r-3r^2+2rt_0-(t_0+k_B)^2,
    r=t_0+alpha(t_0+k_B).                      (9)

The delta bracket exceeds 1/15. Also 0<t_0<r<3/5,
r<2t_0+4/15 and (t_0+k_B)^2<(9/8)(r-t_0)^2. The function
f(r,t)=2r-3r^2+2rt-(9/8)(r-t)^2 increases strictly on 0<=t<r.
If 0<r<=4/15, F>f(r,0)>=9r/10>0. If 4/15<=r<3/5,
the actual t_0>(r-4/15)/2 gives

    F>B(r)=(26/15)r-2r^2-(9/32)(r+4/15)^2,
    B''=-73/16,
    B(4/15)=6/25, B(3/5)=87/800.

Concavity proves positivity on that entire interval. This proves
(7) for the complete aligned slider too, without an artificial
vertex equation.

Subtract (7) from the real H leaf equality
(1-h)^2+A^2=d^2, and use b_*>A. It follows that

    c<1/4 implies h<0.                         (10)

This implication uses both genuine leaves and the actual K-owned
central position. It requires no C force, page owner, C circle
budget, small central gap or other angle estimate.

## 3. The complete singleton top-page C2 chart

First suppose HC is a physical singleton with its actual H-owned
normal E2. Its real point is T=(T_x,G), with

    h-1<T_x<h<1/60.

C has the full strict minimum-height vertex chart

    C=T+[0,1]e+[0,1]f,
    e=(-q,p), f=(p,q),
    p,q>0, p^2+q^2=1.                         (11)

Its true C2, with physical boundary neighbor K, has its unchanged
proper radial concurrence q_C=r_C z_C in C, r_C>0, and
q_C=T+eta_C E2 with eta_C>=0. If its circle were opposite T,
the actual horizontal equality and r_C>=G/(z_C)_y give

    2=|z_C-T|^2<=(R-G)^2<2,

because R-G<161/120<sqrt(2). T itself is not a circle point,
since it also belongs to H. The adjacent candidate T+f has
minimum-e coordinate -T_x q+Gp>-1/60>-1/2, so it cannot be
the unique physical circle corner. Consequently the real circle
is T+e. Its minimum-f own coordinate is below -1/2, so
T_x p+Gq<-1/2; in particular T_x<0 is derived, not presumed
from a sign for h.

Put w_0=-T_x. The actual H-side interval now gives

    0<w_0<1-h,
    z_C=(-w_0-q,G+p),
    a_C=Gp+w_0q>0,
    b_C=w_0p-Gq>1/2,
    a_C<d.                                    (12)

The last inequality follows from the exact radius and the strict
physical own-coordinate comparison. Hence
G=a_Cp-b_Cq<dp-q/2. The whole q>=39/100 alternative would
give p<921/1000 and then

    G<(61/60)(921/1000)-39/200
       =14827/20000<89/120.

The two rational reserves are 341/1000000 and 19/60000.
Therefore throughout the actual singleton row,

    q<39/100, p>23/25.                         (13)

The same real incoming line determines

    q_C=[w_0/(w_0+q)]z_C,
    q_C-T=[b_C/(w_0+q)]E2.

For the actual C-to-K normal n, the complete C2 equation is

    kappa_C z_C=omega E2-gamma n,
    kappa_C,omega,gamma>0.                    (14)

Its f projection gives n.f>0. The full actual support cover is:
if n.e<0, its application is T+f and its proper outgoing ray is
strictly right/down; if n.e>0, the application is T+e+f at height
G+p+q>G+1; if n.e=0, n=f with its full actual side retained.
For the first row the exact proper displacement is

    (T+f)-q_C=(p,-F_C/(w_0+q)),
    F_C=w_0(p-q)-Gq-q^2
       =b_C(1-pq)-(a_C+1)q^2
       >52379/4000000>0.                     (15)

The lower polynomial is 1/2-q/2+q^3/4-(121/60)q^2, decreasing
throughout [0,39/100], with that exact positive endpoint. Thus
the full proper sign is retained; no contact line is reselected.

## 4. Every singleton-page CK owner reduces to one actual K side

If CK is shared, it has a physical C side axis. If CK is singleton,
the two actual C applications are distinct: the complete coincident
radial-D exception would force K and C to share their circle point
by the unit-diameter equality. The existing common fixed-singleton
selector therefore supplies its actual side owner. This selector
is used only on the two fixed singleton applications, never on a
shared mean.

If C owns CK, the nonzero transverse component in (14) leaves
only n=f. But the physical triangle side-normal rule, applied at C
to its owned axis f and its actual direction toward H, -E2, gives

    f.(-E2)>=0,

whereas the actual value is -q<0. Thus this entire owner row,
including every shared CK, is physically impossible.

Suppose K alone owns CK. The triangle rule at K uses the actual
central normal K-to-H=-t and K-to-C=-n, so n.t>=0.
Among the four K axes, this leaves precisely m,-m,t.

For n=m, its e projection cq+sp is positive, so the actual C
point has height above G+1. K's entire minimum-m side has height
at most G-ell s+c<G+1. This is impossible.

For n=t, a positive e projection likewise requires a C point
above G+1, while K's entire minimum-t side has height at most
G+zs<G+1. A negative e projection requires the strict right/down
proper ray (15), while t has positive height. The zero projection
makes t=f a C side axis too and is excluded by the same physical
triangle rule used for C ownership. Every sign is covered.

The sole remaining actual normal is therefore

    n=-m=(c,-s).

Its e projection is -cq-sp<0, so its actual C point is T+f.
Retain the full K-owned side position:

    Z=T+f=R_H+z m+zeta t,
    0<zeta<1.                                 (16)

No original side endpoint or favorable application has been chosen.

## 5. One proper-ray inequality excludes that entire side

Define k=s/c for this section only; it is the reciprocal of k_B.
The exact actual C2 ray (15) and n=(c,-s) give

    k=F_C/[p(w_0+q)]<1-q/p<1.                 (17)

The strict comparison follows by subtracting:
(w_0+q)(p-q)-F_C=q(p+G)>0. All divided quantities are
positive. Thus c>s and c>1/sqrt(2).

The two components of the same actual point identity (16) are

    q=zs+zeta c,
    w_0+h=p+zc-zeta s=p+z/c-kq.               (18)

Because its actual H-side point has w_0+h<1, these give

    z/c<1-p+kq=q[q/(1+p)+k]<q.                (19)

Indeed (17) implies k+q/(1+p)<1-q/[p(1+p)]<1.
The actual central relation in (3) now implies

    beta>ell c=(1-z)c>c-c^2q.

For the entire interval c in [1/sqrt(2),1], the function
c-c^2q is increasing, since 1-2cq>1-78/100>0. Therefore

    beta>1/sqrt(2)-q/2
        >7/10-39/200=101/200>1/2.             (20)

This contradicts the original beta<1/2. The two last strict
reserves are 1/2-(7/10)^2=1/100 and
101/200-1/2=1/200. Thus the entire singleton HC feature is
excluded independently of h's sign and with every actual K-side
application retained.

## 6. The complete shared top-page normal cone

Now suppose HC has positive shared length. Its actual placement
and original real mean have

    C=[l,l+1] x [G,G+1],
    P_HC=(x_0,G), h-1<=x_0<=h<1/60.           (21)

The unique actual C circle is on its top side. Its horizontal
coordinate has the sign of x_0 by the positive radial concurrence.
If it were positive, physical uniqueness would give its own
coordinate greater than 1/2. The actual incoming proper line has
r_C>=G/(G+1), so

    x_0>G/[2(G+1)]>89/418>1/60,

contradicting (21). The zero circle coordinate is incompatible with
physical uniqueness. Hence the actual circle and force signs are

    z_C=(l,G+1), l<-1/2,
    n_x>0, n_y<=0,                            (22)

where n is the unchanged C-to-K normal. The horizontal sign is
from the full C2 force; the height sign is from the physical triangle
rule at C's owned incoming side -E2.

The actual K-owned central side gives n.t>=0, while
n.m=-cn_x+sn_y<0. If n_y<0, the actual C support is its
bottom-right vertex (l+1,G). If n.t>0, K's actual support is
R_H+z m at height G+zs>G. If n.t=0, its entire support is
R_H+z m+[0,1]t, again strictly above G. Both are impossible.
This retains the full possible free/side CK normal cone.

Thus necessarily n=E1. Its actual K support is R_H+z m,
and its C support is the right side. Equality of the real supports
gives

    l+1=h-zc,
    z_C=(h-zc-1,G+1).                         (23)

No shared HC mean was set to an endpoint or substituted into
another force line to obtain this actual circle.

## 7. One complete concave comparison excludes the shared row

Compare (23) with the actual K circle (4). Exact expansion gives

    D:=|z_C|^2-|z_K|^2
      =-2h(1+s)+2zc+1-z^2s^2
                       +2G(1-c-zs).         (24)

Keep the full actual z in (0,1). Put

    Q(z)=2zc+1-z^2s^2,
    F(z)=3-2c-2zs+2zc-z^2s^2.

Both are concave quadratics in z on the whole interval [0,1],
with exact endpoint values

    Q(0)=1, Q(1)=2c+c^2,
    F(0)=3-2c,
    F(1)=3-2s-s^2=(1-s)(3+s).                (25)

First suppose c<1/4. The original two-leaf calculation (10)
gives h<0. If 1-c-zs>=0, every term of (24) except possibly
the last is strictly positive, so D>0. If 1-c-zs<0, G<1
gives D>F(z). Both endpoints of F in (25) are strictly positive
because 0<c,s<1. Concavity again gives D>0.

Now suppose c>=1/4. The original h<1/60 gives
-2h(1+s)>-1/15. If 1-c-zs>=0, use (25):

    D>-1/15+Q(z)
       >=-1/15+min(1,2c+c^2)
       >=-1/15+9/16=119/240>0.               (26)

If 1-c-zs<0, again G<1 gives D>-1/15+F(z).
Here s<=sqrt(15)/4<31/32, so

    F(0)>1,
    F(1)>3-2(31/32)-(31/32)^2=127/1024.

Concavity over the whole actual z interval therefore gives

    D>-1/15+127/1024=881/15360>0.             (27)

These cases include c=1/4 and the zero sign of 1-c-zs. The
comparison uses closed z endpoints only to bound its entire actual
interval; it does not move the contact to one of those endpoints.
Both actual circle norms equal R, contradicting D>0. This
excludes the complete shared HC row.

## 8. Full original feature conclusion

Sections 3--5 cover the whole singleton HC feature. They derive
the actual C circle sign even when h is positive, retain the full
physical CK type/owner boundary, and use the exact original C2
ray and actual K-side point to obtain the single contradiction
beta>1/2. No auxiliary K or H force law is used.

Sections 6--7 cover the entire shared HC feature, including every
actual mean and every initial CK owner or free normal. The actual
C/K circle comparison uses only (4) and one concave quadratic.
The genuine B leaves enter only through the full conditional
calculation when c<1/4; the complementary angle interval has a
strict direct rational reserve without any h sign assumption.

This proves Theorem 1.1. No K2 or H3 is inferred, no original
force or square is removed, and no computational packet is needed.

## 9. Original remaining union and recovery boundary

In the full original H-owned HB/K-owned NW-central chart, the
positive-page and actual application-separation inputs give the
complete HC direction cover: a strict NE contact would use the
already occupied actual central application R_H; an E1 contact
would enter the actual occupied triangle P_HB,Q_BK,R_H; a -E1
contact separates C from K since min_K x=h-zc>h-1; negative
height was already excluded. The only remaining alternatives are
the H-owned E2 top page and the strict NW page at (h-1,G).

The exactly recovered source b6975fe4 supplies the full NW page
exclusion, including its free-HC/shared-CK exception. The present
source supplies the entire E2 complement. This is the geometric
union for the last central feature of H-owned HB. An original
whole-owner assembly still must pin all earlier complete sources,
their separate independent reviews and the exact original caller.
Those missing artifacts are not declared recovered merely because
their earlier hashes remain in the conversation.

The complete direct inputs are:

| Complete source | SHA256 | Exact scope |
| --- | --- | --- |
| SS_HUB_TIP_H_OWNED_SINGLETON_K_OWNED_NORTHWEST_PAGE_EXCLUSION.md | b6975fe44d944a6a202fc350d6a2bd64378fe15e7e1d61f1b6f6d2793ac8e1a7 | Exactly recovered original chart and entire degree-independent physical K-circle lemma in Sections 1--2; local two-leaf argument reproduced above; its full NW exclusion only in the final stated union |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Actual loaded unique true-C2 proper radial line, with physical K boundary neighbor |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full physical triangle nonobtuse side-normal signs; no degree premise |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing original actual owner selection only for two distinct fixed singleton C2 points |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Unique circle own-coordinate inequalities and impossibility of sharing a containing-circle point |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual selected singleton/shared normal convention, genuine positive forces and unchanged means |

The full new mathematical/exact-source review of b6975fe4 is

    REVIEW_SS_HUB_TIP_K_OWNED_NW_PAGE_CERT_INDEPENDENT_2026_10_27.md
    SHA256 874ec260fc9792b86a8eef7e5503bc297d562fca5812e543bcc921af6ba0f161.

It explicitly records which older prerequisites remain missing after
the filesystem rollback. The present new manuscript requires its
own separate complete independent review. No original gate, ledger,
remote repository, Lean source or CI workflow is changed here.
