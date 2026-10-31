# Complete independent review: free opposite-corner page with a shared return

Date: October 27, 2026.  
Reviewer: rooted_final_review.  
Author of the reviewed theorem: cert_final_review.

## 1. Frozen target, verdict and independence

**PASS of the entire seven-section local theorem, unchanged.**

The exact target is

`HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md`

with SHA256

`7df434664a33019260a1b5b41983989a536f223edca4702cfed9a91786bb4f9e`.

I read the complete target and both complete original direct inputs,
independently reconstructed every physical placement, force sign and
circle comparison, and verified the target and both input byte hashes.
No correction is requested. I did not author or contribute an argument
to this target. My earlier work on other hub-tip features is not used as
an unrecorded prerequisite of this review.

This is complete acceptance of the displayed local theorem, including
its boundary values h=0 and G=1. It is not an acceptance of an unstated
original caller or a whole original graph gate. A caller still has to
establish all the actual geometric and force premises listed below.

The target is a newly saved source after the workspace rollback. Its two
logical inputs are present and verified. It does not depend on any of
the unavailable recent continuation manuscripts or review files.

## 2. Entire domain and actual-force contract

I retained the original local contract without replacing the actual
normal or any contact application:

* H,K,C are physical interior-disjoint unit squares in one centered disk,
  with R squared at least 17/4.
* H is `[h-1,h] x [G-1,G]`, with `-1/60<h<=0` and
  `89/120<G<=1`.
* The actual HK contact is K-owned and singleton at
  `R_0=(h,G)`. With `m=(-c,s)`, `t=(s,c)`, `c,s>0`,
  `c^2+s^2=1`, its full physical K chart is
  `R_0+[-ell,1-ell]m+[0,1]t`, with `0<ell<1`.
  The actual H-to-K normal is t.
* K has at least one physical circle contact. Its force degree, other
  forces, circle load and physical mask are unrestricted.
* The actual HC singleton is at `F=(h-1,G)` and is free. Thus F is
  a genuine C vertex and the actual normal n is strict in the two
  relevant vertex cones. It is not an endpoint of a side-owned feature
  silently reclassified by the proof.
* CK is physically shared with positive overlap. Its actual side mean
  remains free over the whole true interval.
* C has one physical circle corner z_C, a positive circle load, and
  exactly the two positive pair loads HC and CK. The proof uses its true
  C2 force equation and makes no degree-two inference at K.

The upper radius, leaf geometry, another square B, global contact graph,
H force equation and K force equation do not enter the new proof. In
particular, the statement is not restricted to one original hub-tip
graph or to one central boundary mask.

## 3. Complete physical shared-translation cover

In the actual `(m,t)` frame relative to R_0, K is
`[-ell,1-ell] x [0,1]`, while F is `(c,-s)`. This coordinate
calculation uses the true displacement F-R_0=(-1,0).

A positive shared segment between two unit squares forces their side
frames to agree. The four signed translations in the manuscript are
therefore exhaustive, including every possible lateral overlap offset.

Across K's maximum-t side, every C point has t coordinate at least one;
F's t coordinate is negative. Across K's minimum-m side, every C point
has m coordinate at most -ell<0; F's m coordinate is c>0. Neither
placement contains the actual HC point.

Across K's minimum-t side, C's t interval is [-1,0]. Because
`0<s<1`, the t coordinate -s of F is strictly inside that interval.
Consequently F cannot be a C vertex, independently of its m coordinate.
This excludes the actual free-HC feature. The argument does not change
the actual free normal into a side-owned normal and does not depend on
which shared-side application is used.

The remaining maximum-m placement has the complete form

    C=R_0+[1-ell,2-ell]m+[zeta,zeta+1]t,
    -1<zeta<1.

The strict zeta bounds are exactly positive physical overlap with K's
t interval [0,1]. Since `0<c<1<2-ell`, F can only use C's lower m
endpoint. This gives `ell=1-c`. If F used C's upper t endpoint, then
`zeta=-s-1<-1`, which is outside the positive-overlap domain. Hence it
uses the lower t endpoint, `zeta=-s`.

The complete surviving physical chart is therefore

    C=F+[0,1]m+[0,1]t,
    ell=1-c,
    w_CK=-m.

The contact normal w_CK is directed from C to K. No equation in this
physical cover fixes, averages or otherwise modifies the actual CK
mean. The strict angle and side-position premises have been retained
throughout; no omitted equality case is within the target domain.

## 4. Actual C force and circle-corner identification

At the derived minimum-m/minimum-t C vertex F, the unchanged actual
free HC normal has

    n.m>0, n.t>0.

Writing omega and gamma for the actual positive HC and CK magnitudes,
the true C force balance is

    kappa_C z_C=omega n-gamma w_CK
              =omega n+gamma m,
    kappa_C>0.

I checked the orientation: the HC normal outward from C is -n, and
the CK normal outward from C is -m. The displayed rearrangement is
therefore the original force equation with its correct signs.

Both projections of the actual circle vector z_C onto m and t are
strictly positive. For a square contained in a centered disk, a circle
corner with positive projection onto one inward own axis must use the
maximum endpoint in that axis. Otherwise adding that unit axis vector
gives another physical square vertex with strictly larger squared norm,
outside the containing circle. Applying the argument to both axes fixes
the genuine physical circle corner as

    z_C=F+m+t.

This is an identification of the actual loaded unique corner from the
unchanged force. It is not a choice of a convenient circle corner. No
torque or concurrence formula, side application or force magnitude at
K is used. The free cone remains entire, and the positive force weights
are unrestricted.

## 5. All four K corners and both full norm identities

### 5.1 The complete minimum-t pair

Each minimum-t K corner differs from R_0 by either -ell m or
(1-ell)m, a vector of norm strictly below one. The displayed bound is
valid even at G=1 and h=0:

    |R_0|^2<=1+h^2<1+1/3600<(61/60)^2.

Thus each of these corners has norm strictly below 121/60. The exact
comparison with the lower permitted containing radius is

    17/4-(121/60)^2=659/3600>0.

Neither minimum-t corner can carry any physical circle contact. This
argument needs no physical uniqueness or circle force at K.

### 5.2 The maximum-t corner with positive m offset

After the full physical reduction `ell=1-c`, this corner is

    z_+=R_0+c m+t.

I expanded the whole global-coordinate squared norms, before applying
the exact unit-frame equation. The resulting identity is

    |z_C|^2-|z_+|^2
      =-2h(c+s^2)+2Gs(1-c)+2c+(1-s)^2.

Every term on the right is nonnegative on the whole domain, and 2c is
strictly positive. There is no need to bound the angle away from either
axis. Both h=0 and G=1 are explicitly included.

### 5.3 The maximum-t corner with negative m offset

The other remaining corner is

    z_-=R_0-(1-c)m+t.

Its separately reconstructed full difference is

    |z_C|^2-|z_-|^2
      =-2h(1+2c-c^2)+2Gs(2-c)+1+4c-c^2-2s.

The first term is nonnegative, since h<=0 and
`1+2c-c^2>0`. Also `1+4c-c^2>1` for `0<c<1`.
For the complete remaining vertical expression,

    2Gs(2-c)-2s >= 2s(G-1)
                  >= -2(1-G)
                  > -31/60.

The first comparison subtracts exactly `2Gs(1-c)>=0`. The second
subtracts exactly `2(1-s)(1-G)>=0` after rearrangement, so it
retains the endpoint G=1. The last strict comparison follows from
G>89/120. Hence the whole second circle difference is strictly greater
than `1-31/60=29/60`.

This is a uniform reserve over the entire angle interval and the entire
physical overlap domain. Neither maximum-t circle possibility was
chosen in advance. Both actual candidate vertices have strictly smaller
norm than the actual C circle point, whose norm is exactly R.

### 5.4 Physical boundary contradiction

All four K vertices are strictly inside the disk of radius R. Squared
norm is convex, so every convex combination of those vertices also has
squared norm strictly below R squared. Since the square is their convex
hull, no physical point of K lies on the circle. This contradicts the
actual physical boundary premise on K, independently of its mask or
force degree.

## 6. Complete original-input reads and exact independent checks

Both direct original sources were read completely, rather than only
their cited lines:

| Complete present input | Exact SHA256 | Scope actually used |
| --- | --- | --- |
| `current_pr11/research/nine/PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Actual strict singleton-side position, free vertex normal convention, real positive C2 force and unchanged shared means |
| `current_pr11/research/nine/C7_FORCE_POLYGON.md` | `d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089` | Elementary physical circle geometry and own-coordinate comparisons |

The first source's actual physical normal strata and force equations
support precisely the contract used here. Its generic regularity
discussion is not used to choose a new normal in this target.

The second source is used only for elementary circle and own-coordinate
facts, which are also justified directly in Section 4 above. Its global
seven-body or all-boundary hypotheses, force-polygon conclusion and
degree-specific concurrence assertions are not transferred to this
three-square local theorem.

I separately recorded an exact arithmetic audit at

`recovery_2026_10_27/rooted_free_opposite_shared_audit.py`

with results at

`recovery_2026_10_27/rooted_free_opposite_shared_audit.json`.

It uses sparse rational polynomials and reduction by exactly
`c^2+s^2-1`. Eight coordinate or polynomial identities pass, including
both complete squared-norm differences and both comparison remainders.
The two norm identities were expanded from the global coordinates

    z_C=(h-1-c+s,G+s+c),
    z_+=(h-c^2+s,G+cs+c),
    z_-=(h+(1-c)c+s,G-(1-c)s+c).

Four independent rational values are

| Exact check | Value |
| --- | --- |
| `(61/60)^2-(1+1/3600)` | `1/30` |
| `17/4-(121/60)^2` | `659/3600` |
| `2(1-89/120)` | `31/60` |
| `1-31/60` | `29/60` |

All three target/input pins match the actual present file bytes. This
audit checks exact algebra and fixed values; it is not a parameter
search, an interval-box certificate or a substitute for the full
physical and force reconstruction recorded above.

## 7. Accepted scope and caller boundary

The entire local theorem passes independently, with no correction. It
excludes every actual free opposite-upper HC contact with physically
shared CK in the stated K-owned central chart. All CK means and their
endpoints, every actual free HC normal, both remaining possible K circle
corners, arbitrary K force degree and mask, h=0, and G=1 are retained.

No additional numerical certificate is required. The proof consists of
one exhaustive physical translation cover, the unchanged true C2 force,
two exact circle comparisons and a fixed lower-radius reserve.

An original caller must still establish the full chart, h<=0, the stated
height interval, actual free HC at F, positive shared CK, and unique
loaded true C2. In particular, this acceptance does not assert the same
conclusion for h>0, an arbitrary central normal, a side-owned HC, or a
boundary unit with an extra positive pair force. Those are different
premises, not omitted subcases of this source.

No original ledger, source manuscript, remote branch, Lean file or CI
configuration was changed during this review. No original gate closure
is inferred from this local result alone.
