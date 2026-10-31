# An intact petal with a shallow root side excludes a loaded-endpoint four-block

Date: October 27, 2026.

**Status: complete proposed uniform geometric and terminal-block theorem,
pending full root and separate independent review.** No original gate,
coarse row or shared ledger is changed.

Keep all nine actual unit squares and the common compatible selected
certificate in `79/40<=R<=sqrt(1105)/16`. Put

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60, M_*=91/60.

Every actual contained center has norm less than M_*. A contained unit
beyond support height h requires h<=d. Distinct actual unit centers
are at least one apart. These are the exact center and halfwidth bounds
of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1.

Suppose an actual root H has an intact petal H,A,B, with A,B true
loaded degree two, and H has an actual own side at positive distance
sigma<=epsilon from O. H retains arbitrary additional forces and its
actual true degree. Suppose also that H is the root of either:

* a terminal C4 whose two H-neighbor private vertices are loaded and
  whose three private vertices have their true degree two; or
* a terminal hub-rooted diamond with its private hub of true degree
  three and its two private tips of true degree two.

All private positive edges of that displayed four-block stay inside
it. Its vertices are distinct from A,B. All original circle masks,
contact owners and actual mean endpoints remain.

**Theorem.** This entire configuration is impossible.

The new quantitative input below sharpens the former proper-port cap
from a far-face height at least one to height at least 59/60. The
resulting center-cap diameter still has the exact reserve 7/720.

## 1. A coupled support/center estimate at height 59/60

Let n=(c,s) be a unit vector with c>0; reflect the transverse coordinate
when needed, so only |s| matters. Suppose an actual neighbor center C
satisfies

    |C|<M_*,
    C.n>=h+1/2,
    A/c<=h<=d,
    A>=59/60.                                          (1)

Then

    C_x>43/30=:L.                                      (2)

First (1) gives `c>=A/d>59/61`. Set

    B_*=sqrt(M_*^2-L^2)=sqrt(885)/60.

If C_x<=L, the maximum of `c C_x+|s| |C_y|` in the radius-M_* disk
with first coordinate at most L occurs on the cap boundary at
`(L,B_*)`. Indeed the unrestricted circle support has first
coordinate `M_* c>L`, since

    (91/60)(59/61)-43/30=41/1220>0.

The elementary circle support on the truncated disk therefore gives

    C.n<=L c+B_*sqrt(1-c^2).                           (3)

We prove, on the entire closed interval `59/61<=c<=1`,

    L c+B_*sqrt(1-c^2)<59/(60c)+1/2.                  (4)

After multiplication by 60c, (4) is

    86c^2+sqrt(885)c sqrt(1-c^2)<59+30c.

The right-minus-first-term quantity `D=59+30c-86c^2` is positive:
this concave quadratic is at least 3 throughout [0,1]. Squaring
the remaining nonnegative terms reduces the claim exactly to

    P(c)=8281c^4-5160c^3-10133c^2+3540c+3481>0.        (5)

Here is a full exact interval proof, with no sampled sign test. Put
`x=1-c`, so `0<=x<=2/61`. Then

    Q(x)=P(1-x)
        =9-918x+24073x^2-27964x^3+8281x^4.

For `0<=x<=1/50`,

    Q(x)>=9-918x+(587843/25)x^2
         >=1386/34579>0.                              (6)

The first inequality uses `27964x<=27964/50` and drops the
nonnegative fourth-degree term; the second is the exact global
minimum of the displayed positive quadratic.

For `1/50<=x<=2/61`,

    Q''(x)=48146-167784x+99372x^2
           >=2601338/61>0,
    Q'(1/50)=363381/31250>0.

Thus Q is increasing on this remaining interval and stays positive
by (6). This proves (5), then (4). Equations (1), (3), (4) contradict

    C.n>=A/c+1/2>=59/(60c)+1/2.

The estimate (2) is proved, including the weak height A=59/60.

Two different actual neighbors satisfying (1) with the same fixed
x axis would consequently have centers in the same open cap

    L<x<M_*, |y|<sqrt(M_*^2-L^2).

Its squared rectangle diameter is

    (M_*-L)^2+4(M_*^2-L^2)=713/720<1.                 (7)

This contradicts the separation of their real open incircles. The
coupling between h and c in (1) is essential; independently rounding
both quantities would not give this reserve.

## 2. The actual intact petal forbids every other boundary contact on the shallow strip

The complete accepted theorem
INTACT_PETAL_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md gives H's actual
own coordinates and a reflection with

    H=[-sigma,1-sigma] times [-P,1-P],
    0<sigma<=epsilon<1/60,
    16/25<P<=11/15.                                    (8)

It also proves that no physical boundary square distinct from one
specified actual intact tip can meet the entire closed strip

    [-sigma,0] times [-P,1-P].                         (9)

This is a physical boundary statement, not a sign condition on a
circle multiplier or a force at H. All private four-block units are
distinct from the intact tips, so every four-block boundary neighbor
of H has its original root application strictly in x>0.

In particular any actual outward normal at such an application has
nonnegative x component. A negative component would expose H's
minimum own coordinate x=-sigma, inside the forbidden strip. Zero
components and genuine side means remain until the following full
root-line cover.

## 3. The unchanged private equations give the entire root concurrence cover

For a C4 with both H-neighbor private vertices loaded, the third
private vertex is either loaded or unloaded. The complete respective
private calculations are:

* ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md for all three
  private loads;
* ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md,
  Sections 2--5, for two opposite private loads.

Their root-independent scope is spelled out in
ROOTED_FOUR_BODY_TERMINAL_ORIGIN_UNIT_EXCLUSION.md, Sections 6--7.
The original root pair u,v has either a nonparallel intersection

    q=-t(u+v), t>0,                                   (10)

or both outward normals have the same direction. In the latter
alternative their actual ports have strictly opposite transverse
signs relative to that direction and are distinct. Opposite root
directions are excluded by the unchanged private equations. All
individual zero circle-weight endpoints and all true private means
remain in this cover.

For the hub-rooted diamond, its actual private K3 and two tip2
equations force all three private bodies loaded. The full local
coefficient proof in
ROOTED_HUB_DIAMOND_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md gives either
the nonparallel outer root intersection

    q=-alpha u-beta v, alpha,beta>0,                  (11)

or all three original H-to-diamond forces parallel with the same
sign. In that parallel case the two outer ports still have strict
opposite transverse signs, by the original K3 coefficient identity.
No HK chord force or circle atom is removed. These are precisely
the arbitrary-root inputs of Section 10 of the earlier uniform
four-block theorem.

Both cases thus give the same complete alternatives needed below.
No equation involving only u,v is imposed as H's full equilibrium.
In (11) the positive coefficients are an algebraic description of
the actual intersection, not new physical force multipliers.

## 4. The complete nonparallel alternative enters the coupled cap

Let u,v be the original two root-edge force vectors in the
nonparallel alternative, with (11), and let P_1,P_2 be their real
applications. By Section 2, both ports have positive x coordinate
and both outward normal x components are nonnegative. Since u,v
are independent, at least one x component is positive. Hence

    N=alpha u+beta v has N_x>0,
    q=-N has q_x<0.

A zero x component at either normal would put its entire contact
line at its actual positive port x coordinate, contrary to q_x<0.
Thus both normal x components are strictly positive. Both actual
ports lie on H's far own side

    x=A=1-sigma>59/60,

and both are proper, because the difference from q to either port
has positive x component along its positive-x normal.

For clarity, the support estimate used here does not assume H
avoids the origin or a resultant ray. Write the two unchanged unit
normals as n_i, the positive auxiliary coefficients of N as mu_i,
and the proper original ports as

    P_i=q+a_i n_i, a_i>0.

Their positive convex mean with weights proportional to mu_i/a_i is

    P_bar=q+N/W=(1/W-1)N,
    W=mu_1/a_1+mu_2/a_2.

Since its x coordinate is the actual A>0 and N_x>0, the coefficient
along N is positive. Both nonzero transverse normal components
cannot have the same sign: that would put both ports at the same
H vertex, making q that vertex, contrary to q_x<0. For opposite
components properness puts q_y between the two port heights; a zero
component retains the actual side-mean height of q_y.

Write P_i=(A,y_i). The auxiliary sum N is parallel to -q, so the
two fixed original lines have total geometric moment zero with
these positive coefficients:

    A N_y=sum_i mu_i y_i(n_i)_x.

Thus k=N_y/N_x is a positive weighted mean of y_i/A. The unchanged
normal slope is

    (n_i)_y/(n_i)_x=(y_i+N_y)/(A+N_x).

This is a positive weighted mean of y_i/A and k. For an upper
vertex with positive transverse normal component it is at most
y_i/A; for a lower vertex with negative component it is at least
y_i/A. The horizontal side-mean case has zero transverse component.
Multiplication by that correctly signed component gives in all cases

    h_H(n_i)=A(n_i)_x+y_i(n_i)_y>=A/(n_i)_x.           (12)

Every actual neighbor is contained and has halfwidth at least 1/2,
so its center C_i satisfies precisely (1) with this same fixed H
axis and A>59/60. Sections 1 and (7) put both real neighbor centers
less than one apart. This contradiction excludes the entire
nonparallel alternative, including all original owner types and
zero/private proper-length limits. No neighbor force equation or
modified physical stress was used in the cap.

## 5. The complete parallel alternative

In the remaining root alternative both actual outer normals equal
one unit direction e and their original ports strictly straddle its
axis. The ports are distinct, so e is an actual H side axis. The
only directions are the four axes of (8).

If e points toward the shallow side, both ports are in (9), already
forbidden. If it points toward the opposite side, its support height
is A=1-sigma>59/60. Both real neighbor centers then have projection
strictly greater than 89/60 in that one direction. Their common cap
rectangle has squared diameter strictly below

    (91/60-89/60)^2+4[(91/60)^2-(89/60)^2]
        =361/900<1.

If e is either transverse axis, strict port straddling requires one
actual port to have negative x coordinate. Section 2 requires both
to have positive x coordinate. This is impossible.

These exhaust all parallel normals. In the diamond case its third
parallel force stays in the actual system throughout; the argument
uses only the two real distinct loaded outer neighbors and the
already proved whole parallel alternative. The theorem follows.

## 6. Scope

The conclusion is uniform in all other actual forces at H, all
original circle masks and private two-corner weight endpoints. It
uses the intact petal at its true two loaded tips and the stated
terminal-four-block private degrees. A leaf added to a private tip
would invalidate that private-degree premise and is not covered.

The shallow side is an actual own support of H, not an invented
radial force or contact. The comparison in Sections 1 and 4 is a
geometric implication for fixed physical neighbors and their fixed
ports/normals. No new stress, selected normal, force split, virtual
unit, canonical motion, Lean compilation, CI or remote operation is
introduced, and no shared ledger is edited.
