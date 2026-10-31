# A shared West roof and a D-owned hub interface force ownership of the exterior C port

Date: October 31, 2026 UTC.

**Status: complete hand feature exclusion under the already adopted
common algebraic selection.** In the physical-two West/strict chart
with the strict AV roof A-owned, DV physically shared, and AD owned
only by D, the original exterior DC normal cannot be free. Its
strict support at D therefore forces C to own that same original
normal at a genuine side-interior point. This removes all six
free-C placement alternatives in the older generated cover at once.
It does not exclude the remaining owned-C feature or close an
original row.

The proof uses the full original A3, D3 and V2 equations only. It
does not use a B, C or N force equation, endpoint degree, positive
load, circle-mask reduction or new normal choice.

## 1. The same original physical chart

Retain all actual physical units and the original common certificate.
Let V have two physical circle corners and write

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,1/2-j), 1/2<j<=1,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1.

The original strict A-to-V direction h is A-owned. The physical DV
intersection has positive length, and Q is its unchanged complete
mean, including either allowed endpoint. The original A-to-D normal
is owned only by D.

The actual shared DV frame is aligned with V. The physical triangle
own-axis inequalities exclude East, West and North for the D-only
AD axis, leaving exactly South. Its support at A is the actual
lower front corner. Thus the whole original geometry is

    A=P-[0,1]*h+[-ell,1-ell]*e,
    0<ell<1, y=1-ell>0,
    W=P-ell*e,
    D=[d-1,d] x [-1/2-ell*c,1/2-ell*c],
    K=P-h+y*e,
    L=(d-1,-1/2-ell*c).                         (1)

W is the unchanged AD application, K the actual AB application and
L the actual DC application. These geometric reductions, including
all directed-axis alternatives and shared-mean endpoints, are the
hand Sections 1--2 of
`PHYSICAL_TWO_SHARED_WEST_D_OWNED_FINITE_PLACEMENT_AND_CHANNEL_REDUCTION_2026_10_30.md`
and Section 6 of
`PHYSICAL_TWO_WEST_STRICT_HUB_OWNED_ROOF_COMPLETE_L135_JOIN_2026_10_30.md`.
No generated-cover conclusion from those sources is used here.

Let mu,nu,gamma>0 be the original magnitudes on AV,DV,AD. The
full unloaded-hub vector equations give

    F_AB=-mu*h+gamma*North,
    F_DC=-nu*East-gamma*North.                 (2)

Both own components of F_AB at A are strict: in the (h,e) frame
they are `-mu-gamma*s<0` and `gamma*c>0`. Likewise F_DC is
strictly Southwest in D's actual aligned frame. Thus (1) gives
the actual exposed vertices K,L for these original forces; no
new application is manufactured.

In particular DC cannot be physically shared and D cannot own its
normal. Its exhaustive original alternatives are C-owned genuine
singleton or a free genuine vertex/vertex singleton.

## 2. Eliminate every original force magnitude and the whole West mean

The full original A moment about P gives

    mu*y=gamma*(c-s).

Put F=c-s and B0=d*s+c/2. Positivity gives F>0 and B0>0.
The full D moment and the full V origin moment are respectively

    gamma*(1-ell*s)=nu*(1-j+ell*c),
    nu*(j-1/2)=mu*B0.                           (3)

All actual individual V circle forces are radial at their original
corners, hence have zero origin moment. No equality of their
coefficients is imposed in deriving the second equation of (3).

Add the two equations (3). The original shared mean cancels exactly:

    nu*(1/2+ell*c)=gamma*(1-ell*s)+mu*B0.

Now multiply by y and use the unchanged A moment. The result is

    y*(1/2+ell*c)*nu
       =[y*(1-ell*s)+F*B0]*gamma.              (4)

Every coefficient in (4) is determined by the fixed original
physical geometry. Neither j, any unknown pair magnitude, any
individual circle coefficient nor any other shared mean occurs in
these coefficients. In particular this is not a relation obtained
by adjoining an unknown extracted mean to the selection field.

## 3. A free DC normal would satisfy one proper fixed-geometry factor

Suppose DC were free and write its already chosen D-to-C unit normal
as g=(g_x,g_y). By the full D vector equation (2), some positive
original magnitude kappa_DC satisfies

    kappa_DC*g=(-nu,-gamma).

Eliminate kappa_DC,nu,gamma using (4). Necessarily

    A0*g_x-B0star*g_y=0,                       (5)

where the fixed physical coefficients are

    A0=y*(1/2+ell*c)>0,
    B0star=y*(1-ell*s)+F*B0>0.

Thus (5) is the restriction of a nonzero linear functional to the
actual open free-normal arc at L. It cannot vanish identically on
that arc: a nonzero linear functional has only two zeros on the
unit circle. Equivalently, substitute the actual rational
half-angle chart and clear the positive denominator 1+t^2; the
result is a nonzero polynomial of degree at most two over the
field of fixed physical data.

This remains true at an actual matched four-unit junction. The
matching convention supplies one open genuine parameter whose
normal still varies over an open unit-circle arc, possibly with
a fixed sign, quarter turn or interchange of the two components.
A nonzero linear functional remains nonidentically zero under
each such actual substitution. No independence from a second
normal at L is asserted or needed; (5) contains only this one
normal and fixed geometry. The geometric coefficients in (5)
remain fixed while the original normal parameter varies in its
pre-extraction open domain.

## 4. Apply the same adopted common selection, with no reselection

Sections 1 and 8, especially Lemma 8.1, of

`GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md`

choose all genuine free half-angle parameters in their actual
nonempty open domains algebraically independently over the
countable field of fixed physical data, after the real matching
substitutions. The source explicitly avoids every proper polynomial
factor over that field once its physical nonidentity is proved.
Its Section 10 preserves the same selected normals through
multiplier extraction, uncrossing, thinning and aggregation.

Equation (5) has exactly that interface. Section 2 eliminated all
unknown weights and the full shared mean; Section 3 proves
nonidentity even after the actual matching substitution. Therefore
the already chosen original certificate cannot satisfy (5).
This contradicts the full original equations in the proposed free
DC feature. No normal is varied or replaced after extraction.

The free alternative is impossible. Since the other alternatives
were exhausted in Section 1, C owns the unchanged DC direction at
its actual genuine relative-side-interior point L.

## 5. Scope and retained obligations

This is a whole-domain hand replacement for the free-C part of the
old shared-West finite-placement cover. It includes all six loaded
free-C vertex-placement labels, every physical C circle mask and
any individual zero circle coefficient, without examining a finite
pose list. In fact it needs no positive C load or equation at C,
B or N: it applies to both original L135 and L1345 when their
literal full A3/D3/V2 stars have the stated owner geometry, and to
higher exterior degrees under the same original full hub stars.

The owned-C shared-West feature, the D-owned genuine-West feature,
and the A-owned perpendicular West feature retain their separate
hand obligations. No whole graph/load row, coarse checkbox or
global sharp theorem is declared closed by this source.

All actual units, original normals, positive magnitudes, physical
circle corners, complete shared means and unused full-star equations
remain. The only discarded alternative is contradicted by the
proper factor (5) in the already adopted original common selection.
No external script, generated cover, pose search, proof-certificate
replay, Lean/Lake invocation or CI is used.
