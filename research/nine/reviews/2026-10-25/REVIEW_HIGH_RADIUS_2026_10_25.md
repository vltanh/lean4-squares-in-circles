# Independent review of the high-radius triangle-tip pressure assembly

Date: October 25, 2026. Reviewed snapshot:
`4c8584155ba0b4f5a59375d7140e3a38f95eecfa`.

Reviewer: the independently delegated `high_radius_review` agent. This
report records this review, not an audit of every older manuscript in the
repository and not Lean verification.

## Verdict

**PASS at the exact stated scopes.** No mathematical gap was found in
`NEGATIVE_TRIANGLE_UPPER_LEFT_UNIFORM_HIGH_RADIUS.md` or in its use in
`HIGH_RADIUS_TRIANGLE_TIP_PRESSURE_AND_DIAMOND_FAMILIES.md`.
The complete high-radius tip-owned and free-owner sources were also
read and checked against the hypotheses needed by the new assembly.

The new uniform proof closes the full mathematical obligations of the
following two existing leaves, subject to the root's independent agreement
and normal roadmap bookkeeping:

- `M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.UUS.HIGH.AK_K_OWNED`
- `M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.UUU.HIGH.AK_K_OWNED`

No LOW leaf or full-radius parent follows. No coarse cell closes solely
from these two high-radius leaves. The original full prerequisite-chain
audit remains a distinct open obligation.

## 1. Independent reconstruction of the new physical argument

I reconstructed the actual support calculation rather than treating the
manuscript's HK owner table as a premise. With

    E = su+cv, d = sv-cu, r0 = s/E, delta0 = v/E,

the coordinates of n and j in the positively oriented (f,g) frame are
respectively (E,d) and (-d,E). The physical triangle lemma applies at H
because HA is H-owned, and at K because AK is K-owned. Thus an auxiliary
H-to-K separating side axis M obeys n.M >= 0 and g.M >= 0, without changing
the selected HK force or presuming its multiplier is positive.

For d>0 the allowed axes are n,j,f,g. The n and g cases give respectively
delta=delta0, r>=r0 and r=r0, delta>=delta0. The j support vertex has
strictly positive relative n-coordinate, so lies outside H. The f support
vertex has g-coordinate below h, so lies outside K. Hence delta>=delta0.
For d<0 only j and f remain. The j equality gives r=u+d*delta<u,
contradicting the independently derived negative-pressure restriction
r>u. The f equality gives delta=c+rd>=c+d. At d=0, r>u=s gives a
positive-length overlap of the g intervals, forcing delta=c by physical
nonoverlap. This includes every genuine shared mean and the zero endpoint
between the two sign regimes.

The pressure restriction r>u is valid on the entire original interval:
at r=u the coefficient norm is 5/2+u-u^2+2uv<=15/4; completing the two
squares gives the positive reserve 241/3200. Pressure decreases with r
because bu-av<0. At r=1 the coefficient norm is 5/2+2v, which gives the
later whole-offset pressure bound. These are comparisons of the original
pose, with no motion and no application-point substitution.

For rho=u/v<=5/9, I checked both complete signs of d. In the d>0 case,
delta0<1 implies 0<m<rho. The bound on A=a/b is monotone on the entire
m interval; it gives x>3/5 and L>1/2. This correctly identifies the
positive f endpoint as the farthest absolute f coordinate. The h<=-1/2
case retains its tie and has every K corner strictly inside q0. In the
h>-1/2 case, the remainder comparison is nonnegative on the full domain,
and J(rho) is strictly increasing up to rho=5/9. Its endpoint value is
strictly less than q0, so a-b*rho>1. The resulting corner-radius
contradiction covers either possible physical circle mask.

In the d<=0 case, the implications c>=v and s<=u follow from s/c<=u/v;
the rational bounds used for both coordinates of K are valid. The
estimate 841/225<q0 is strict, including d=0. Thus rho>5/9 throughout
the full original radius window. At q>=17/4, the pressure lower bound
is strictly greater than 7/8-9/sqrt(106)>0, contradicting the assumed
negative endpoint. The squared final comparison is 5/3392>0.

No K2 equation, H equilibrium, positive HK stress, return contact at B,
petal hypothesis, or additional physical-circle-corner assumption occurs
in this proof. The full upper-left geometry therefore has the stated
higher-degree and zero-stress-HK scope.

## 2. Whole-owner coverage and assembly

The original negative-endpoint chart and proper concurrence were checked
in Section 1 of `NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md` and
Lemma 2.1 of `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`. Their use precedes
the radial-middle specialization and needs only the true A2 equations
and K's physical circle contact. The unique radial-D coincidence is
explicitly removed using the physical boundary-neighbor hypothesis.

The complete source `NEGATIVE_UNIQUE_ENDPOINT_TIP_OWNED_HIGH_RADIUS.md`
retains every actual HA mean. Its lower, horizontal and upper outgoing
normal alternatives are exhaustive; the upper alternative treats both
coordinate orders. Its sharp support-height input applies to any
contained neighbor and requires no physical HK contact or K2 equation.

The complete source `NEGATIVE_UNIQUE_TRIANGLE_FREE_ENDPOINT_HIGH_RADIUS.md`
uses the fixed-tip selection only for two fixed applications. Its shared-AK
case retains the original side mean, obtains t>1/2 from physical circle
equality, and uses actual HK contact to force the H corner frame. The
coefficient comparison gives positive pressure at q=17/4 as well as
above it. The local portions of its fan-source dependency do not import
the fan's separate hub torque equation or opposite-endpoint premise.

For the H-owned HA branch, the left outgoing feature is covered by
`NEGATIVE_H_OWNED_LEFT_HIGH_RADIUS_EXCLUSION.md`, including its complete
small-coordinate source. The upper outgoing feature physically separates
H from K. The strict upper-left feature has two distinct fixed A
applications; `GENERAL_FIXED_TIP_NORMAL_SELECTION.md` removes its free
normal in the common pre-extraction certificate. The retained singleton
convention then puts T in the relative interior of a K side, precisely
the premise of the new uniform proof.

`RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md` supplies strict positive pressure
for each original radial-tip corner. A zero individual weight causes no
loss because the total is positive. Therefore Theorem A correctly claims
nonnegativity for a unique tip and strict positivity for a radial tip.

For Theorem B, `BOUNDARY_THREE_PATH_RESULTANT_CONE.md` concerns the actual
three physical boundary bodies and their original resultants. Its strict
cone coefficients do not require a middle-body equilibrium or degree-two
hypothesis. Hence the original sum has nonnegative H projection. The
external-pressure corollary uses only the legitimate sum of all component
equations; every internal force cancels there. In particular H5 and K3
are retained in the diamond/petal application, and H4/K2 is retained for
the physically chorded C4.

For Theorem C, the exact-degree-three unloaded-hub exclusion applies to
each nonroot diamond hub, while the degree-two triangle-tip transmission
obstruction loads its tips. The boundary-triangle obstruction forces H
to be circle-clear. The intact end-triangle theorem in
`BOWTIE_CELL_CLOSED.md` has arbitrary additional H forces. Its strict
pressure, the radial-leaf pressure and the selected D-leaf root-axis
identity are the actual external loads needed in the full force sum.
The integer constraint gives exactly eleven profiles for s=1 and three
for s=2, hence fourteen profiles total. It does not license additional
positive edges at designated tips or attachment at other roots.

## 3. Exact verification actually performed

The scalar signs and physical feature covers above were checked directly.
An independent standard-library rational-polynomial calculation reconstructed
18 algebraic identities, including both derivative formulas, the half-angle
and remainder identities, the pressure coefficient norms modulo
u^2+v^2=1, and the tip-owned cubic/completed-square identities. Seven
displayed exact reserves were independently reproduced:

| Comparison | Exact positive reserve |
| --- | --- |
| Pressure at r=u | 241/3200 |
| a>8/5 squared | 541/23680 |
| h<=-1/2 corner bound | 15809/78400 |
| q0-J(5/9) | 20973/84800 |
| d<=0 coordinate bound | 535591/4000000 |
| d<=0 corner bound | 469/2880 |
| Final high-radius squared comparison | 5/3392 |

This check did not run the author's SymPy script; SymPy is unavailable in
the current runtime. The independent calculation used exact Fraction
coefficients and polynomial expansion. No floating-point sample was used
to establish any of the reviewed implications. No Lean compilation or CI
was run, and this agent made no remote writes or roadmap edits.

## 4. Remaining mathematical direction

The high-radius proof is valid, but its local tip-sign conclusion cannot
be extended below the threshold from the same local geometry and A2
equations alone. `LOW_RADIUS_TRIANGLE_TIP_PRESSURE_OBSTRUCTION.md` gives an
exact three-body witness to those local hypotheses with negative tip
pressure in the original low-radius interval. It is not a nine-square
packing or a complete positive component. It identifies why a uniform
low-radius proof must use the true remaining K3/H5 equations, an actual
block-pressure comparison, or a complete physical packing obstruction.

The ABC physical-noncontact residue, both remaining alternating C6
families, other mixed cells, unrestricted lower bound and every original
equality packing remain outside this review's closure claim.
