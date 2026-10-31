# Independent review: the full parallel-HK return and physical HK fan

Date: October 25, 2026.

**Result: PASS at the precisely stated local scopes.** This review found no
mathematical gap in the complete saved parallel-HK side-return manuscript,
the complete physical/selected HK fan, or the direct complete near-return
prerequisite. The side and near arguments together exclude the entire
strict K-owned HK branch parallel to AK, at every original radius and for
both physical B masks. They do not close an entire upper-left diamond gate.

This was a separate reading and exact reconstruction by the `abc_remaining`
reviewer, not the source author's check and not the source's own SymPy
script. The local source snapshot was fetched at PR head
`4c8584155ba0b4f5a59375d7140e3a38f95eecfa`.

## Exact saved manuscripts reviewed

| File | SHA-256 of saved source |
|---|---|
| NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_SIDE_EXCLUSION.md | d7a1ba471a821b737bfbbe614036de8f2ef027c6280dd7f5cbf800264b64328a |
| NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_HK_CONTACT_FAN.md | 6e9d1974e848b37de7647dcb97d65b7533073238d40ebbe02b51ad07ae44ea54 |
| NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_NEAR_EXCLUSION.md | ab6eaf15d74b5e52da341a451140b7e9e7994ccfd79e2bf7874c25d5fe67671f |

## Complete geometric and domain review

The review checked the entire original A/K/H chart and the genuine K3
force and moment equations. The two original incoming K forces and their
distinct applications T,U occur in every needed moment. The near theorem's
proof of F>1 precedes its near-return specialization and therefore supplies
the side manuscript's stated whole-branch input. The full KB support fan
comes from the physical KHB triangle and the genuine K3 equation, without
a false K2 concurrence assertion.

For the side manuscript, the h<=0 and aligned-B exits retain every original
mean and do bound all four actual corners. The complete auxiliary HB side
axis cover was checked separately: the only surviving geometric alternatives
are H's j face and B's e face, and each gives the same bound

    y <= h+C-t*(Delta+S).

These auxiliary axes identify actual geometry; none replaces the selected
HB force. In the e-axis case, E-Delta>0 follows from y>=h, d>0 and the
original contact equation, so no zero-denominator endpoint is lost.

All four B corner estimates, including a negative vertical coordinate of
the fourth corner, were checked. The F>=4/3 and F>=5/4 exits use strict
inequalities on the complete displayed intervals. The smaller-F proof was
checked along the entire comparison path, not only at its endpoints:

* The derivative in tau has positive denominator and positive numerator
  throughout 0<=tau<=tau_actual<F.
* The fixed-F comparison in m stays in [1/3,61/100], with 0<Fm<1 and
  0<1-T0<=129/116. Positivity of 1-T0 along the path follows from
  monotonicity and its value at the actual endpoint.
* The two cases z>=1-T0 and z<1-T0 cover the original whole half-angle
  interval 0<z<1. The sign of the k derivative is retained on the complete
  enlarged k comparison interval.
* The boundary maps cover all actual F values. On I, A(w)<0<B(w),
  X_b>0 and 0<h_b<1; therefore every denominator and the tangent-quadratic
  argument has its asserted sign.
* The low-F fourth-corner comparison retains 0<t_b<=t<1, so its joint
  monotonicity in h,t is valid.

For the physical HK fan, the review checked all four auxiliary side axes,
all three signs of d, every contact endpoint, and the conversion to the
actual selected singleton/shared convention. The d=0 case has positive
g-overlap and the complete unchanged f-normal shared interval. Its opposite
horizontal ordering would require delta>=c+2 and is impossible. In the
free d>0 vertex junction, the actual normal sector is exactly the strict
sector between n and g; neither endpoint normal is substituted into it.
The r>u restriction and its uniform reserve were reconstructed directly.

## Independent exact arithmetic

SymPy was unavailable. The reviewer therefore implemented a separate
standard-library Fraction polynomial calculation from hand-derived
numerators and denominators. In particular it used

    T0 = [4m^2-F(1-m)^2(1+m^2)] /
         [(1-m^2)(F(1+m^2)+2m)].

It independently reconstructed all 70 exact Bernstein coefficients and
the full inverse power-polynomial identities, and reproduced every displayed
integer floor:

| Packet | Natural multidegree | Exact coefficients | Result |
|---|---|---:|---|
| D: dT0/dm-2 | (2,8) | 27 | All positive; floors and inverse identity pass |
| L: t_b+1/8 | 4 | 5 | All positive; floors and inverse identity pass |
| U: 1-t_b | 4 | 5 | All positive; floors and inverse identity pass |
| S: tangent-quadratic discriminant | 16 | 17 | All positive; floors and inverse identity pass |
| T: low-F t_b | 4 | 5 | All positive; floors and inverse identity pass |
| G: fourth-corner gap | 10 | 11 | All positive; floors and inverse identity pass |

The same independent calculation checked the tau derivative identity,
the derivative of T0 in F, the m-domain numerator identity, the rational
circle-boundary substitution and its explicit t_b formula, the comparison
derivative identity, the r=u pressure identity modulo u^2+v^2=1, and all
seven displayed rational endpoint reserves. The quartic corner-gap and
convex tangent-remainder formulas were also derived directly in the review.
There was no floating-point proof input or sampled geometric sign.

## Direct prerequisite scope and retained limitations

The full saved near-return source was read and its supporting-point lemma
was checked from the full vertex and side proof in
NEGATIVE_H_OWNED_LEFT_AXIS_SMALL_COORDINATE_EXCLUSION.md, Section 1.
The radius-free triangle normal lemma was read in full. The owned,
strict vertex/vertex, and shared-side convention was checked against
PHYSICAL_CONTACT_STRESS.md, Sections 2.1--2.3. The original endpoint-chart
proof and the precise proper-concurrence premise in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, were checked for the
true A2 application. No extra degree restriction at H or K was imported.

This is a complete audit of these three manuscripts and their direct local
input use. It is not an audit of every older prerequisite in the full PR.
The original true H5/K3, all nine physical squares, intact petal, three
extras, original shared means and individual zero circle weights remain.

The H-owned n HK singleton, the free n/g junction, and the K-owned f
family with its genuine d=0 shared endpoint remain open at the relevant
lower radii. ABC, the other mixed cells, unrestricted lower bound and
original equality are not closed here. No new ID or accepted checkbox is
changed by this report. No Lean compilation or CI was run.

## Additional independent review: no third square at the H-owned HK vertex

**PASS for the exact radius-free lemma in Section 4 of
LOW_DIAMOND_PARALLEL_ROOT_BRANCH_WORKING.md.** This additional check does
not review or accept that note's pending whole-block pressure assertion.

Suppose V is in the relative interior of a side of H with outward normal
n, and is a vertex of K whose two inward unit directions are f,g. Assume
f,g are perpendicular and n=E f+d g with E,d>0. The entire physical
H-owned HK row of the reviewed fan has exactly these hypotheses:
delta=delta0 and r>r0 place V strictly inside H's actual n side.

For a sufficiently small disk about V, the interior of H fills the open
n-negative half-disk, and the interior of K fills the open quadrant
between f and g. The quadrant's two boundary rays lie strictly inside
the n-positive half-plane because E,d>0. The complement of these two
open interior sectors has exactly two angular components, each of width
strictly less than pi/2. The common origin V does not supply any additional
angular directions.

If a third unit square B contained V, its interior directions arbitrarily
close to V would form one connected angular interval of width pi/2,
pi, or 2pi, according as V is a vertex, side-interior point, or interior
point of B. Interior-disjointness from H and K would force that interval
into one of the two smaller angular components, which is impossible.
Thus no third unit square contains V.

This excludes the whole near-vertex KB feature in the strict H-owned HK
row, including every B orientation and physical mask, any free/owned KB
normal, and all circle-weight endpoints. It uses no radius inequality or
force equation. It must not be transferred to the free n/g vertex junction
r=r0, where V is also a vertex of H; the side-interior hypothesis would
then be false. The other HK rows and the remaining KB features stay open.
