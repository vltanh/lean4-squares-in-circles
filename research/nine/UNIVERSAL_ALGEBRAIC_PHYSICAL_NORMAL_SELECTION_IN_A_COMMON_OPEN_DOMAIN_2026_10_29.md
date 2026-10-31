# One initial certificate avoids every proper algebraic normal obstruction

Date: October 29, 2026 UTC. Author: root continuation.

**Status: complete proposed universal selection theorem, frozen for full
independent review.** This is an existence theorem for the original
physical normal parameters. It replaces repeated finite determinant
choices by one simultaneous choice, including all genuine four-unit
matching relations. It never makes a selected side mean into fixed
physical data and never changes a normal after stress extraction.

The nonempty open domain is an explicit input to the abstract theorem.
The companion common-domain theorem constructs such a domain for the
four precisely catalogued R/S/J/B rules after the force-free physical
C7 exit. No claim that those are every nondense rule in every existing
manuscript is added here. A concrete transfer must still identify its
operative nondense requirements and prove the nonidentity of each
necessary algebraic relation that it uses.

## 1. Exact fixed geometry and genuine parameters

Fix the original nine actual unit squares and their containing circle.
Retain all physical pair intersections, physical circle masks, corners,
unit frames and shared-side endpoints. A pair with positive shared
length keeps its fixed actual own-axis normal and its whole endpoint
atom set. A side-owned singleton also keeps its fixed physical normal.

For each free vertex/vertex singleton, use the original open interval
of strict common normals. At an actual four-unit junction the opposite
free pairs have the original matched normal parameter; they are not
independent. Apart from that precise matching, parameters at different
physical points and the independent pairs at a smaller junction are
the genuine parameters of the accepted construction.

Let m be their total number. It may be zero. Let Omega be any nonempty
open subset of that genuine parameter space, defined before multiplier
extraction. It may include finitely many compatible nondense strict
angle restrictions. The abstract theorem does not create Omega by
calling a nonempty restriction dense.

Fix a countable subfield K of the real numbers containing all the
following actual physical constants:

* The circle origin and radius, all actual square corners and the
  components of every actual signed own axis.
* Every physical singleton point and every shared-side endpoint.
* All constants in the finitely or countably many proposed initial
  algebraic conditions, provided these constants are fixed before
  the normal choice and do not depend on it.

Such a K exists. A field generated over Q by finitely or countably many
specified real numbers is countable: its elements are values of finite
rational expressions in a countable alphabet. If square roots or other
real algebraic extensions are wanted, include its real algebraic closure
inside R. There are countably many polynomials over a countable field,
each has finitely many roots, and the resulting algebraic extension is
still countable. In particular every physical length, normalized own
axis and diagonal needed below can be included without changing this
argument. The physical constants need not themselves be algebraic over Q.

No future force magnitude, individual circle coefficient, aggregate side
mean or chosen free-normal value is adjoined to K after the choice. This
restriction is essential. A relation with a coefficient chosen from the
selected parameter itself is not a proper geometric obstruction of the
kind proved here.

## 2. Rational coordinates preserve the actual matching

At an independent free pair, choose the two signed outward own axes
u,v of one actual endpoint at its strict contact vertex. The actual
normal is

    n(t)=((1-t^2)u+2t v)/(1+t^2),    0<t<1.        (1)

This is exactly the open quadrant of strictly positive own components,
with t=tan(theta/2) for 0<theta<pi/2. Its intersection with the other
endpoint's strict cone restricts t to the corresponding nonempty open
interval. The direction map and its inverse are continuous there.
The coordinate t is real, not required to be rational; it is the
parametrization as a function of t that is rational.
The physical normals in (1) are unit vectors; no normalization variable
is omitted or regarded as a new independent parameter.

At a four-unit matched junction choose the genuine common own frame.
In the original notation its two free directions have coefficients

    a=(1-t^2)/(1+t^2), b=2t/(1+t^2), 0<t<1,
    a u+b v, a u-b v,                              (2)

up to the actual pair signs and orientations. Both use the same t.
Every component in (2) is rational over K in that one variable. Adjacent
shared-side axes remain fixed. We never replace (2) by two free angles.

Apply (1) or (2) to each genuine parameter. Thus Omega corresponds to a
nonempty open subset Omega_t of R^m. Every selected normal component is
a rational function over K of these m variables. The denominators
1+t_j^2 are everywhere strictly positive. A finite collection of
determinants and vector operations on the actual normals is therefore
rational over K in the genuine variables, including every matching.

Different physical singleton points have different junction parameters.
Two pairs at the same point may share a matched parameter; the theorem
uses the actual formulas (2), even if an algebraic obstruction thereby
becomes identically zero. It does not infer independence from graph
labels or from a larger fictitious parameter space.

## 3. Algebraic independence exists in every such open domain

**Lemma.** If K is a countable subfield of R and Omega_t is a nonempty
open subset of R^m, then Omega_t contains a tuple t such that

    P(t)!=0 for every nonzero P in K[X_1,...,X_m]. (3)

The tuples satisfying (3) are dense in Omega_t. For m=0, the single
empty tuple has this property, since a nonzero constant is nonzero.

Here is a complete argument for m>=1. First a nonzero real polynomial
cannot vanish on an open box. For one variable it has only finitely many
roots. Inductively, write a polynomial in its final variable with
polynomial coefficients in the preceding variables. If it vanishes on
an open product box, every coefficient vanishes on the preceding open
box by the one-variable fact; the induction hypothesis makes all of
them zero. This would make the original polynomial zero. Thus every
nonzero polynomial zero set is closed and has empty interior.

The nonzero polynomials over K form a countable set; enumerate them
P_1,P_2,... . Start in an arbitrary nonempty open box inside Omega_t.
It contains a nondegenerate compact box B_0 with rational endpoints.
Suppose B_(j-1) has been chosen. Its interior is nonempty and cannot
be contained in the zero set of P_j. Since that zero set is closed,
the interior contains a smaller nonempty open box avoiding it.
Choose inside that smaller box a nondegenerate compact rational box
B_j, of diameter at most 2^(-j). In particular

    B_j is contained in interior(B_(j-1)),
    P_j is nonzero at every point of B_j.          (4)

The B_j are nested nonempty compact sets and their diameters tend to
zero. Their intersection is one real tuple t. For every fixed j,
this tuple belongs to B_j, so (4) gives P_j(t)!=0. Also t belongs
to B_0, hence to Omega_t. Since the starting open box was arbitrary,
these tuples are dense in Omega_t, proving the lemma.

Condition (3) is algebraic independence over the fixed field K. No
numerical approximation to the tuple is needed for the hand existence
theorem. The construction uses no angle mesh or packing search.

The set of all tuples in (3) is generally not open. The statement is
nonemptiness and density, obtained inside the original open domain.
The proof does not incorrectly promise an open neighborhood satisfying
infinitely many exclusions. Any finite subcollection still has an open
dense common complement there.

## 4. The universal obstruction theorem

**Theorem.** Select a tuple from Section 3 and the actual matched normals
from Section 2. Every rational function F of those normal components
with coefficients in K has the following property: after substituting
the genuine parameter formulas, if F is not identically zero and its
denominator is not identically zero, then its value at the selected
tuple is defined and nonzero.

To prove this, write the substituted expression as P(t)/Q(t), with
P,Q in K[X_1,...,X_m] and Q not the zero polynomial. Nonidentity means
P is not the zero polynomial. Equation (3) gives P(t)!=0 and Q(t)!=0.
This proof applies simultaneously to every such expression, without
having to select again for a later finite application list.

An equivalent useful conclusion is:

    A necessary rational equality in the selected actual normals,
    with coefficients fixed by the original geometry, must be an
    identity on the genuine parameter space.     (5)

Here and throughout, a denominator that is identically zero is a
separate geometric branch. One may not divide by it, declare the
branch generic, or discard its positive stresses. The same applies
when a numerator vanishes identically. The theorem supplies no
contradiction in that case. A caller must keep that branch or exclude
it by a complete independent physical or full-force argument.

Nonidentity on an open parameter box suffices: a rational numerator
nonzero on such a box is a nonzero polynomial. Conversely a nonzero
polynomial cannot vanish throughout any other open box. It follows
that a nonidentity proved by varying a genuine free parameter with
the others fixed remains proper inside every nonempty open restriction
of Omega_t. That is the exact bridge from a local determinant proof
to simultaneous global parameter choice.

## 5. How to use a full-star elimination without fixing unknown data

Suppose a proposed positive star has original magnitudes lambda_i,
actual normals n_i, and actual singleton applications P_i or full
shared means M_i. Its complete force and torque equations may imply

    F(n_1,...,n_k; physical data)=0,               (6)

after eliminating the unknown lambda_i and M_i. If F is rational
over K and nonidentical on the genuine parameters, Section 4 excludes
that positive star in this one certificate.

The elimination must actually remove every future unknown from (6).
The theorem does not permit setting a shared mean to an endpoint,
regarding a force ratio as a geometric constant, or deleting a real
term from the full force equation. If a denominator used during the
elimination can vanish in the original positive star, its entire
zero branch has to be handled separately.

One common valid nonidentity proof holds the other normal parameters
at a hypothetical surviving star's values and varies one independent
free parameter. For example, a necessary det(n,W)=0 with W nonzero
at those other values is not an identity if n varies on a genuine
independent open interval and W does not depend on it. W may depend
rationally on those other variables; it need not be fixed numerically
before extraction. The *whole* expression after substitution has
coefficients in K. No value of W is illicitly adjoined to K later.

If the only potentially linked variable is the opposite pair at a
four-unit junction, a caller must either retain that matching in F or
prove that the two pairs cannot both survive the accepted uncrossing.
It cannot simply hold the linked variable fixed. If two contacts are
at distinct singleton points, their genuine parameters are independent
as in the original physical construction.

Finiteness of the original packing makes the set of physical graph,
owner, mask and feature assignments finite. They can all be covered
simultaneously. More strongly, the one tuple already avoids every
proper rational obstruction over K, including later applications that
use only these same fixed physical constants. This does not certify
their nonidentity or their geometric hypotheses for them.

## 6. Initial finite directions and later certificate operations

The standard nonradial and incident-diagonal exclusions are included.
At a nonzero singleton point P, det(P,n)=0 is a nonzero rational
condition on any genuine free interval. At P=O no nonradial condition
is imposed. An incident own diagonal has fixed components in K, and
parallelism to it is again a proper rational condition on a free
parameter, including a matched parameter in (2). Fixed side-owned
normals are not required to satisfy a free-normal avoidance.

After choosing the normals once, invoke the accepted physical branch
and multiplier construction at the minimizing packing. Its complete
force and torque equations retain all nine actual units and every
physical circle coefficient. The algebraic choice changes no physical
position, frame or contact set.

The accepted uncrossing uses exactly the matched rule (2). It retains
the directions of all surviving free singleton forces and adds only
genuine adjacent shared-side endpoint atoms. Subsequent conic thinning
deletes atoms; aggregation takes the full actual weighted mean of
shared endpoints, including either endpoint if the other coefficient
is zero. Every fixed side axis and endpoint was already physical data.

Every surviving subcollection of free parameters still obeys (3),
since a nonzero polynomial in a subset of the variables is a nonzero
polynomial in all of them. Consequently every proper obstruction
justified for a final positive star remains excluded. No selected
normal is rotated after its multipliers or true degree become known.

If the accepted pipeline asks for minimum positive original atom count
among its admissible normalized certificates, this additional class
is nonempty by the same multiplier construction. A nonempty set of
integer atom counts has a least attained value. No compactness of the
algebraically independent parameter set is claimed or needed for this
discrete minimization. Any separate prerequisite of the physical
multiplier or sparsity theorem remains its explicit input.

## 7. Concrete common-domain input and exact logical boundary

Use the domain from

    COMMON_PHYSICAL_NORMAL_OPEN_DOMAIN_AFTER_FORCE_FREE_BOUNDARY_CYCLE_EXIT_2026_10_29.md.

In its original radius window, either the nine actual units are already
excluded by the accepted force-free physical boundary-C7 capacity
theorem, or it constructs a nonempty open domain for all four of its
printed rules R/S/J/B. It checks every same-pair and matched-junction
interaction, including the closed small-support thresholds. Sections
2--6 here then select one point inside that domain satisfying every
proper algebraic avoidance over the fixed geometry field.

Thus a local caller whose only nondense rules are among that catalogue
has a proved simultaneous domain for *all* its properly justified
algebraic selectors. It need not add a separate compatibility assumption
for each determinant, provided its exact nonidentity and physical/full-
star application premises have been checked.

The historical C7 conclusions are used only at their actual C7 scopes,
where the force-free physical exit makes them vacuous on this remaining
branch. Literal old near-tangential intervals are not silently intersected
with near-bisector intervals. No old manuscript is edited to change its
claim or predicate.

An unlisted nondense restriction is not covered automatically. A
condition involving an uneliminated future force or side mean is not
covered automatically. An identically zero factor is not covered as
an exclusion. A genuinely nonalgebraic analytic condition would need
its own justified dense extension or a separate compatible construction.
The theorem does not claim that a whole current global caller inventory,
the entire G6 prerequisite chain, a remaining original family, the sharp
nine-square theorem, equality classification or Lean proof is closed.

## 8. Exact operative inputs and independent review requirement

| Complete input | SHA256 | Exact role |
| --- | --- | --- |
| COMMON_PHYSICAL_NORMAL_OPEN_DOMAIN_AFTER_FORCE_FREE_BOUNDARY_CYCLE_EXIT_2026_10_29.md | 395e5b86976faea66d26ed639e17acbe04c833758319286fa35b2283842c4a25 | Nonempty open domain for the precise R/S/J/B catalogue after the independent physical C7 exit; global inventory limit retained |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Accepted physical branch and full original force/torque certificate at a fixed initial normal assignment |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Genuine independent/matched parameter construction, retained surviving directions and actual shared endpoint atoms |

The algebraic-independence and nested-box arguments are proved in full
above. The rational parametrization identities can be checked exactly;
they require no floating-point value, packing certificate or angle mesh.
Full independent current-source and application review is required before
this result is adopted. No original flag, count or shared metadata is
changed by this proposed manuscript. No build, CI, workflow, remote write
or merge is used in its development.
