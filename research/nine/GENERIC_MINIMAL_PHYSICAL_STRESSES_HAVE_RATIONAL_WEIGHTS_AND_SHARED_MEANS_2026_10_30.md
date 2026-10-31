# One generic selection controls every actual weight and shared-side mean

Date: October 30, 2026.

Base physical sources: repository tree
`4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed uniform structural theorem, awaiting separate
review.** This theorem supplies one exact algebraic interface for all
finite physical stress supports. It permits polynomial relations involving
the actual stress weights and shared-side means to be handled without
treating those unknowns as fixed geometric data. It does not assert that
any particular remaining topology is impossible, nor close the full
downstream G4.2.c audit or an original packing cell.

## 1. Fixed physical geometry and genuine normal parameters

Fix the entire minimizing physical packing: every center, frame, contact
intersection, actual circle corner, and every zero-stress completion
square. Fix a nonempty open product `Omega` of legitimate strict
vertex/vertex normal parameters, with one matched parameter at each
four-square junction. Any compatible nondense restrictions already
proved in the common-domain source are incorporated in `Omega`.

Let `K` be a countable subfield of the reals containing all these fixed
geometric coordinates, fixed constants used in the construction, and
the coefficients of the rational unit-circle charts. The field generated
by finitely or countably many specified real constants is countable.
Its real algebraic closure may also be included without changing that
fact. No force weight or variable shared-side mean is placed in `K`.

Parametrize each genuine normal interval by a half-angle parameter:

    n(t) = ((1-t^2)/(1+t^2))u + (2t/(1+t^2))v.                (1.1)

The frames `u,v` belong to the fixed geometry. At a four-square junction,
the same parameter gives the matched pair `au+bv` and `au-bv`, with
`a=(1-t^2)/(1+t^2)` and `b=2t/(1+t^2)`. There are `k` genuine parameters,
and `Omega` is a nonempty product of open intervals in `R^k`.

Choose

    t*=(t_1*,...,t_k*) in Omega

algebraically independent over `K`. The existence proof is elementary:
choose each coordinate transcendental over the countable field generated
by `K` and the preceding coordinates, inside its prescribed nonempty
open interval. If `k=0`, use the unique empty tuple and interpret the
following statements over `K` itself.

Write `F=K(t_1,...,t_k)` for the rational-function field. Evaluation at
`t*` is an injective field map from `F` to the reals: a nonzero polynomial
over `K` cannot vanish there, so every nonzero rational denominator is
legitimate and every nonzero rational function remains nonzero.

## 2. The full atom matrix contains no unknown application point

Use the original physical local feasible branch, before aggregation.
There is one atom at a physical singleton contact and two endpoint atoms
at a positive shared side. Each application point is therefore a fixed
physical point in `K^2`. All actual circle corners are also fixed.

For each body use two force coordinates and one **origin moment**
coordinate. Add one normalization coordinate. For a contact atom at
fixed point `p`, directed from body `i` to body `j` with unit normal `n`,
put the following entries in its column:

    body i: (n_x,n_y,det(p,n)),
    body j: (-n_x,-n_y,-det(p,n)),
    all other entries and normalization: zero.              (2.1)

For a circle atom at actual circle corner `z` of body `i`, its column is

    body i: (2z_x,2z_y,0),
    normalization: 1,
    all other entries: zero.                               (2.2)

The zero circle moment in (2.2) uses radiality of the actual circle
force. Force balance plus origin-moment balance is equivalent to force
balance plus the original moment about each body's center; subtracting
`det(c_i,total force)` changes one moment convention into the other.

Let `A(t)` be the resulting `(3n+1) by N` matrix and let

    b=(0,...,0,1).

Every matrix entry belongs to `F`: side-owned normals are fixed geometric
data and free singleton normals have the rational form (1.1), with all
matching substitutions already made. The exact normalized physical
certificate equations are simply

    A(t)w=b,    w>=0.                                       (2.3)

No shared-side mean appears in `A`. Such a mean is derived later from
the two actual endpoint weights.

The atom universe is finite. The crude bound

    N <= 4n + 2 binom(n,2) = n^2+3n

already suffices; it is 108 for nine squares. Only actual circle corners
and actual contacts need be included. No enumeration of the subsets in
this bound is needed for the theorem.

The sum of the `n` origin-moment rows is identically zero for every
column, including circle columns. Therefore

    rank_F A <= 3n.                                        (2.4)

This is the same rotational redundancy as the earlier physical-gradient
argument, expressed after changing to origin moments.

## 3. Choose the support once, before local arguments

At `t*`, the physical minimizer theorem and the matched-normal
uncrossing theorem provide at least one normalized physical certificate
whose positive body-pair graph has a physically compatible noncrossing
embedding: its local sector order is retained, all actual circle-access
spokes can be retained, and at most one opposite singleton pair is
positive at any four-square junction. Choose one with the smallest
number of positive **unaggregated scalar atoms** among certificates with
these physical noncrossing properties for the fixed geometry and normal
system. Abstract graph planarity alone is not the selection class.

Equivalently, one may first fix the surviving noncrossing atom universe
from a particular matched-normal uncrossing and minimize support inside
that universe. All conclusions below hold for either specified choice.

This is a selection at the initial construction stage. It does not
replace the means in an already analyzed certificate. Once selected,
its actual weights, means, degrees and physical masks are the data used
by every later theorem.

Let `I` be its positive atom support, and write `s=|I|` and `w_I*>0`.

**Lemma 3.1 (independent positive support).** The columns `A_I(t*)` are
linearly independent.

*Proof.* If `A_I(t*)h=0` with `h!=0`, reverse its sign if necessary so
some `h_j>0`. Set

    alpha=min_{j:h_j>0} w_j*/h_j,
    w'_I=w_I*-alpha h.

Every new weight is nonnegative and at least one becomes zero. The
equations and normalization are unchanged. Only old atom types remain,
so the positive body-pair graph is a subgraph of the same planar graph.
Every surviving atom is still a legitimate original physical contact or
circle atom. This gives a planar normalized physical certificate with
strictly fewer positive atoms, contrary to minimality. QED.

In particular `s<=3n` by (2.4). This recovers the 27-atom bound for the
selected nine-square certificate. An endpoint deletion in this proof
can change a shared-side aggregate mean; it is legitimate precisely
because the proof selects the initial certificate before any local
argument freezes that mean.

## 4. Every actual coefficient is a unique rational function

**Theorem 4.1 (rational minimal stress branch).** There is a unique vector

    w_I(t) in F^s

such that `A_I(t)w_I(t)=b` identically over `F`, and its value at `t*`
is exactly the selected actual vector `w_I*`.

*Proof.* Lemma 3.1 gives a set `R` of `s` rows for which the square
minor

    D(t)=det A_{R,I}(t)

is nonzero at `t*`. It is therefore a nonzero element of `F`. Define

    w_I(t)=A_{R,I}(t)^(-1)b_R.                              (4.1)

Cramer's rule places every entry in `F`. At `t*`, these chosen rows
have a unique solution; the actual vector `w_I*` solves them, so
`w_I(t*)=w_I*`.

For every other row, the residual `A_I(t)w_I(t)-b` is a rational function
over `K` whose evaluation at `t*` is zero. Injectivity of evaluation
forces each residual to be identically zero. Thus (4.1) solves the full
physical system over `F`. Column independence over `F` gives uniqueness.
QED.

All entries of `w_I` are nonzero rational functions, since their values
at `t*` are strictly positive. By continuity there is an open
neighborhood `U` of `t*` contained in `Omega` on which every denominator
in (4.1) remains nonzero and every coefficient remains positive.
Consequently the same physical geometry and same atom support carry a
positive planar normalized force-and-torque certificate for every `t`
in `U`. Its true positive body degrees and its positive circle-atom mask
are unchanged there. The physical circle mask was fixed from the start.

This local continuation varies admissible normal parameters and their
resulting weights; it does not move a square. It is a proof of the
algebraic branch, not a license to replace the actual certificate in a
later inequality. No continuation to an arbitrary endpoint of `Omega`
is asserted: positivity or an invertible minor may fail before then.

## 5. Every aggregate force and shared-side mean is rational too

For an actual shared segment with fixed distinct endpoints `p_-,p_+`,
write its atom weights as `w_-,w_+`, placing an identically zero weight
at an endpoint omitted from `I`. If its body pair is positive, then

    mu(t)=w_-(t)+w_+(t),
    P(t)=(w_-(t)p_-+w_+(t)p_+)/mu(t).                       (5.1)

The total magnitude and both coordinates of the actual mean are rational
functions in `F`. The denominator is positive at `t*` and throughout a
possibly smaller `U`. Formula (5.1) evaluates to the original actual
weighted mean, including both exact endpoint cases.

If exactly one endpoint atom is positive, that endpoint is the mean
identically on the branch. If both are positive, the mean is strictly
inside the complete physical segment throughout `U`. In particular,
there is no assertion that every positive shared segment must have an
interior mean. Physical sharedness and an endpoint-valued mean remain
different notions.

Singleton means are their fixed physical point. Total circle loads,
individual positive circle coefficients, resultants, and all other
finite sums or legitimate rational combinations of the original weights
are likewise elements of `F`.

## 6. Uniform identity-or-avoidance theorem, including unknown means

Let `H` be any polynomial with coefficients in `K` in finitely many
normal coordinates, actual atom weights, aggregate magnitudes, individual
circle weights, or coordinates of actual shared-side means. Substitute
the complete rational branch from Sections 4--5, with the actual matching
of normals. The result is one rational function

    h_I(t) in F.

**Theorem 6.1 (complete identity-or-avoidance).** Exactly one of the
following holds:

1. `h_I=0` in `F`. Then `H=0` on the entire rational support branch
   wherever its displayed denominators are defined, including `U`.
2. `h_I!=0` in `F`. Then `H!=0` at the single selected actual certificate
   `t*`.

*Proof.* This is precisely injectivity of evaluation `F -> R` at the
algebraically independent tuple. All substituted denominators are
legitimate by construction and positivity of the relevant aggregate
magnitudes at `t*`. QED.

The same dichotomy applies to a rational expression on its stated
nonzero-denominator domain. A denominator that becomes identically zero
on a support branch is a separate branch; it cannot be divided out.

The conclusion holds simultaneously for every such expression over `K`,
not merely a list chosen before the eventual support was known. In
particular it is legitimate to use algebraic genericity involving an
actual unknown mean **after eliminating it through its full atom
system**. It is illegitimate to add that mean to the fixed-geometry field
as though it were independently prescribed. These are different
operations, and only the first is used here.

The theorem does not assert that an arbitrary displayed `H` is nonzero
as a rational function. Relations forced by full equilibrium, geometry,
or the selected support are exact branch identities and survive. To
exclude a particular accidental relation, a caller must show its
substitution is not identically zero on each applicable support branch.
That is an exact algebraic question with no unknown application point
left in its coefficients.

## 7. A finite full-network rank test for support impossibility

For any physically prelisted atom subset `J`, define

    r_J=rank_F A_J,
    r_J^+=rank_F [A_J | b].

Every matrix minor is a rational function over `K`, so evaluation at
`t*` preserves both ranks. Therefore

    r_J^+ > r_J  =>  no normalized physical stress supported on J
                    exists at the common generic choice.     (7.1)

This is a complete obstruction, regardless of coefficient signs,
neighboring degrees, circle-weight splits, or shared-side means.
It uses the full physical equations of the candidate support rather
than discarding equations to manufacture a small local determinant.

When the columns of `A_J` are independent and `r_J^+=r_J=|J|`, Cramer's
rule gives the unique normalized vector. It is a positive physical
certificate at `t*` exactly when all of its entries there are positive;
its body graph has the required noncrossing property exactly when that
fixed support admits the stipulated physically compatible embedding,
including absence of both opposite pairs at every four-square junction.
These sign and physical embedding conditions
are not implied by rank consistency alone.

There are finitely many atom subsets and minors. Thus (7.1) and the
rational-branch conclusion may also be obtained for any specified finite
collection of expressions by one finite product of the relevant nonzero
minor and expression numerators, within `Omega`. Algebraic independence
gives the stronger single choice that is independent of which support
and which later polynomial expression occur.

## 8. Relation to local U3 and loaded-tip selectors

For an unloaded true-three-force body with three fixed singleton
applications, restrict the full matrix to that body's two force rows
and origin-moment row. Its three contact columns are exactly

    (n_x,n_y,det(p,n)).

Positive equilibrium forces their determinant to vanish. The existing
geometric nonidentity theorem for three distinct singleton ports is an
explicit proof that the proposed free-normal branch has a nonzero
determinant; Theorem 6.1 therefore excludes it in the same common
selection. Four-junction matching remains substituted literally.

If a contact has a positive shared segment, its two fixed endpoint
columns are both retained instead. The aggregate determinant may then
depend on its actual mean, and a genericity claim cannot freeze that
mean independently. Sections 4--6 give the correct complete replacement:
solve the full independent support over `F`, substitute the genuine mean
from (5.1), and test whether the resulting rational expression is an
identity. This covers loaded branches, chords and arbitrary neighboring
stars in exactly the same framework.

For a degree-two body with one physical circle corner, including
the possibility that its circle coefficient is zero, retain the actual
circle atom only if positive and retain all original contact endpoint
atoms. The corresponding local eliminants are again covered by the
same theorem. It does not silently delete the physical second corner
in a two-circle mask or replace a loaded equation by an unloaded one.

Thus the theorem supplies one properness interface for all current
local selectors and for larger full-network eliminations. It does not
claim to have rechecked the individual geometric nonidentity proofs,
their true-degree callers, or the remaining sharp packing inequalities.

## 9. Scope, direct inputs, and exact remaining task

The direct mathematical inputs are the already proved physical branch
and multiplier theorem, the matched-normal planarization theorem, and
the existence of the stated nonempty normal domain. The linear algebra
and generic evaluation argument above are proved in full here.

| Direct input | SHA-256 at the pinned tree |
| --- | --- |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |
| `GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md` | `557d3f5904a6ba09250a2167c6495cf3555d02536cf016a5ee09c0ccf84cfb20` |

All nine actual squares remain fixed. All original contact types,
physical circle masks, individual zero coefficients and complete
shared-segment endpoints remain represented. The final selected
certificate is used unchanged in later applications; the rational
continuation is not spliced into its equations.

The remaining G4.2.c work is to check the concrete operative conclusions
against this interface: any purported exclusion must supply actual
nonidentity (or the full rank obstruction), and every post-extraction
caller must establish its genuine physical and degree premises. The
existence of a common properness framework alone does not verify those
particular proofs. No original fine or coarse flag changes here.

No numerical pose search, angle mesh, new packing certificate, Lean
compilation, CI or repository metadata mutation was used.
