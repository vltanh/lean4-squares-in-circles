# A free hub normal is unnecessary in the all-unique middle-triple house

**Status: complete compatible finite-selection implication for the all-unique physical mask;
root and separate independent full hand audits passed.** This is a whole physical-mask reduction,
not a completed middle-triple exclusion. Shared-side application means at
any of the five other edges remain arbitrary.

Work in the declared radius window and the selected physical certificate.
Label the exact positive house component by
\[
                      AT,\quad DT,\quad AD,\quad AB,\quad BC,\quad CD,
\tag{1}
\]
where precisely T,B,C are loaded and A,D are unloaded. Assume in this
source that **each of T,B,C has exactly one physical circle corner**.
This is stronger than having one active corner on a two-corner body;
the latter physical mask is not included here.

**Theorem.** The pre-certificate normal choices can be made compatibly
with the existing strict, nonradial and matched-junction convention so
that AD cannot be a positive free vertex/vertex edge in (1). In this
entire physical mask its surviving AD contact has an actual side-axis
owner. The shared-side alternative is separately excluded by
`HOUSE_MIDDLE_TRIPLE_SHARED_HUB_EXCLUSION.md`; a singleton owned by
only one hub is not excluded by the present theorem.

The proof uses translation balance and fixed circle-load ratios. It
never freezes a shared-side application point.

## 1. The isolated unique-corner roof has nonparallel pair forces

B and C are degree-two loaded bodies with a boundary neighbor, so their
two pair-force directions are nonparallel by the existing proper
concurrence theorem. We need the analogous statement at T, whose
neighbors A,D are unloaded and physically touch each other.

Suppose T's two pair forces were parallel. Their common axis is its
unique circle-corner direction. A contact pointing outward along that
direction would expose the circle corner itself, which cannot belong
to another contained square. Hence both forces point in the opposite
radial direction. Their common support is the opposite vertex p, and
T's torque makes p radial. The exact radial-D geometry gives
\[
                            p=(R-\sqrt2)e\ne0.
\tag{2}
\]
Both A and D therefore contain p. Since the radial direction is not
a side axis of this radial-D square, each of the intersections TA,TD
is the singleton p.

If p were a vertex of either neighbor, its corresponding point-only
vertex/vertex normal would be radial at the nonzero point (2), forbidden
by the retained nonradial choice. Thus p would have to be in the
relative interior of a side of **both** A and D. Both of those side
interiors have the same supporting line and their inward half-planes
point to the same side: both neighbors are on the inward radial side
of T's supporting plane. Their open interiors would overlap near p.
This contradicts nonoverlap.

Therefore T's two pair directions are nonparallel as well. This
argument allows the two roof applications to coincide before the
parallel alternative is excluded; it does not assume distinct triangle
junctions or a boundary neighbor at T.

## 2. The three circle-force ratios are fixed by the physical pose

Let z_T,z_B,z_C be the three unique physical circle corners. The
positive component's total force balance is
\[
                  \lambda_Tz_T+\lambda_Bz_B+\lambda_Cz_C=0,
                    \qquad\lambda_T,\lambda_B,\lambda_C>0.
\tag{3}
\]
The common factor2 can be absorbed into the loads. The directions of
z_B and z_C are distinct, and their scalar product is positive because
B,C physically touch. In particular these two vectors are linearly
independent. Consequently the kernel in (3) is one-dimensional.
After the normalization
\[
                         \lambda_T+\lambda_B+\lambda_C=1,
\tag{4}
\]
all three circle-force vectors are fixed by the physical pose alone.
They do not depend on any selected point normal or any application mean.
If (3) has no positive solution, that ordered physical house is already
impossible and need not be included in the selection list.

For later junction accounting, T is physically closed-disjoint from
both B and C. The loaded physical noncontact graph on {T,B,C} must be
connected, while BC is already a physical contact. A further TB or TC
contact would isolate one of B,C in that noncontact graph.

## 3. Translation balance fixes the required AD direction

Temporarily fix all selected normals except the free AD direction n.
At each of T,B,C, its two incident pair directions are nonparallel by
Section1. Its two positive pair magnitudes are therefore uniquely
specified by its two-dimensional translation equation and the fixed
circle vector from (3)--(4).

The shared BC edge receives one required magnitude from B and one from
C; if they disagree there is no house stress. If a required magnitude
is nonpositive there is likewise no stress with support (1). Otherwise
all five magnitudes on AT,DT,AB,BC,CD are now fixed independently of n.
This conclusion holds even if any or all of their physical intersections
are segments, because translation equations contain their normals and
magnitudes, but not their application means.

At the unloaded hub A, write f_AT and f_AB for the fixed outward pair
vectors just obtained. Its translation balance requires
\[
                            \gamma n=W:=-f_{AT}-f_{AB},
                              \qquad\gamma>0.
\tag{5}
\]
If W=0, (5) is impossible. If W is nonzero, it restricts n to at most
two directions through the exact necessary condition
\[
                                \det(n,W)=0.
\tag{6}
\]
The torque equations can only further restrict these possibilities.
No claim about a fixed application at any shared edge is used.

## 4. Independence at coincident and four-body junctions

The free AD parameter must be independent of the five other positive
normals used in Section3. The existing matched-junction construction
couples a point normal only to the **opposite disjoint pair at that
same four-square junction**.

An edge sharing A or D cannot be that opposite pair. Among the five
other positive edges in (1), the only disjoint pair is BC. If AD and
BC were the two opposite pairs at one junction, the planar uncrossing
construction would not leave both with positive weight. Thus this
cannot occur in the final selected positive house.

A roof contact AT or DT may coincide geometrically with the AD
application. It still shares a body with AD and hence is not the
matched opposite pair. If a fourth square is present, its matched
pair with T cannot be TB or TC, since those physical pairs are
closed-disjoint by Section2. It can only be a different, zero-weight
physical interface. Its matched parameter does not enter any of the
five positive translation equations used above.

These facts justify the independence of n even in every allowed
coincident triangle-junction case. They do not assume that all contact
applications occur at different points.

## 5. One simultaneous finite choice before multipliers

Before applying the physical multiplier theorem, prelist all ordered
physical five-tuples with (1), the physical one-corner masks of this
source, a free AD edge, and the fixed positive load ratios (3)--(4).
This is a finite list for the given packing.

On the open set where the three degree-two normal pairs are
nonparallel, their force solutions are rational analytic functions
of the other normal parameters. If W vanishes identically, (5)
already prevents a positive house throughout that parameter set.
Otherwise choose a parameter value where W is nonzero and vary the
independent AD direction within its nonempty strict interval. This
shows that (6), after clearing the nonzero two-by-two determinants,
is a nontrivial real-analytic equality on the permitted product of
normal intervals. Its zero set has empty interior. It can be avoided
simultaneously with all existing finite generic conditions, inside
any already required open strict/nonradial or near-axis domain.

Parallel normal-pair limits do not supply omitted positive houses:
Section1 excludes them for all three loaded bodies. Clearing those
determinants therefore loses no stress satisfying the theorem's
hypotheses.

After planar uncrossing, each surviving free AD normal retains the
chosen direction. Any newly added forces are along actual shared
sides. Thinning only removes atoms. A final all-unique positive house
would still satisfy the complete translation equations (3)--(6) and
was included in the finite list; it is consequently excluded from the
free-AD alternative. This proves the theorem.

## 6. Remaining scope

This source does not assert the same fixed-ratio argument when B or C
has two physical circle corners: an unknown corner split can change
its circle-force direction. It also does not replace a forced
side-axis AD normal by a generic direction. All radial physical masks
and the singleton one-owner hub geometry remain part of the complete
middle-triple problem.

All four additional squares remain in the physical packing throughout.
The normal choices are made before, not after, the stress certificate.
No numerical diagnosis, Lean compilation or CI is used.
