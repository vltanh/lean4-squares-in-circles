# Generic small-cut rules retain an entire unloaded branching module

Date: October 30, 2026.

Input tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed uniform theorem, awaiting separate review.**
This extends local degree-two and singleton degree-three selection
arguments to arbitrary subsets of unloaded bodies. Internal branches,
chords, cycles, contact means and all physical bodies are retained.
It gives necessary conditions for the boundary cut of the full subset;
it does not replace its members by a fictitious transmitter square.

## 1. Full physical cut equations

Fix the common selected physical force-and-torque certificate with its
physically compatible noncrossing body-graph embedding produced by
matched-normal uncrossing. In particular at most one of the two opposite
singleton pairs is positive at every four-square junction; all local
sector orders and physical circle-access spokes are retained. Any
subsequent minimum-support choice is made in this physical noncrossing
class, or in one already noncrossing atom universe. Abstract graph
planarity alone is not the hypothesis.
Let `U` be any nonempty subset of bodies whose **total circle coefficient
is zero at every member**. A physically circle-touching body with zero
coefficient is allowed. No assertion of physical circle clearance is
made from this assumption.

Every positive body-pair contact crossing from `U` to its complement is
a cut edge. After aggregating its actual endpoint atoms, write its
outward unit normal from `U` as `n_e`, its positive magnitude as `mu_e`,
and its original physical application as `p_e`.

Summing all original body forces and origin moments over `U` cancels
every internal contact in action/reaction pairs, at its unchanged shared
application. Thus

    sum_cut mu_e n_e = 0,
    sum_cut mu_e det(p_e,n_e) = 0.                            (1.1)

All internal equations remain true. Cancellation is a derived identity,
not a deletion of the internal physical units or their forces. These
two equations hold for any size, shape, connectedness or internal graph
of `U`.

If a cut consists of three physical singleton contacts, put

    W(p,n)=(n_x,n_y,det(p,n)).

Its exact necessary equation is

    mu_0 W(p_0,n_0)+mu_1 W(p_1,n_1)+mu_2 W(p_2,n_2)=0.        (1.2)

Here all `p_i` are fixed physical points. A positive-length shared segment
with an endpoint-valued mean is **not** a physical singleton.

## 2. One common generic normal choice

Use the original legitimate normal parameter system: one open strict
parameter at each free vertex/vertex singleton and one matched parameter
for the two opposite pairs at each four-square junction. Incorporate all
already proved compatible nondense restrictions first.

The following additional avoidances are finite and proper:

1. A free singleton normal is not parallel to the normal of any distinct
   fixed-normal physical contact.
2. Two free normals with independent parameters are not parallel.
3. For every prelisted triple of physical singleton cut contacts with
   independent free parameters, avoid its full wrench determinant when
   the geometric classification in Section 4 proves it nonidentically
   zero.

The first two conditions are nonzero sine/cosine determinants on every
open interval or product. The matched opposite normals at a four-square
junction obey

    det(au+bv,au-bv)=-2ab != 0,

so they are already nonparallel for `a,b>0`. More generally, after
planar uncrossing at most one opposite singleton pair at that junction
is positive. Therefore the free parameters of any final positive
singleton-contact triple are independent: two supported edges cannot
be the two members of one matched pair.

Prelist the physical subsets and cuts before extraction. There are
finitely many bodies, physical contacts and triples. Tuples containing
both matched opposite pairs may be omitted from the determinant
prelist because they cannot be a cut of the final positive planar
certificate. No omission is made merely because of an unknown future
load or degree: all remaining physically possible tuples are prelisted.

The nonzero factors in this theorem are polynomials after rational
half-angle substitution and positive-denominator clearing. They may
therefore be imposed simultaneously in the existing nonempty open
normal domain, or obtained automatically from the common
algebraically-independent choice over fixed physical geometry.
Uncrossing retains surviving free singleton normals, and thinning
only deletes atoms. The conditions survive both operations.

## 3. Complete two-port theorem, including shared contacts

**Theorem 3.1.** If the positive cut of `U` has exactly two body-pair
edges, both contacts have geometrically fixed normals. Neither is a
free point-only vertex/vertex contact.

*Proof.* The full cut force equation is

    mu_1 n_1 + mu_2 n_2 = 0,    mu_1,mu_2>0.

Since the normals are unit vectors, `mu_1=mu_2` and `n_2=-n_1`. If one
contact were free, Section 2's pairwise nonparallel condition would
contradict this equality. This covers every possible pairing of a free
contact with a fixed contact, an independent free contact, or its
matched opposite-junction partner. QED.

The second equation in (1.1) also gives

    det(p_1-p_2,n_1)=0.                                     (3.1)

Thus the **original** two aggregate applications lie on one common
force line. Their side means remain unchanged. This is a module-level
force-line statement, not a conclusion that `U` is one square or that
its width is one or square-root two.

The contacts in this theorem may be physical shared segments with any
original mean, because the argument uses only their geometrically fixed
normal and then their actual full torque equation. No fixed-mean premise
is needed.

A one-edge nonempty cut is immediately impossible by force balance.
A component with positive contacts and no cut or circle load is
impossible by the usual center-dot work identity.

## 4. Complete three-singleton determinant classification

Suppose the cut has exactly three positive body-pair contacts, each
physically a singleton. Designate a free contact at the fixed point
`p_0`, and translate the coordinate origin of this calculation to `p_0`.
This changes no physical pose or force. Write

    w_0=(n_0x,n_0y,0),
    w_i=(n_ix,n_iy,det(p_i-p_0,n_i)),    i=1,2.               (4.1)

The allowed free vectors at `p_0` span the two-dimensional plane

    E_0={(x,y,0):x,y in R}.

### Both other contacts have fixed normals

If `n_1,n_2` are parallel, the force equation forces `n_0` to be parallel
as well, contradicting Section 2. Hence any surviving positive cut has
nonparallel `n_1,n_2`; its two vectors `w_1,w_2` are independent.

As `n_0` varies over its open strict interval, the determinant
`det(w_0,w_1,w_2)` vanishes identically exactly when

    span(w_1,w_2)=E_0.

Because the normals are nonparallel, this is exactly

    det(p_1-p_0,n_1)=det(p_2-p_0,n_2)=0.                     (4.2)

Thus either both actual fixed normal lines pass through `p_0`, or the
determinant is a nonzero linear sine/cosine factor and is excluded by
the common choice. The common-point line case is retained, not
misclassified as a proper avoidance.

### Exactly one other contact is free

Let `n_1` be free at fixed point `p_1`, and let `n_2` be fixed. Their
parameters are independent in every final positive triple.

If `p_1!=p_0`, choose an allowed `n_1` avoiding both the line through
`p_0,p_1` and the two directions parallel to `n_2`. Only finitely many
directions are forbidden. Then `w_1,w_2` are independent and
`w_1` does not lie in `E_0`, so their plane is not `E_0`. Varying `n_0`
makes the determinant nonzero. Therefore the determinant is a proper
factor on the full product, and this entire case is excluded.

If `p_1=p_0`, the vectors for `n_0,n_1` range independently in `E_0`.
Their determinant with `w_2` is nonidentically zero unless `w_2` belongs
to `E_0`, namely unless the fixed normal line at `p_2` passes through
`p_0`. This is the exact retained case.

### Both other contacts are free

If at least one of `p_1,p_2` differs from `p_0`, fix an allowed value
of the other free normal and choose the normal at a different point
to be neither radial from `p_0` nor parallel to that fixed value.
The same preceding argument gives a nonzero determinant. Thus the
determinant is nonidentically zero unless

    p_0=p_1=p_2.                                           (4.3)

If all three points agree, all columns lie in one wrench plane and
the determinant is identically zero. It must be handled geometrically,
as in Section 5; no genericity assertion removes it by fiat.

These cases exhaust every number of free normals in a cut containing
the designated free contact. The proof uses only fixed actual singleton
points and genuine independent normal parameters. No force coefficient
or unknown shared mean occurs in a determinant coefficient.

## 5. An unloaded cut cannot have one common actual application

**Lemma 5.1 (common-point cut impossibility).** Suppose `U` is entirely
unloaded, its positive cut is nonempty, and all cut forces act at one
actual point `p`. This is impossible, for any number of cut edges and
with arbitrary internal branching or cycles.

*Proof.* Dot each body's original force balance with `c_i-p` and sum
over `i in U`. Every internal oriented contact contributes

    mu_e n_e . (c_i-c_j)
       = -mu_e(h_i(n_e)+h_j(n_e)) < 0.

For a cut edge from body `i`, the common application `p` is an actual
support point of that body in direction `n_e`, so its contribution is

    mu_e n_e . (c_i-p) = -mu_e h_i(n_e) < 0.

All loads of bodies in `U` are zero. The summed original equations
therefore say that a strictly negative number is zero, because the cut
is nonempty. Contradiction. QED.

The lemma requires equality of the **actual** applications, not merely
concurrence of their force lines at some other point. It does not infer
that a point on an extension of a side is a physical application.

## 6. The uniform three-port conclusion

**Theorem 6.1 (arbitrary-module singleton cut rule).** Let an entirely
unloaded subset `U` have exactly three positive cut edges, all three
physical intersections being singletons. If one cut contact is free
at `p`, then:

1. Every other free cut contact has that same actual application `p`.
2. The actual normal line of every fixed cut contact passes through `p`.
3. At least one cut contact has a geometrically fixed normal and an
   application different from `p`.

*Proof.* The complete classification in Section 4 supplies the first
two conclusions: every alternative is excluded by a proved proper
determinant or by the force-parallel contradiction. If every remaining
contact also applied at `p`, Lemma 5.1 would exclude the cut. Thus one
contact has a different application. By the first conclusion it must
have a fixed normal. QED.

In particular:

    No entirely unloaded module has a three-edge cut
    consisting wholly of free vertex/vertex contacts.        (6.1)

This is a whole-module statement, regardless of how many bodies,
branches, loaded external neighbors, or internal cycles occur. The
external neighboring bodies may have arbitrary actual degrees, loads
and circle masks. Internal contact means remain complete.

If the three singleton applications are pairwise distinct, at most one
cut normal can be free. If exactly one is free, the two fixed exit
force lines must concur at its actual application. Unlike the stronger
single-square U3 theorem, this source does not exclude that concurrence
for an arbitrary multi-square module. Such an exclusion would require
a separate geometric argument for the entire module.

## 7. Boundary and applications

Theorems 3.1 and 6.1 are restrictions on a physical **cut**, not on the
degrees of its individual bodies. They apply without suppressing a
loaded or branching vertex and without treating a union of squares as
a unit square. They can be combined with an independent module work or
terminal-separation inequality while retaining the same full equations.

For a singleton subset `U`, Theorem 3.1 recovers the no-free-contact
consequence for an unloaded degree-two transmitter. For a larger
two-port subset it supplies that conclusion at its entire external cut.
Theorem 6.1 similarly extends the generic three-force argument to an
arbitrary unloaded branching module, retaining the exact concurrence
exception instead of importing the single-square support classification.

### An explicit family inside several open biconnected parents

Let `H` be any two-connected graph on `h>=3` actual unloaded bodies.
Let an exterior retained cycle have `k>=3` actual bodies, with arbitrary
individual loads and additional physical contacts. Connect three
distinct vertices of `H` to three distinct vertices of that cycle by
exactly three positive body-pair edges. Suppose these are the entire
positive cut of the unloaded set `V(H)`. The surrounding graph remains
unchanged in the application; the theorem uses no positive-degree
restriction at the exterior vertices.

Theorem 6.1 excludes at once the whole feature in which all three
connecting contacts are free physical vertex/vertex singletons.
Neither the internal structure of `H` nor its original internal means
enter the proof. With two free contacts, the exact necessary domain is
the common-application/concurrent-fixed-exit domain in Theorem 6.1.
With one free contact, both fixed exit lines must pass through its
actual application. These are precise remaining features, not closures.

The abstract graph consisting of `H`, the exterior cycle, and the
three joins is two-connected: removing a vertex from either constituent
leaves that constituent connected and retains at least two joins to
the other constituent. It is therefore a genuine single-block caller,
not an artificial isolated-cycle substitution. For example:

| Unloaded module `H` | Exterior size `k` | Total bodies | Original bare-block parents containing this feature |
| --- | ---: | ---: | --- |
| Triangle | 3, 4, 5, 6 | 6, 7, 8, 9 | `C1.6.b0`, `C1.7.b0`, `C1.8.b0`, `C1.9.b0` |
| Diamond | 3, 4, 5 | 7, 8, 9 | `C1.7.b0`, `C1.8.b0`, `C1.9.b0` |
| `K2,3` | 3, 4 | 8, 9 | `C1.8.b0`, `C1.9.b0` |

This table is a graph-family application of the complete cut theorem,
not a claim that every abstract listed graph has a physical square
realization. If a listed original graph/load/contact feature is realized
in the common certificate, its entire unloaded module satisfies the
theorem. The `K2,3` row explicitly includes a branching module with no
simple cycle of length five; the argument never relies on finding a
long rim inside that module. All `9-h-k` actual completion squares
remain when `h+k<9`.

No exact fine row is checked by this table. The other contact features,
load allocations and graph shapes in each listed coarse parent remain
separate. It demonstrates transfer across body counts at the same
full-cut hypothesis rather than promoting a feature exclusion to an
entire parent.

The three-port theorem does **not** cover a physically shared cut
segment by treating its variable mean as a fixed singleton. The rational
full-atom framework in
`GENERIC_MINIMAL_PHYSICAL_STRESSES_HAVE_RATIONAL_WEIGHTS_AND_SHARED_MEANS_2026_10_30.md`
can represent those remaining means correctly, but their determinants
need separate symbolic or geometric analysis. The two-port theorem and
Lemma 5.1 remain valid with shared contacts at their actual means.

The direct structural input is the physical certificate and its
matched-normal planarization. Genericity uses the existing nonempty
common normal domain; every new bad factor has its complete nonidentity
proof above. The full force-and-torque equations and all actual bodies
remain. No original fine or coarse cell is declared closed by this
manuscript alone.

No numerical search, angle mesh, Lean compilation, CI or metadata change
was used in this proof.
