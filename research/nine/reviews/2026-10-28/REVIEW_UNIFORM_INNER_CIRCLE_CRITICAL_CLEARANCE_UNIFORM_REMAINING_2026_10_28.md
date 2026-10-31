# Fresh independent review of the exact critical-clearance extension

Date: October 28, 2026 UTC. Reviewer: uniform_remaining continuation.

**Disposition: PASS for the entire extended manuscript at the current
frozen hash below, including Theorem D.** I reread the full manuscript
after the extension, checked its consistency with all earlier cases,
and independently checked the complete new equality classification and
the actual overlap of two adjacent equality units.

## 1. Current and historical pins

| Artifact | SHA256 | Role |
| --- | --- | --- |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 | Entire current extended mathematical source reviewed here |
| REVIEW_UNIFORM_INNER_CIRCLE_ARC_FAMILY_UNIFORM_REMAINING_2026_10_28.md | e7836f79f4fe821fabdd5917855954f2a4e687560528bc148434aa4660d5266d | Earlier full independent review, retained unchanged as the detailed review of the predecessor bytes |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Unchanged older-kernel reference, fully read in the earlier review and rechecked for the current join |

The earlier review correctly pins source
`a8e38f8fa30e50933a0548ddd61fc831531249bf68b1a918a67ad6a6b0bc95f0`.
It is not silently repinned and does not certify Theorem D. This fresh
review supplies the current source pin and explicitly supersedes that
old-source pin for current adoption. The earlier review remains valid
as historical evidence at its own exact bytes.

Root authored both the original source and its endpoint extension.
I did not contribute to either proof or change the source. Root described
the intended extension when requesting this review; I independently
rederived its equality and overlap arguments from the complete source.
No full original gate is credited by this review.

## 2. Recheck of the continuous family and retained conclusions

I reread Sections 1--10 with the new Theorem D in place. The open radius
interval `r_-<r<r_+` is still exactly the scope of the strict one-unit
angular-measure and connected-arc theorems. The new introduction does
not claim those strict one-unit conclusions at r=r_-.

The own-frame domain `a>=b>=1/2`, the farthest-corner constraint
`a^2+b^2<=Q`, and the nearest-point formula are complete. At a>r,
the fixed-q expression is strictly convex in a+b, and both fixed-q
endpoints give the printed bound by E_*. The actual circle intersection
is the stated interval, with both possible length constraints handled.

At a<=r and B>0, all four candidate interval differences remain
strictly greater than pi/4. The exact derivative factor is

    (A-B)*[(A+B-h)^2+(k^2-h^2)*(A+B+1)],

with every factor nonnegative on the full weak-clearance domain.
The tangent-side residue at a=r and B<=0 retains its one removed
tangency point. Its measure is strictly greater than pi/4, while
connectedness is correctly withheld at the weak clearance endpoint.

Under strict clearance the nearest-point supporting line and actual
halfwidth imply `|c|>r-1/2`; the unchanged farthest-corner estimate gives
`|c|<91/60<r+1/2`. Thus the radial center point remains in the actual
open incircle. No assertion that an entire intersection is centered
has been added.

All constant comparisons, exact rational reserves, inverse-function
branches, endpoint continuities, actual interior-measure sums, and
physical-clearance implications checked in the earlier detailed review
remain correct. The closed central-disk containment endpoint is still
handled by the weak-clearance measure theorem. The older radius-5/4
kernel and strict channel-height >3/10 join are unchanged at their
precise physical scopes.

The previous explicit single-square examples still demonstrate failure
of a strict pi/4 inequality at each radius endpoint. The new theorem
does not contradict either example: it concerns the coexistence of
eight units, with the complete equality geometry retained.

## 3. The one-unit measure at the exact lower radius

Set r=r_- and h=h_*. All earlier strict inequalities that depend only
on `6/5<r<4/3` or `r<r_+` remain strict. Only the last comparison

    E_0<=E_*=r_-^2/2<r^2/2

loses its final strict step. It becomes `E_0<=r^2/2`.

Thus the two strip widths are still strictly longer than pi/4; every
outer-face case, including the exact tangent-side residue, is still
strict. In the a>r case the inner-face width becomes at least pi/4.
The source consequently proves measure at least pi/4 for every
actual unit with clearance at least h_*. This is a direct complete
endpoint proof, not an appeal to an unjustified limit of strict
inequalities or connected intersections.

## 4. Complete equality classification

If the measure equals pi/4, the strict cases just reviewed force a>r,
and the strict strip candidate forces the inner-face width itself
to equal pi/4. This implies `E_0=E_*`.

The fixed-q endpoint b=1/2 has strict bound below E_*. The quadratic
in t=a+b is strictly convex; its fixed-q interval is nondegenerate,
since the present domain has q>r^2+1/4>1/2. Every interior t is
strictly below the larger endpoint value. Hence equality requires
the other endpoint a=b=w.

There `(w-1)^2=(v-1)^2`, with `3/4<w<=v`. The second algebraic
possibility w=2-v is less than 3/4, because v>29/20. It is therefore
excluded. The sole remaining value is w=v.

The actual equality square is consequently

    S_0=[A,v] times [A,v], A=v-1.

The earlier endpoint example proves the converse and gives its exact
open arc `(pi/8,3*pi/8)`. Undoing the own-axis normalization produces
only rigid rotations about O of S_0. An orientation-reversing choice
does not create another class: S_0 is invariant under exchange of its
two coordinates, and any such reflected image is a rotated image.

Its radial center direction is the midpoint of the exact arc. That
direction determines the rotated physical equality square uniquely.
The equality classification therefore includes every original
orientation and every weak clearance boundary, with no omitted frame
or equality endpoint.

## 5. Eight equality arcs force an impossible pair of actual squares

Eight actual open-interior circle intersections are disjoint measurable
sets. If each has measure at least pi/4, all eight must have equality.
They are therefore the single open arcs of the classified equality
squares. Their midpoint directions have successive gaps at least pi/4;
otherwise two of those actual open arcs overlap. The gaps sum to 2*pi,
so every gap equals pi/4. In particular a clockwise adjacent equality
pair is a common rotation of S_0 and `Rot(-pi/4)S_0`.

I checked the geometric overlap directly. With K=1+sqrt(2), put

    P=(K*A,A).

One has `A<K*A<v`. The second inequality is exactly
`v<1+1/sqrt(2)`, implied by v<3/2. Thus P is relative-interior
on S_0's bottom side. Rotating P back by pi/4 gives

    ((K-1)*A/sqrt(2),(K+1)*A/sqrt(2))=(A,K*A),

which is relative-interior on the other square's left side.

For the direction d=(2,1), its first-square second component is
positive, and its coordinate vector in the rotated square is

    Rot(pi/4)d=(1/sqrt(2),3/sqrt(2)).

Both relevant inward coordinates therefore increase strictly at P.
The other two coordinates start with the strict margins A<K*A<v.
Consequently P+eta*d lies in both actual open square interiors for
all sufficiently small eta>0. This is an actual two-dimensional
overlap, despite the disjoint open comparison-circle arcs. It
contradicts the original physical interior nonoverlap.

The endpoint argument therefore does not relabel weak arc inequalities
as strict. It uses the fully classified physical equality squares and
an explicit overlapping interior point. At most seven units can have
clearance at least h_*.

## 6. Exact critical consequences and final disposition

The same count among nine actual distinct bodies forces at least two
units with distance strictly less than h_*. If an actual unit contains
the entire closed disk D_(h_*), each of the other eight closed units
has distance at least h_* by physical nonoverlap, contradicting the
new endpoint count. Tangency of a side to the closed disk causes no
exception.

The boundary-distance estimate in the complete original radius window
is strictly larger than h_*<1/3. Both forced near units are therefore
physically circle-clear, and only then may their zero circle load be
inferred in a selected certificate.

The exact constant

    h_*=sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1)-1

is correctly derived from r_-. It is strictly smaller than 29/128,
as already proved by the exact constant comparison. The source makes
no claim that it is the best possible packing obstruction beyond
this proved endpoint argument.

**All statements of the extended manuscript, including Theorem D,
pass at the current frozen source hash in Section 1.** No source
correction is required. Its broad geometric consequences are complete;
its original graph/load applications, equality classification of the
nine-square sharp packing problem, remaining prerequisite audit, and
formal integration still require their separate full proofs.

No Lean compilation, CI, workflow, numerical pose certificate,
post-extraction normal change, source mutation, ledger edit, or remote
write was used in this review.
