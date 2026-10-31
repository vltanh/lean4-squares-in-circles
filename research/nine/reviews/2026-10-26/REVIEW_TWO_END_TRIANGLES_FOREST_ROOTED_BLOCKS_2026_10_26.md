# Independent full review: two end triangles joined through a bridge forest

Date: October 26, 2026.
Reviewer: rooted-blocks independent agent.

**Verdict: ACCEPT the complete interface, path and whole-family theorems.**
The full primary source reviewed is
`GLOBAL_CLOSURE_TWO_END_TRIANGLES_BRIDGE_FOREST_EXCLUSION.md`, SHA-256
`12102ca79ccde030a994bc1e96eea09d02f58b9ff0d8bbf9eec370dd49b5985e`.
I read its full strict-interface prerequisite
`OUTER_BRIDGED_TRIANGLE_CAP_EXCLUSION.md`, including its original threshold
inheritance, rather than substituting the older weaker interface bound.
The already independently reviewed off-origin and articulation-splitting
theorems were checked at the exact positive-degree/canonical-pose scope.

## 1. The strict interface is available with the complete far component

The actual end triangle has two true degree-two tips and a root of true
degree three with one exterior bridge. In the orientation from the far
component toward the root A, the accepted cap theorem proves rho<0 for
the original application rho e. Its source explicitly allows arbitrary
positive loads, cycles and degrees beyond the bridge and preserves every
physical mask, owner and mean endpoint.

The source's inheritance from `OUTER_BRIDGED_TRIANGLE_EXCLUSION.md` is
valid under rho>=0 alone: the proper tip concurrences, moment sign, three
distinct actual ports, root concurrence on the negative ray, and tilted
frame exclusion do not use rho>=max(d-1,0). Its added cap argument then
excludes the complete remaining aligned nonparallel domain without that
stronger threshold. The support-height comparison forces t>8; both actual
tip center projections exceed 29/20, and their cap diameter squared is
less than 178/225<1. The parallel branch puts both centers beyond 3/2 and
has the same contradiction. Thus the strict rho<0 theorem includes zero
applications and does not leave a small positive-radius gap.

Reversing e to f=-e and writing r=-rho>0 correctly gives the original
geometry

    A subset {f dot x<=r}, neighbor subset {f dot x>=r}, p=r f.

The neighbor has unique nearest point p and avoids zero. This is a
geometric conclusion from the unchanged radial bridge, not an equation
obtained by modifying an end-triangle force.

## 2. The full all-bridge neighbor is an original transmitter

If this neighbor U is an all-bridge nonleaf, the exact loaded-articulation
split and complete at-most-five-body exclusions make it truly unloaded
at the same canonical pose. The source keeps this inherited hypothesis;
it does not export a pose-dependent exclusion to an arbitrary equality
packing.

U has positive pair degree, is all-bridge and avoids zero. The complete
off-origin theorem therefore applies to precisely this original body. In
the same minimum-support stress its degree is two, its width is one,
and its actual applications are r f and (r+1)f with
0<r<=d-1<1/60. A is its unique incoming neighbor and contains zero. All
transverse sliders and endpoint means remain. The source correctly does
not infer radial-leaf geometry or circle load for its outgoing neighbor V.

V cannot be an unloaded all-bridge body: it lies entirely beyond radius
one, whereas such a positive-degree body must meet D_delta, delta<1/12.
It also cannot be a loaded all-bridge nonleaf, by the same exact split.
Thus V is a genuine leaf or belongs to a cyclic block. If V is another
intact bridged end-triangle root, its interface from U has positive
signed radius r+1, directly contradicting the full strict interface.

## 3. Complete path and graph-family joins

For a direct bridge between the two exact roots, reversing the bridge
changes rho to -rho. Both end triangles would require a strictly negative
value. The zero application is excluded as well.

For a longer positive path, its first internal all-bridge body is not a
leaf. The preceding complete theorem forces its actual degree to be two,
so the path must follow its unique outgoing edge. If the next vertex is
still internal it is an excluded all-bridge nonleaf; if it is the second
root its positive signed interface is excluded. This covers every path
length and every initially permitted off-path branch without dropping an
original force. The degree-two conclusion is proved by the previously
established common stress selection, not assumed after selecting a path.

In the stated whole family, the two disjoint cyclic blocks are triangles
and each has exactly one incident bridge. Their other four vertices are
therefore true degree-two tips, and the block tree supplies one connecting
path whose internal bodies lie outside all cyclic blocks. The path
theorem applies to the full graph, including every additional branch and
all nine physical squares. Contracting blocks only locates that graph
path; no force resultant is replaced by a physical square.

The exclusions are exactly scoped. They do not cover a triangle root
with two exterior bridges, shared-articulation triangles, or an additional
cyclic block on the connecting path. No larger coarse cell or sharp
radius/equality theorem is implied by this result alone.

No correction is required. No Lean compilation, CI, numerical sampling,
remote commit or change to a shared ledger was performed in this review.
