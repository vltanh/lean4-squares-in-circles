# Independent full review: negative bridges with a full cyclic-root load

Date: October 27, 2026.

Reviewer: rooted_blocks, independently of author triangle_bridges.

**Verdict: ACCEPTED for all three complete corrected sources below.**

| Source | Reviewed SHA-256 |
| --- | --- |
| `FOUR_BODY_BLOCK_NEGATIVE_BRIDGE_WITH_FULL_ROOT_LOAD_EXCLUSION.md` | `f2b3b0fc1c41fced68a7f2196ae6261e87b7b2f03d5bfda171da157c5c7887fe` |
| `FOUR_BODY_BLOCK_DIRECT_LEAF_AND_SHORT_ARM_FORK_CLOSED.md` | `8cd72d77b3f4f8554d88d39060e198bca7bacbd932ac5627eedbae7cecbb66c5` |
| `FOUR_BODY_BLOCK_SINGLE_FOUR_EDGE_TREE_CLOSED.md` | `b4e2bea5638619ff8fbe61dc40c9022e5aed10c83c7c69a2d2612728bf085807` |

This is a fresh complete audit of the corrected theorem and both full
callers. It does not accept the earlier draft's incorrect circle-force
sign or its invalid positive-resultant-point construction. Those claims
were identified during independent review and have been removed.

I read all three final sources, reread the complete relevant adjacent,
opposite and three-load C4 local proofs, the complete terminal hub-diamond
proof and geometric proper-port cap, and checked their exact scope under
the new original bridge data. I also checked the full articulation and
off-origin-transmitter premises used by the two callers.

## 1. The correct full root balance and its limited immediate consequence

The private circle sum M is exactly the sum of the original block forces
pointing out of H, by the unchanged private body equations. Its total
origin moment at H is zero. With the outward-circle convention of the
physical certificate, H's complete equation is

    M+beta n+G_H=0,       M=-G_H-beta n.

The actual negative radial bridge gives H subset {n.x<=rho}, rho<0,
so H avoids O. If G_H=0, M=-beta n is nonzero and H avoids the whole
nonpositive M ray. The corrected source makes no inference about n.M
or a positive-M point from this equation when G_H is nonzero.

Every further use of that forbidden ray is established at its actual
load mask. In particular the root circle force is retained in the one
remaining loaded-root mask, rather than erased by a presumed clearance.

## 2. The complete C4 load-mask cover

For the real order H--A--C--B--H, A,C,B retain true degree two.
The zero, three singleton, three double and full private masks are all
covered, including the indicated reflection A<->B.

For zero private loads, the three true transmitter widths propagate on
one common line and force two actual H applications at distance at least
three. A sole adjacent load forces an actual normal gap of at least two
along the two-transmitter alternate path, contradicting the real direct
root contact. Neither argument uses any equation at H beyond its actual
support and diameter.

For the sole opposite load, the two parallel channels have width one
and the common endpoint-owned axis, by the complete two-channel theorem.
The loaded C parallel-star theorem concerns its original positive weighted
application mean. Subtracting the real unit width puts the corresponding
weighted mean (r_C-1)e in H; neither individual transverse mean is reset.
The longitudinal interval of H is [r_C-2,r_C-1] and its transverse unit
interval contains zero. Thus every H point has squared norm less than
13/4, below the original radius. This proves physical clearance and
G_H=0. The actual inward segment contains (r_C-2)e on the forbidden ray.

For the adjacent double mask, the old local proof's Sections 1--4 use
only the private equations, actual unit bypass, root support cover and
the original radius bound R>2. Its Section 4 proves G_H=0 without its
old external middle triangle. I checked this distinction explicitly:
H may remain physically boundary with zero actual circle force. The
corrected source now calls this a zero-load proof, not physical clearance.
After this proved vanishing, the real negative bridge supplies exactly
the ray required by the old final local argument. The parallel actual
face straddling or the nonparallel proper-port weighted mean gives its
contradiction. The same-nine R>2 dependency and all zero weights remain.

## 3. The full loaded opposite mask

If the actual G_H is nonzero, H,A,B are physical boundary units and H
touches both A and B. The degree-free acute-contact result therefore
gives G_H.F_A>0 and G_H.F_B>0. Their sum is G_H.M>0.
Every point x in H also satisfies G_H.x>0, since each positive-weight
circle corner z satisfies z.x>=R^2-R sqrt(2)>0. Consequently H avoids
every nonpositive M-ray point. This proof retains the entire original
G_H and every physical circle corner, including zero-weight corners.

I reread `ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md`
to check that the imported local proof does not secretly use H-clearance
again. After the forbidden ray is supplied, its Sections 2--5 use only
the genuine private A2/B2 equations and actual channel geometry. The
parallel loaded-endpoint exclusion uses the other endpoint's boundary
status, not a false boundary-neighbor premise. Conditional nonparallel
proper concurrence, the nonzero channel height, independent circle rays,
the root cap and the nearest-point argument all retain their hypotheses
with G_H present. The private origin-moment sum still supplies the real
root-pair moment equation. Thus the same negative concurrence and complete
one-improper cover hold in this exact loaded-root setting.

## 4. The replacement winding correction is complete

In the remaining case q=-tM with t>0 and

    P_i=q+b_i n_i,       b_1 b_2<0,
    M=mu_1 n_1+mu_2 n_2,       mu_i>0.

The two displayed determinant identities have the same strict sign:

    det(M,P_1)=-b_1 mu_2 det(n_1,n_2),
    det(M,P_2)= b_2 mu_1 det(n_1,n_2).

Hence conv(q,P_1,P_2) meets the M line only at q, a nonzero point.
It avoids O. For any actual D in H, conv(D,P_1,P_2) lies in H and
also avoids O. The oriented difference of their two zero-winding
boundaries is exactly D--P_1--q--P_2--D. Every edge avoids O.
This establishes the required zero correction without any premise
about where D lies relative to the M line and without any positive-M
point in H. The correction remains valid for zero private proper lengths,
degenerate auxiliary triangles and the original shared-side endpoints.

The unchanged private concurrence loop has winding one. The homotopies
at the boundary units stay in strict positive-circle half-planes. At the
unloaded channel, its nonzero transverse height and the triangle spanned
by its center and original endpoints avoid O even if O is on that unit's
boundary: positive center coefficients are interior points, whereas the
remaining edge has nonzero height. This is exactly the closed-origin
argument required when U contains O only closed.

The resulting actual ring has an O-neighborhood of winding one. Some
interior points of the original U belong to that neighborhood, and its
connected interior avoids every occupied ring strand. The complete
physical four-ring equality then gives the aligned cross. Its opposite
boundary pair forces R^2=5/2, outside the original window. No positive
edge or physical square has been removed to form this ring argument.

The full three-private-load mask has actual root clearance from the
forbidden physical boundary four-cycle. Its full boundary cone and
three genuine private concurrences retain the middle load. The same
new correction applies to its one-improper case, and its three-boundary
ring capacity excludes the original U. This completes all eight masks.

## 5. Diamond and K4 coverage

For a hub-rooted diamond, the real K3 and both true degree-two tips are
loaded by their existing full local obstructions. A boundary H would
make a physical boundary triangle, so H is genuinely clear. The bridge
then supplies the forbidden ray used in the terminal diamond argument.

I checked that proof's complete coefficient cover: it uses the full K3
equation and actual HK chord, retains parallel/coincident alternatives,
and never assigns K a degree-two star or splits its circle force into
two independent triangle stresses. Its private path has the actual short
angular lift. Its correction already permits an arbitrary D in H.
The zero-winding and strict-interior alternatives respectively give the
three-boundary outer-ring contradiction or the exact geometric two-port
cap. The closed-origin U limit is valid because all ring strands avoid O.

For a tip-rooted diamond, the three private bodies are loaded and already
form a forbidden physical boundary triangle. The selected positive K4
theorem retains arbitrary original external edges. These are all actual
four-body biconnected profiles. The uniform result therefore has the
whole stated profile and root-orbit scope, with the strict rho<0 premise
unchanged.

## 6. The full direct-leaf/short-arm fork caller

The original graph H--U, U--L, U--V, V--M keeps U3, V2 and both genuine
leaves. Articulation minimality gives zero U load; the complete off-origin
all-bridge theorem would reduce its true degree to two if it avoided O.
Thus O belongs to U. The three branch force/normalization vectors cannot
all be collinear, because the exact same-atom branch reweighting argument
would remove a positive branch. This is a valid use of the selected
minimum support, with every remaining original mean preserved.

The real V transmitter has actual parent port (r_M-w)e. U contains O,
so its support there is nonnegative. The complete S/D and width cover
therefore leaves only M S, w=1, d>=1 and the actual epsilon e port.
The entire U-side moment sum makes the original H--U application radial.
Its U-side support lambda lies in [0,d].

At high radius, a direct D leaf makes U origin-interior. For a direct S
leaf, an own-axis root would exclude O. If the tilted root had O on its
boundary, its exact chart would be [0,1] times [-t,1-t], with
t=sqrt(2epsilon+epsilon^2). All vertices have norm greater than epsilon,
and none of its four own support heights equals epsilon, since both
t and 1-t exceed epsilon. This contradicts the real epsilon e support,
including all owners and side means. Hence U is origin-interior and
lambda>0 throughout the high case.

At critical radius, the arm port is O. An origin side-interior U makes
its direct S direction and both other forces collinear, impossible.
For U=[0,1]u+[0,1]v, the full three-force equation gives the arm's
v component negative and the parent's positive. A negative parent
u component cannot give a radial port; a positive one gives support
sqrt(2)>d. Thus the parent is exactly v at port v, lambda=1. This
includes a physical boundary H and does not declare it clear.

The true H bridge consequently has rho=-lambda<0 in every survivor.
The private block degrees and sole external-edge premise are exact.
The corrected uniform theorem closes every type, mask and radius of
this whole original attachment, with the ninth physical square retained.

## 7. Exhaustive single-four-edge-tree assembly

Every outside nonleaf is genuinely unloaded by the complete all-bridge
splitting result, and the branch bound limits its degree to three. The
rooted tree on four outside vertices consequently has exactly the listed
three shapes: a path, a stem to two leaves, or the first fork with one
leaf and one short arm. The child-size count is exhaustive and never
deletes an original positive edge.

Every outside nonleaf meets D_epsilon by the full off-origin theorem or
closed origin containment. In the path, the two downstream true widths
give U support at most d-2<-epsilon, contradicting that near-origin point.
The stem row has the separate accepted full no-unloaded-transmitter
exit. Its stated direct critical check also works: the true fork port
is O, the original U width is forced to one by sharp support at d=1,
and the H--U port is -e. The uniform negative-bridge theorem applies
with U containing O closed and H's full load retained. The remaining
row is exactly the whole fork caller reviewed above.

Thus all three sources are accepted in full. The final assembly closes
the whole single-outside-tree forest class of C1.4.b4; it does not by
itself claim the other forest classes or the entire coarse cell closed.
No Lean compilation, CI, numerical sampling, remote action or shared-
metadata edit is used in this review.
