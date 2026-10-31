# Full root review of the lower-house TD genuine-D family

Date: October 28, 2026 (UTC). Reviewer: root.

**Verdict: ACCEPT the entire original family, without correction.**
I read the complete current proof, independently derived its geometric
and force implications, and read the complete separate independent
review. The source is HOUSE_LOWER_TD_D_COMPLETE_EXCLUSION.md, SHA256
51d90e77cccd75ba987e9f26717c1019ad9e4fc3d9d9cbf4a034c2bcecfe6fcb.
The separate full review is
REVIEW_HOUSE_LOWER_TD_D_COMPLETE_TRIANGLE_BRIDGES_2026_10_28.md,
SHA256 2b6dea170d318ccf284d8cbfc0b2be0089b6e9256632b75b1a7689fe8176b694.

This acceptance closes exactly M6.B5L.HOUSE.LOWER.LTD.D. It does not
close the separate S companion or the parent five-body load cover.

## 1. Original graph, units and applications

The original positive block edges are AT, DT, AD, AB, BC, CD, and the
genuine pendant edge is BL. The T,D load row has true degrees
B3/A3/D3/T2/C2/L1. In particular the channel body C is really unloaded
degree two, the bypass A is still degree three, and D retains all three
positive contacts, including CD. Three further physical units remain.
These are the original lower-root labels, not an assumed symmetry with
a different house row.

Applying the complete actual B--C--D channel theorem with physical
bypass A gives the original unit direction n and actual application P,
with h=n.P=h_B(n), P_CD=P+n, and D entirely at n-height at least h+1.
The actual BA point Q is a maximum-m point of B and minimum-m point of
A for its original direction m. The actual A--D contact supplies
Z in A at n-height at least h+1. This extraction uses no shortened
equation at A, D or T and never centers the actual channel mean.

## 2. Independent derivation of the normal restriction

If n.m<0, a unit square at a minimum-m point Q has positive n-span
strictly less than one. At a vertex, write its two inward orthonormal
axes u,v. Their m-components are nonnegative. The negative dot product
forces a negative n-component on at least one of them; the remaining
positive component is strictly less than one. Equality to one would
force the other component to vanish and make n.m nonnegative. At a
side-interior point only the tangential interval can advance in n;
its length is at most one and its unit projection is strictly less
than one. Both side endpoints are already vertex cases.

Since n.Q<=h, this would prevent the actual A from reaching its real
point Z at height h+1. Hence n.m>=0, including equality. There is no
assumed A--C contact and no force or degree hypothesis at the bypass.

The full genuine-root equation is alpha e+mu m+nu n=0 with all three
magnitudes positive. Dotting with each nonleaf direction gives
e.n<0 and e.m<0. This uses precisely the actual degree-three root B;
it is not a claim for a higher-degree root with omitted forces.

## 3. Entire D-root chart and radius cover

The existing genuine-D selection convention gives, after rotation,
B=[-s,r] times [-b,a], e=East, r=R-sqrt(2), s=1-r,
a,b>0, a+b=1. The leaf vertex (r,0) is in the relative interior of
the real root side. Only the chart in Sections 1--2 of the fixed-point
source is used; its separate two-boundary-neighbor theorem is not.

The origin is in the interior of B, so h>0. The contained-unit support
bound for the actual far D gives h+1<=d, d=sqrt(R^2-1/4)-1.
Thus all d<=1 radii, including the critical endpoint, are already
excluded. On the surviving strict-high interval epsilon=d-1 satisfies
0<epsilon<1/60. The displayed exact radius comparisons give r>1/2
and s>1/4, without any special root pose.

For n=(xi,eta), the actual rectangular support obeys
h>=min(r,s)|xi|. Therefore |xi|<1/15. One reflection of the entire
configuration makes eta>0 and then eta>14/15. The full vertical
root equation forces m_y<0; the earlier strict e-dot signs give
xi<0 and m_x<0. Consequently the original actual applications are
P=(-s,a) and Q=(-s,-b). This accounts for the whole support cover:
axis normals and side means are impossible by these original force
signs, not discarded by a later normal choice.

## 4. The final contradiction concerns one actual unit

Both Q and Z belong to A. Their projection satisfies

    n.(Z-Q)>=h+1-n.Q=1+n.(P-Q)=1+eta>29/15>sqrt(2).

Their Euclidean distance is at most the diameter sqrt(2) of that same
actual unit A. This is the contradiction. No virtual replacement,
omitted far-body force, or circle-mask assumption is needed.

The same argument proves the explicitly stated local generalization:
a genuine degree-three D root, a true unloaded degree-two channel,
and a distinct physical unit bypass. The far body and bypass may
have arbitrary genuine degrees because none of their equations was
used. It does not apply to an arbitrary higher-degree root.

## 5. Literal input scopes and exact arithmetic

I checked the complete current direct input pins. The two channel and
support-span files were read in full again for this review; the other
operative sections were already fully read in the preceding root
audits and retained at these exact bytes.

| Input | SHA256 | Operative scope |
| --- | --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d | Original lower-root TD graph and load row |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 | Genuine D radial geometry and clear root |
| RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md | f3a3e4c9d82e3fa0b8fef7f7d385cf08fce88c39543bf97a74cb479d995037f9 | Sections 1--2, side-interior D-root chart only |
| UNIT_BYPASS_NORMAL_CHANNEL.md | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 | Complete original reserve-one channel |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac | Section 1 support-span statement |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb | Section 1, degree-free supporting height |

Independent exact rational expansions give:

| Difference | Value |
| --- | --- |
| (121/60)^2+1/4-1105/256 | 31/57600 |
| (25/12)^2-1105/256 | 55/2304 |
| 1-(1/15)^2-(14/15)^2 | 28/225 |
| (29/15)^2-2 | 391/225 |
| (3/2)^2-2 | 1/4 |
| 2-(4/3)^2 | 2/9 |

All are strict positive reserves. All nine units, every actual mean,
all true degrees, every physical circle mask and individual zero
weight remain. No numerical configuration, new selected normal,
canonical motion, compilation, CI or remote mutation is used.
The older global certificate audit remains a separate prerequisite;
this record does not assert a completed unrestricted n=9 theorem
or equality classification.
