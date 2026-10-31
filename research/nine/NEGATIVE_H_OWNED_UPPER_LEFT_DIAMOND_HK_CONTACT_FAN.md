# The complete physical HK fan after an upper-left K-owned contact

**Status: complete hand reduction; author, root and separate independent
full saved-source/direct-prerequisite review passed on October 25, 2026.
Section 4.1 adds a separately reviewed radius-free near-vertex exclusion.
See REVIEW_PARALLEL_HK_2026_10_25.md. No ID or checkbox is added.**

This is a continuation of the existing upper-left diamond obligation, with
all nine original squares, true H5/K3/A2/B2, the intact HXY petal, all original
forces and application means, every physical B mask and every completion
square retained. The argument itself uses only the indicated physical
triangle HAK and the actual negative endpoint frame; it never deletes a force.

Pinned source checkpoint: `b55e508c1dd5aaf020d8f833af394316df6450f5`.
The negative endpoint chart is Section 1 of
NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md. The geometric triangle
normal theorem is UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. The selected
singleton/shared convention is PHYSICAL_CONTACT_STRESS.md, Sections 2.1--2.3.

## 1. Original coordinates

In the actual ordered A frame, let
\[
 z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,\quad
 q\ge q_0=6241/1600,\quad P=(a-1,b-1),\quad T=(a-1,b),
\]
\[
 n=(u,v),\quad j=Jn=(-v,u),\quad 0<u\le v,\quad u^2+v^2=1,
\]
\[
 H=P+[-1,0]n+[-(1-r),r]j,\quad 0<r<1,\quad c_H\cdot z_A<0.
\tag{1}
\]
The actual H-to-A normal is n, owned by H. AK is a strict K-owned
upper-left singleton. Put
\[
 g=(-c,s),\quad f=(s,c),\quad c,s>0,\quad c^2+s^2=1,
\]
\[
 K=T+[0,1]g+[-\delta,1-\delta]f,\quad 0<\delta<1.
\tag{2}
\]
The offset \(\delta\) is geometric, not the A concurrence parameter.

Use positively oriented coordinates (f,g), with
\[
 L=T\cdot f,\quad h=T\cdot g,\quad
 E=su+cv>0,\quad d=sv-cu,\quad E^2+d^2=1.
\tag{3}
\]
Then
\[
 n=(E,d),\quad j=(-d,E),\quad P=(L-c,h-s),
\quad K=[L-\delta,L+1-\delta]\times[h,h+1].
\tag{4}
\]
Define the two actual contact-transition values
\[
 r_0=s/E,\qquad
 \delta_0=v/E=c+sd/E.
\tag{5}
\]
These are comparison coordinates derived from the original packing, not
substituted positions. Note that \(\delta_0>0\).

## 2. A table-free negative-pressure restriction

**Lemma.** In (1), if \(r\le u\), then
\[
                    c_H\cdot z_A\ge241/3200>0.
\tag{6}
\]
Consequently every actual negative endpoint has \(r>u\).

**Proof.** Since \(j\cdot z_A=bu-av<0\), the expression
\[
 c_H\cdot z_A=q-a-b-\tfrac12(au+bv)
                         +(r-\tfrac12)(bu-av)
\]
decreases with r. At \(r=u\) it equals \(q-aA-bB\), where
\[
 A=1+(u-v)/2+uv,\qquad
 B=1+(u+v)/2-u^2.
\]
The exact identity using \(u^2+v^2=1\) is
\[
 A^2+B^2=\tfrac52+u-u^2+2uv\le\tfrac{15}{4},
\tag{7}
\]
because \(u-u^2\le1/4\) and \(2uv\le1\).
Completing two squares gives
\[
 q-aA-bB
 =\tfrac12\{q-A^2-B^2+(a-A)^2+(b-B)^2\}
 \ge\tfrac12(q-15/4)\ge241/3200.
\]
This proves (6) on the full domain, without a numerical or polynomial
coefficient certificate. No equation at K, H or B is used. QED.

## 3. Exhaustive auxiliary side-axis cover

Because H and K touch with disjoint interiors, the separating-axis
theorem gives an auxiliary H-to-K separating direction M along a side
axis of H or K, with equal supports. This is used only to identify their
actual contact geometry; it is NOT substituted for the selected HK force.

The physical triangle HAK imposes both
\[
                         n\cdot M\ge0,\qquad g\cdot M\ge0.
\tag{8}
\]
The first uses the owned HA direction n at H. The second uses the owned
KA direction -g at K and its direction -M toward H.

Among H's four side normals, (8) permits j and, only when \(d\ge0\), n.
Among K's four side axes, it permits f and, only when \(d\ge0\), g.
Thus this four-axis list is exhaustive. The following support calculations
include all contact endpoints and both signs of d.

### 3.1. The n axis when d>0

The minimum-n point of K is its actual near vertex
\[
                         V=(L-\delta,h).
\]
Equality with H's front n side gives
\[
                         \delta=\delta_0.
\]
Moreover \(V-P=r_0j\), so the point lies on the actual H side only if
\(r\ge r_0\). It is in that side's strict relative interior if \(r>r_0\).
At \(r=r_0\), V is also H's actual front/top vertex.

### 3.2. The g axis when d>0

H's unique maximum-g point is its actual front/top vertex
\(U=P+rj\). Equality with K's minimum-g side gives
\[
                         r=r_0.
\]
Its f-coordinate is \(L-\delta_0\). Inclusion in K's actual side is
equivalent to \(\delta\ge\delta_0\); the other endpoint bound is automatic
from \(0<\delta<1\) and \(\delta_0>0\). The point is in the strict side
interior if \(\delta>\delta_0\).

### 3.3. The j axis

For \(d>0\), the minimum-j point of K is
\((L+1-\delta,h)\). Its n-projection relative to P is
\[
 E(c+1-\delta)+ds=v+E(1-\delta)>0.
\]
It cannot be a point of H, all of whose relative n-projections are
nonpositive. Thus this entire auxiliary-axis alternative is impossible.

For \(d<0\), the minimum-j point of K is V. Equal support and inclusion
on H's top j side give
\[
 r=u+d\delta,\qquad v-E\delta\le0,\qquad \delta\ge\delta_0.
\]
The identities
\[
 u=Es-cd,\qquad
 r=r_0+d(\delta-\delta_0),\qquad
 r_0-u=vd/E
\tag{9}
\]
show \(r\le r_0<u\). This contradicts Section 2.

### 3.4. The f axis

For \(d>0\), H's unique maximum-f point is
\(P+(r-1)j\). Its g-coordinate is
\[
                         h-s+(r-1)E<h,
\]
so it cannot belong to K. This entire alternative is impossible.

For \(d<0\), H's unique maximum-f point is U. Equal supports give
\[
                         \delta=c+rd.
\tag{10}
\]
Its g-coordinate is \(h-s+rE\). Membership in K requires \(r\ge r_0\).
Section 2 and (9) strengthen this to \(r>u>r_0\).
Consequently
\[
 0<rE-s<1,\qquad \delta<\delta_0,
\tag{11}
\]
so U lies in the strict relative interior of K's minimum-f side.
The upper inequality in (11) follows from \(r<1\), \(E\le1\), \(s>0\).

### 3.5. The complete d=0 case

Here \(E=1\), \(n=f\), \(j=g\), \(u=s\), \(v=c\).
Section 2 gives \(r>s\).
In the (f,g) frame H's intervals are
\[
 [L-c-1,L-c]\times[h-s+r-1,h-s+r].
\]
Its g interval overlaps K's g interval in the positive-length interval
\([h,h-s+r]\), since \(0<r-s<1\).
Disjoint interiors and contact therefore force the other intervals to
meet at their endpoints:
\[
                            \delta=c.
\tag{12}
\]
Thus HK is a genuinely shared f-normal interface with geometric segment
\[
               \{L-c\}\times[h,h+r-s].
\tag{13}
\]
The original HK mean may be anywhere on this entire segment, including
either endpoint. It is not replaced by U.

There is no g-normal contact or vertex/vertex endpoint left when d=0:
those would require \(r=s=u\), which Section 2 excludes.

## 4. Complete selected-normal and original-mean classification

The geometric alternatives determine the selected force types, not merely
a new list of possible auxiliary normals:

| Sign | Exact original contact condition | Actual selected HK type |
|---|---|---|
| \(d>0\) | \(\delta=\delta_0,\ r>r_0\) | H-owned singleton; normal n, application V |
| \(d>0\) | \(r=r_0,\ \delta>\delta_0\) | K-owned singleton; normal g, application U |
| \(d>0\) | \(r=r_0,\ \delta=\delta_0\) | Vertex/vertex singleton; original free normal strictly between n and g, application \(U=V\) |
| \(d<0\) | \(\delta=c+rd,\ r>u>r_0\) | K-owned singleton; normal f, application U |
| \(d=0\) | \(\delta=c,\ r>s=u\) | Genuinely shared HK; normal \(f=n\), full original mean interval (13) |

For a side-interior/vertex singleton the common separating normal is
unique, hence it is the displayed owner axis. At the vertex/vertex row,
H's relevant outward normal cone is spanned by n,j, and K's incoming cone
is spanned by f,g. For \(d>0\) their intersection is the sector from n to g.
The original strict singleton convention places the selected normal in
its interior, so it is a positive normalized combination of n and g.
Neither endpoint is selected by changing the force afterward.

The five rows are disjoint and exhaustive. They are not five sampled
poses. Every continuous parameter, every genuine force and every
application mean in each row remains.

In particular, no H-owned j case survives, no free HK case with
\(d\le0\) survives, and the entire shared-HK domain is exactly the
d=0 f-normal row, with its unchanged mean interval.

### 4.1. The H-owned row has no third square at its near vertex

In the first row, V is in the strict relative interior of H's front
side and is K's near vertex. No third interior-disjoint unit square B
can contain V.

At V, H locally occupies the open n-negative half-plane and K the
quadrant spanned by f,g. Since n=E f+d g with E,d>0, both quadrant rays
lie strictly inside the n-positive half-plane. Each of the two remaining
connected angular regions has aperture strictly below pi/2. A unit
square's local open interior directions at any of its points form a
connected sector of aperture at least pi/2: pi/2 at a vertex, pi at a
side-interior point, and 2pi at an interior point. Such a sector cannot
fit in either region. Crossing between them would overlap H or K.
This excludes every orientation and physical B mask.

Thus the entire near-vertex KB feature is impossible under strict
H-owned HK, without radius or force premises. This does not apply at
r=r0, where V is also an H vertex; the original free n/g junction
remains. Root and a separate independent reviewer checked this argument
and its scope in REVIEW_PARALLEL_HK_2026_10_25.md.

## 5. Complete reviewed five-row join

NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_NEAR_EXCLUSION.md and
NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_SIDE_EXCLUSION.md together
exclude the entire second row. Their full geometry and 70 exact coefficient
identities passed root and independent review. Section 4.1 additionally
excludes the whole near-vertex KB feature in the first row.

LOW_DIAMOND_F_INTERFACE_ROOT_PROJECTION.md, its complete rotation and
lower-g comparisons, and the full UNIQUE_RETURN_EXCLUSION and
RADIAL_RETURN_EXCLUSION sources now exclude the fourth and fifth rows
together. The proof covers both B masks, including every original
radial weight endpoint and the entire d=0 shared-HK mean interval.
REVIEW_LOW_F_INTERFACE_2026_10_25.md records root and separate full
saved-source, prerequisite, exact-algebra and geometric review.

The three complete LOW_DIAMOND_FREE_HK_NEAR_RETURN_EXCLUSION.md,
LOW_DIAMOND_FREE_HK_SIDE_RETURN_EXCLUSION.md and
LOW_DIAMOND_FREE_HK_OUTER_RETURN_EXCLUSION.md sources now exclude the
entire third row. Their exhaustive actual KB fan retains the free n/g
normal and genuine K3 force and moment. The near proof handles shared HB
before coincident B2; the outer proof uses the original A barrier and
bounded contact triangle; the left side verifies every hypothesis of the
preserved scalar comparison at Delta=0. Root and separate independent
full-source/direct-prerequisite reviews passed, recorded in
REVIEW_FREE_HK_DIAMOND_2026_10_25.md.

The final H-owned n row is now completely excluded for physical radial
B by LOW_DIAMOND_H_OWNED_HK_RADIAL_AND_NONNEGATIVE_PROJECTION_EXCLUSION.md.
Its cn>=0 argument covers both masks. For cn<=0 the two distinct actual
boundary contacts P,V give |Z|^2<13/16 for every H point; the strict
physical radial-B norm bound makes HB impossible for every individual
circle-weight endpoint. The complete original HA/AK and five-row HK
join is reviewed in REVIEW_LOW_H_OWNED_HK_RADIAL_AND_UUS_JOIN_2026_10_25.md.
The entire UUS diamond mask, including both radius intervals, is CLOSED.

The final physical UUU residue has d>0, delta=delta0 and r>r0,
strict H-owned HK normal n, and cn<0. The actual upper-g K circle corner
and h>0 are proved in LOW_DIAMOND_H_OWNED_HK_RETURN_FAN.md.
LOW_DIAMOND_H_OWNED_HK_FRONT_SUPPORT_BOUND.md further gives
3/8<N=P dot n=V dot n<1/2, so -1/8<cn<0. Every H point still has
|Z|^2<13/16; both statements have independent full-source reviews.

The full actual KB fan is the left -f side or upper-left K vertex.
LOW_DIAMOND_H_OWNED_HK_SIDE_RETURN_REDUCTION.md exhausts the entire
left-side feature to a strict H-owned HB=j singleton at B's vertex
opposite its physical circle corner. It excludes every aligned, free,
B-owned and shared HB alternative while retaining the actual applications
until physical exclusion. See
REVIEW_LOW_H_OWNED_HK_SIDE_RETURN_REDUCTION_2026_10_25.md.

The complete upper-left KB feature is now excluded by
LOW_DIAMOND_H_OWNED_HK_UPPER_LEFT_RETURN_EXCLUSION.md. The original A2
equation gives u/v<4/5, a whole concave comparison gives
N*delta>E*tau*W, and the unchanged K3 moment about the actual KB point
gives a strict B-owned slope. It implies sigma<N, contrary to the
actual B2 origin moment. The full independent audit is
REVIEW_DIAMOND_UPPER_LEFT_EXCLUSION_2026_10_25.md.

The final strict K-owned left KB=-f feature is now excluded by
LOW_DIAMOND_H_OWNED_HK_SIDE_RETURN_EXCLUSION.md, with the complete
original range h<=y<=W. The stronger whole-row front comparison gives
N+(4/15)d>1/2. The actual K3/A2/B2 moments retain every force and
give (beta+eta)/nu<2D_B/D_A. One whole-interval cubic with a positive
quadratic lower bound then proves strictly positive original A/K/B
pressure. Together with the intact petal this contradicts H5.

Both complete KB features are therefore excluded. No owner, free
normal, shared mean, physical mask, individual zero radial weight,
true K3 term, actual application or completion square is removed.
Root's full analytic/force review is
REVIEW_DIAMOND_FINAL_SIDE_PRESSURE_2026_10_25.md.

The separate full original load, negative-endpoint, HA/AK owner,
mask, radius and five-row HK assembly passed in
REVIEW_COMPLETE_DIAMOND_ASSEMBLY_2026_10_25.md. All five original
remaining diamond gates now close, including DIAMOND_HUB_EXIT.
The earlier two UUS closures remain unchanged, and no ID is added.
The coarse C2.34.b0 cell remains open through its separate ABC orbit.
The unrestricted theorem, original equality and older full
prerequisite-chain audit remain open. No Lean compilation or CI was run.
