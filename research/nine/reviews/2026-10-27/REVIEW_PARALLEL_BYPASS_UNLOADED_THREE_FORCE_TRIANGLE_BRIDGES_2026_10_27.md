# Full independent review: parallel bypass at an unloaded three-force endpoint

Date: October 27, 2026.
Reviewer: triangle_bridges, independently of the source author.

**Disposition: ACCEPTED in the entire stated radius-free local scope.
No correction is requested.** I read and rederived the full physical
frame cover, the complete unloaded V3 force calculation, every C owner,
both actual Y widths, and all shared-side and section endpoints.

## 1. Exact source and full original graph

Reviewed in full:
`PARALLEL_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md`,
SHA-256
`0643b1ea0c6cd66724f2ad130c9cbd3fb2ffdbb53979e43170d7b58b2023e3be`.

Its actual positive edges contain A-X-V-B-A and A-Y-C-V, with
six distinct bodies. The actual X and Y are unloaded degree two.
The entire positive neighborhood of the unloaded V is exactly X,B,C.
A,B,C may have arbitrary further positive forces. The physical frames
of B and X are assumed parallel; no selected normal is replaced by
that physical-frame assumption. All other squares and all original
means and physical zero-weight contacts remain present.

I checked the original inner-pentagon labels against the complete
load cover `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md`,
`fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434`.
For spokes 0,H,2, no outer chord, and load set {0,1,3}, the source's
substitution A=0, B=1, V=2, C=3, X=H, Y=4 gives precisely
A3/B2/V3/C2/X2/Y2, with X,Y,V unloaded. The existing roadmap ID is
`M6.B6.PENTAGON.H2_D0.L013`. Its three other physical units remain.
No whole load-family or whole C1.6.b0 closure is inferred from the
parallel-interface theorem.

## 2. Exact transmission and selection prerequisites

I read the complete degree-two transmission proof in Section 5 of
`PHYSICAL_CONTACT_STRESS.md`,
`9bbb1b0e278508841a0eb5284ab845be78801753308e346026f38aad45ea5af9`,
and the literal actual-path version in Section 1 of
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`,
`6f28e0fc0631928506de027dfe5609e8d5adf42a1551eef955a6d2f1acad7b6e`.
Unloaded force balance gives equal opposite forces, and torque makes
the two actual applications collinear along that normal. The full
unit support cover gives exactly width one with matched transverse
means, or width sqrt(2) with the two actual opposite vertices.
The later radius-dependent and whole-cycle claims of the old path
source are not used.

I also read all four sections of `UNIT_BYPASS_NORMAL_CHANNEL.md`,
`d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8`,
including the complete physical diagonal exclusion and transverse
separation. B is an actual unit bypass of the X channel, so X must
be side-normal with reserve one, independently of B's degree or load.

The only normal-selection premise used is the existing strictly
exposing convention at actual point-only vertex/vertex contacts.
I checked its original compatible statement in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`,
`eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a`.
No new generic exclusion, circle-origin normal condition, or changed
post-extraction direction is introduced.

The rigid local coordinate normalization is legitimate: the proof
uses no circle-origin equation at A,B,C. The unloaded X/Y torque
equations and V force equation remain valid under this notation
change. The actual physical squares are not moved.

## 3. All endpoint frames and positive-length channel contacts

With X=[0,1] times[y,y+1], the channel puts A in x<=0 and V
in x>=1. A parallel B touching both has a unit horizontal interval
containing both 0 and 1, hence exactly [0,1]. Disjointness from X
puts it wholly above or below; a reflection gives B at heights
[t,t+1], t>=y+1.

If A were tilted, its maximum-x support would be one actual vertex.
Both its X and B contacts would have to be that vertex at x=0.
The two vertical intervals meet only when t=y+1, at their common
endpoint. Thus AX would be a point-only vertex/vertex contact whose
unchanged horizontal channel normal is an axis of X. It is not
strictly exposing at X, a contradiction. The same complete argument
at V's minimum-x support excludes every tilted V.

Therefore A and V are exactly the two aligned unit rectangles of
the source's equation (3). Their original AX and XV contacts cannot
have zero physical length: that would again make the actual axis
normal a forbidden vertex/vertex endpoint normal. Positive length
gives a-1<y+1 and v-1<y+1. Actual contact with B gives a>=t and
v>=t, so the full ranges are t<=a<t+1 and t<=v<t+1.

This deduction does not choose either original transverse channel
mean. It also permits the physical B/X touching endpoint t=y+1,
with any extra zero-weight contacts there.

## 4. Whole V/B interface and full V3 force

For v>t, the V/B intersection is the full positive-length vertical
segment from height t to v. Thus both original V-to-B and V-to-X
normals are West. The complete unloaded V3 sum forces the remaining
V-to-C normal East. The actual A and C then lie in x<=0 and x>=2.
Their unchanged Y channel would require an endpoint distance at
least two, contrary to either of its exact widths 1 or sqrt(2).
This closes every shared-side mean in that entire row.

For v=t, the actual V/B contact is the singleton (1,t), where
the strict original V-to-B normal is Northwest with both components
nonzero. Together with the positive original West V-to-X force,
the full V3 equation makes V-to-C strictly Southeast. Both signs
are strict consequences of the original positive magnitudes; an
owned-axis limit is not silently discarded. Its unchanged V port
is precisely P=(2,t-1). No torque or load equation at C is needed.

## 5. Complete C support-span observation

I checked the new observation for every actual support feature.
At a strict minimum-n vertex, n=(c_0,-s_0), c_0,s_0>0, is a
positive combination of the two inward orthonormal axes. At most
one axis has negative x; that component is strictly greater than -1,
since (-1,0) has negative dot product with n. Hence the whole closed
unit has x>P_x-1. The same reasoning for a positive y component
gives y<P_y+1. Neither bound assumes that a support-axis component
is uniformly bounded away from its limiting value.

If n is an owned side axis, the exact original mean eta remains
in [0,1]. The frame P-eta*j+[0,1]n+[0,1]j gives minimum x
P_x-eta*s_0>P_x-1 and maximum y
P_y+(1-eta)*c_0<P_y+1. This includes axis normals at vertices,
which belong to the owned row rather than the strict-vertex row.

Thus every actual C, at every owner and side endpoint, lies in the
strict whole-square region x>1, y<t. This strictness is supplied
by the actual nonzero components of n, not by generic selection.

## 6. Both original Y widths and all mean endpoints

For the unchanged A/Y/C channel, R_x<=0 and S_x>1 force
w*m_x>1. Width one is impossible. Hence the actual Y is diagonal
with width sqrt(2) and m_x>1/sqrt(2).

If m_y>0, the actual A support is its upper-right vertex (0,a),
and S_y=a+sqrt(2)*m_y>t contradicts the whole C bound. The complete
remaining direction is m=(c,-s), c>s>=0 and c>1/sqrt(2).
For s>0, R is the original lower-right A vertex. For s=0, R is
its unchanged East-side mean, and S_y=R_y<t supplies the same
upper bound. Both rows yield exactly

    R=(0,t-1+delta), 0<=delta<1.

The diagonal-transmitter theorem fixes the actual two opposite
application vertices R,S and therefore the complete Y frame in
equation (12), up to exchanging its own axes. There is no remaining
transverse slider being fixed by choice.

## 7. Exact open-section identities and the physical contradiction

Since c>s, both intermediate Y vertices have x strictly less than
one, while S_x=sqrt(2)*c>1. The line x=1 therefore cuts the actual
open Y interior between its two far incident edges.

I independently derived both line-section formulas. Multiplying the
lower expression by c+s reduces its numerator to

    -sqrt(2)*s(c+s)-(sqrt(2)*c-1)(c-s)
       =-sqrt(2)*(c^2+s^2)+c-s=-sqrt(2)+c-s.

For the upper expression, multiplication by c-s gives

    -sqrt(2)*s(c-s)+(sqrt(2)*c-1)(c+s)
       =sqrt(2)*(c^2+s^2)-c-s=sqrt(2)-c-s.

These are exactly the two source identities, including s=0.
Both denominators and both displayed subtracted/added numerators
are strictly positive because c>s and c+s<sqrt(2). Hence

    y_-<t-1+delta<t,  y_+>t-1+delta>=t-1.

The interval between y_- and y_+ is nonempty and open. It has a
nonempty open intersection with (t-1,t), including delta=0.
A point in that intersection at x=1 is in int(Y) and on the
closed left side of the actual V. Its open Y neighborhood meets
int(V), so the two open interiors overlap. No contact point,
force normal, or original mean has been moved to obtain this
contradiction.

## 8. Whole stated conclusion and retained frontier

The shared and singleton V/B rows exhaust the actual range of v.
The proof retains the full true V3 and both exact X2/Y2 channels,
while placing no degree or circle-load hypothesis on A,B,C.
Every actual C support owner, channel width, shared-side endpoint,
horizontal m endpoint, delta=0 endpoint and t=y+1 junction is covered.

The theorem is therefore accepted as a complete radius-free parallel-
bypass exclusion. Its exact original caller removes only the whole
rim1-parallel-H interface of H2_D0.L013. The oblique rim1/H domain
remains explicitly open, and no whole load-family or coarse-cell
claim is made. The source pin was reread after this derivation.
No correction, new numerical certificate, metadata edit, remote
action, Lean compilation or CI operation was required.
