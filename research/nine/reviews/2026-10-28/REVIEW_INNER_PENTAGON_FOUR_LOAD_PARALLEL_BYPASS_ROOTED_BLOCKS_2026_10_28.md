# Full independent review: the four-load inner-pentagon parallel bypass

Date: October 28, 2026.
Reviewer: rooted_blocks.

**Disposition: ACCEPTED in its entire stated parallel-frame domain.
No correction is requested.** The actual oblique B/X interface remains
outside this theorem; this record does not close the whole load family.

## 1. Exact source and all six complete direct reads

I read and independently derived the complete
`INNER_PENTAGON_FOUR_LOAD_PARALLEL_BYPASS_EXCLUSION.md`, SHA-256
`46a853de32bca6a4198c3305fea1f9cdba56744da86712d07ae0b812f93b8494`.

I also read all six direct sources in full and checked their current
SHA-256 against the theorem's Section 7:

| Source | Exact SHA-256 | Literal scope used |
| --- | --- | --- |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434 | Original two-spoke/no-chord graph and load set1234 |
| UNIT_BYPASS_NORMAL_CHANNEL.md | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 | True unloaded X2, actual width-one channel and unchanged mean |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a | Original strict singleton convention and physical circle-point nonsharing |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb | Degree-free contained-unit support and center bounds in Section 1 only |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708 | Complete actual balanced four-boundary path with arbitrary endpoint degrees |
| PARALLEL_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md | 0643b1ea0c6cd66724f2ad130c9cbd3fb2ffdbb53979e43170d7b58b2023e3be | Section 2's physical parallel-frame argument only, repeated in the new source |

All seven current hashes, including the reviewed theorem, match exactly.
No unreadable historical source or deferred review supplies a step.

## 2. Original graph, circle balance and exact parallel frame

The actual labeling A=2, B=1, V=0, C=4, Y=3, X=H gives exactly
the edges AX,XV,VB,BA,AY,YC,CV. The full degrees are
A3/B2/V3/C2/Y2/X2. The positive circle loads are precisely A,B,Y,C;
X and V have zero total circle load. In particular the real Y2 is
loaded and is never assigned a transmitter equation. The three
arbitrary other physical squares remain present.

Summing all six original force equations cancels every internal
pair force and gives the required balance of the four complete
circle resultants. The actual boundary path is B-A-Y-C. I checked
the complete four-boundary-path proof: its center-angle/corner-cone
argument permits both physical corner masks and zero individual
weights and yields |c_B-c_C| > 1+sqrt(2). It requires no false
degree-two equation at A and no fifth-unit incidence in this use.

The genuine X2 channel has the real bypass B, so its width is one.
After a rigid coordinate change, with the original circle origin
still recorded as O=(o_x,o_y), the complete physical chart is

    X=[0,1] x [y,y+1],
    B=[0,1] x [t,t+1], t>=y+1,
    A=[-1,0] x [a-1,a],
    V=[1,2] x [v-1,v],
    t<=a<t+1, t<=v<t+1.

I independently checked the endpoint argument. A tilted A or V
would have one extreme-x vertex supplying both its X and B
contacts. It would necessarily be at the common endpoint t=y+1,
making the original AX or XV contact a singleton vertex/vertex
contact with a side-axis channel normal. That contradicts the
initial strict singleton convention. An aligned AX or XV singleton
endpoint is excluded for the same reason; their actual side
intersections therefore have positive length, giving the strict
upper bounds a,v<t+1. No equation at Y enters this derivation, and
no original side mean is centered or changed.

The older 0643 theorem's later unloaded-Y channel proof is not
transferred. Only this complete physical frame calculation is used.

## 3. The entire shared VB side contradicts the actual B load

For v>t both original V-to-X and V-to-B normals are West. The
complete unloaded V3 equation makes V-to-C East, so C lies in
x>=2. The degree-free contained-unit bound gives 2-o_x<=d.
The two actual x=-1 corners of A imply (o_x+1)^2+1/4<=R^2 and
therefore o_x<=d. Thus 2-d<=o_x<=d and d>=1.

Both vertical endpoints of A have absolute height from O below
5/8, using o_x+1>119/60. The original t range puts B's bottom
inside A's vertical interval and its top no more than one above
A's top. Consequently every B point has vertical distance below
13/8 and horizontal distance at most d<61/60. The resulting
strict bound is below (79/40)^2, so every actual B corner is
circle-clear. This contradicts B's genuine positive circle load.
No physical C frame, force or mask is selected to obtain this exit.

## 4. The full V3 singleton moment and all possible C supports

For v=t, the original V-to-B force is strictly Northwest at
P=(1,t). Writing the actual V forces as

    (-lambda,0), (-beta,gamma), (lambda+beta,-gamma),
    lambda,beta,gamma>0,

is the full three-force equation, with VX at (1,z), t-1<=z<=t,
and VC at the strict Southeast V vertex (2,t-1). Its moment
about P is exactly

    lambda(z-t)+lambda+beta-gamma=0.

Hence gamma=beta+lambda*rho with rho=1+z-t in [0,1]. In particular
beta<=gamma<=lambda+beta, retaining both original mean endpoints.
The actual normalized VC direction n=(c,-s) therefore has c>=s>0.

I checked the complete minimum-support observation on C. At a
strict minimum vertex, the inward-axis decomposition of n has
positive coefficients A0,B0 with A0^2+B0^2=1. The center
displacement has n component (A0+B0)/2>=1/2 and absolute Jn
component at most1/2. At an owned minimum side its displacement
is n/2+tau Jn for the full actual tau in [-1/2,1/2]. Thus in
either case its x component is at least (c-s)/2>=0. The actual
center satisfies (c_C)_x>=2, including c=s, owned-axis vertices
and both side-mean endpoints. No C2 concurrence is used.

## 5. Excluding one circle-origin half-plane by the full path bound

If o_x<=1/2, the actual C center has x-distance at least3/2 from
O. The universal center bound |c_C-O|<91/60 then makes its
absolute y-distance below1/4. The B center is (1/2,t+1/2), with
nonnegative x-coordinate relative to O. Consequently

    0<(c_C)_x-(c_B)_x<91/60,
    |(c_C)_y-(c_B)_y|<53/30.

The squared distance is strictly below (12/5)^2. Since
12/5<1+sqrt(2), this contradicts the original balanced-path
separation. This deduction uses the actual centers, not a
selected circle corner or force-line intersection. It includes
the boundary o_x=1/2. Therefore the remaining origin range is
strictly o_x>1/2.

## 6. Whole physical B mask and the unchanged B2 contradiction

For o_x>1/2 the B corner on x=1 is strictly nearer O than the
corner at the same height on x=0. Its bottom-left corner belongs
to actual A and its bottom-right corner belongs to actual V.
The complete circle-point nonsharing lemma excludes each from
the physical circle. As B is genuinely loaded, its only physical
circle corner is therefore Z=(0,t+1). This proves the entire
physical mask before using a single-corner force formula; it
does not simply assign zero weight to another physical corner.

Put H0=t+1-o_y and let its complete circle force be
kappa(-o_x,H0), kappa>0. The full actual B-to-A contact cover is
(-mu,-nu) at (0,t+xi), where mu>0, nu>=0 and 0<=xi<1.
For a>t it is the original shared-side mean with nu=0; for a=t
it is the original strict Southwest singleton with xi=0 and
nu>0. These are all cases, including every original shared mean.

The other force is (beta,-gamma) at (1,t). The complete B force
equation is

    beta=mu+kappa*o_x,
    gamma=kappa*H0-nu.

I independently derived the circle moment about P=(1,t) as
-kappa*(H0-o_x), and the B-to-A moment as nu+mu*xi. Thus the
unchanged B2 moment gives nu+mu*xi=kappa*(H0-o_x), and exactly

    gamma-beta=mu*(xi-1)<0.

This contradicts gamma>=beta from the original V3 equation.
The VX force, original VX mean, full B circle vector and original
BA mean all remain. No load at Y, false V2 equation, properness
assumption or later selected direction is introduced.

## 7. Exact arithmetic and accepted scope

I independently recomputed all six rational reserves by Fraction
arithmetic, obtaining exactly:

| Comparison | Positive reserve |
| --- | --- |
| Actual A endpoint-height bound | 451/57600 |
| B corner clearance below the minimum radius | 163/720 |
| C transverse center bound | 11/900 |
| Endpoint-center squared distance below (12/5)^2 | 1219/3600 |
| Strict d<61/60 at the maximum radius | 31/57600 |
| sqrt(2)>7/5 | 1/25 |

Both full moment eliminations were also checked independently
by sparse exact coefficient addition. These calculations verify
the displayed identities; the geometric and force arguments
above establish the theorem without numerical pose premises.

The v>t and v=t alternatives exhaust the actual parallel frame.
All circle-origin positions, physical C masks/support owners,
original side means and their endpoints are covered. The proof
excludes the whole parallel B/X interface of the original
H2_D0.L1234 family at its actual A3/B2/V3/C2/Y2/X2 degrees,
keeping all nine physical squares.

The oblique interface and any whole-family assembly remain
separate. This independent acceptance changes no frozen source,
graph/load cover, original ID, metadata, selected normal, force,
application, square, remote object, Lean state or CI workflow.
