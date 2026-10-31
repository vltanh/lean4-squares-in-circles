# Full independent audit: the four-load oblique bypass and its center lemma

Date: October 28, 2026.

Reviewer: triangle_bridges, independently of source author hexagon.

**Verdict: ACCEPTED in full, without correction.** Both complete sources
were read and independently rederived, including their substantive
physical prerequisites and the literal original graph/load assignment.
This record accepts the whole oblique B/X interface of the original
`M6.B6.PENTAGON.H2_D0.L1234` family. It also separately accepts the
force-free three-boundary-center theorem at its stated arbitrary-degree
scope. The parallel interface and the exhaustive two-interface parent
have their own separate reviews; no whole coarse-cell claim is made here.

## 1. Exact complete sources and substantive input pins

The reviewed mathematical sources are unchanged:

| Source | SHA-256 |
| --- | --- |
| `THREE_BOUNDARY_PATH_MIDDLE_CENTER_OBTUSE.md` | `c2fb1f360163a513724c5388a5eca77b1ecadef40f39b7f6b3e46ea52335623b` |
| `INNER_PENTAGON_FOUR_LOAD_OBLIQUE_BYPASS_EXCLUSION.md` | `c97050fd440b02a5aa71849c603132d9b37cb479a58e183102ce3f4d5a3dc6e3` |

I read and checked the following current literal inputs. Their hashes
were read back from the actual local files, rather than inferred from
their titles or historical acceptance records.

| Input | SHA-256 | Exact use checked |
| --- | --- | --- |
| `CIRCLE_CONTACT_ANGULAR_ORDER.md` | `2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449` | Complete physical center annulus, pair-angle lower bound, contact-angle upper bound in Sections 1–3 |
| `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md` | `fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434` | Original no-chord spokes 0,2 and four-load set 1234; actual degrees and all three extras |
| `UNIT_BYPASS_NORMAL_CHANNEL.md` | `d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8` | Whole width-one channel theorem and the complete force-free projection-containment calculation of Section 4 |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a` | Original strictly exposing singleton convention, before extraction; compatible selected class remains unchanged |

I also reread the complete early physical and V3 feature calculations
in `OBLIQUE_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md`,
`95cdc83959d7a93b5788c9678d0c8bda5f2f0298df27a9c1d4920a4c9cf126ee`.
The new source repeats those calculations in full. Its old later
unloaded-Y transmission and diagonal-width steps are not imported.
The distinct complete parallel source is
`INNER_PENTAGON_FOUR_LOAD_PARALLEL_BYPASS_EXCLUSION.md`,
`46a853de32bca6a4198c3305fea1f9cdba56744da86712d07ae0b812f93b8494`;
the present acceptance does not substitute for its separate full audit.

## 2. Independent derivation of the complete center theorem

The radius interval is the entire closed interval

    79/40 <= R <= sqrt(1105)/16.

For every actual circle-touching unit with center radius r, the corner
formula and unit circumradius give

    R-1/sqrt(2) <= r <= sqrt(R^2-1/4)-1/2.

The cited physical input therefore gives the strict uniform annulus
5/4<r<61/40. I checked both radical comparisons and the full physical
arguments for pair separation greater than pi/5 and actual-contact
separation less than 2pi/5. None of these statements depends on a
positive circle multiplier, normal choice, force resultant, or degree.

At a physical three-boundary path B–A–C, the two neighbor directions
must be on opposite sides of A's radial direction. If both were on
one side, their angles from A would lie in (pi/5,2pi/5), and their
own minor angular separation would be less than pi/5. This is an
immediate contradiction to the pair bound, including the possible
choice of angular representatives across the negative real axis.

Choose e along the middle center and f toward B. With actual center
radii r,s,t, the two displacements have the exact form

    b-a = -(r-s*cos(alpha))*e + s*sin(alpha)*f,
    c-a = -(r-t*cos(beta))*e - t*sin(beta)*f,

where alpha,beta lie in (pi/5,2pi/5). Throughout this interval,
cos(theta)<13/16 and sin(theta)+cos(theta)>5/4. The latter follows
from strict concavity and the two endpoints; the smaller endpoint
at 2pi/5 has cos>3/10 and sin>19/20. These are exact radical
inequalities, not decimal approximations.

Consequently both radial deficits u,v are positive, with uniform
reserve 7/640, while each tangential magnitude exceeds the
corresponding radial deficit, with comparison reserve 3/80. Thus

    (b-a) dot (c-a) = u*v-p*q < 0.

This proves the whole new theorem, at both closed radius endpoints,
for all actual circle masks and zero individual circle weights. It
does not assert obtuseness of the contact normals. Its use later in
the oblique proof concerns actual center displacements only.

## 3. Literal four-load graph and the unchanged channel

The relabeling is exactly

    A=2, B=1, V=0, C=4, Y=3, X=H.

The full original graph is A–X–V–B–A and A–Y–C–V. Its true degrees
are A3/B2/V3/C2/Y2/X2. X and V are unloaded; A,B,C,Y are loaded
and hence physical boundary units. In particular Y is a loaded
degree-two body throughout this proof. It is never assigned a
transmitter width or a collinear pair of forces. All three remaining
physical squares are retained and arbitrary.

The actual B bypass makes the true X2 channel side-normal with width
one. Its actual original means have the common height z in [-1,0].
The coordinate normalization is only a rigid notation change:

    X=[0,1]x[-1,0], A in x<=0, V in x>=1, B in y>=0,
    E=(0,z), R0=(1,z).

No translated coordinate is mistaken for the containing-circle origin.
B's oblique frame is P+[0,1]u+[0,1]v, with P=(p,h),
u=(c,s), v=(-s,c), c,s>0 and c^2+s^2=1. Its real two contacts
give 1-c<=p<=s, hence 0<p<1. These weak projection endpoints,
h=0, and z=-1,0 all remain in the calculation.

Y is used first only through the diameter of its actual closed unit:
any actual AY and CY applications are at distance at most sqrt(2).
This holds for every original mean and every Y frame, independently
of its loaded force balance.

## 4. The support-coordinate bound covers every actual neighboring frame

I rederived the bound min(S.x)>=P0.x-t for a minimum support point
P0 with inward unit normal (r,-t), r,t>0. At a strict support vertex,
an inward axis with negative x must be (-a,-b), with a,b>0, and
its positive normal projection gives a<t. At most one inward axis
can extend left. At an owned side, the full mean representation is

    S=P0-eta*(t,r)+[0,1]*(r,-t)+[0,1]*(t,r), 0<=eta<=1.

Its exact leftmost coordinate is P0.x-eta*t. Thus both owned endpoints,
every interior side mean and all strict vertices are included. The
bound does not rely on a unique circle corner, a degree-two equation,
or proper concurrence. This is essential in both VC side exits.

## 5. Complete oblique-V contact and full three-force equations

At oblique V, R0 is its unique minimum-x vertex and the two inward
axes are f=(a,b), j=(b,-a), a,b>0. I checked all eight vertex/side
features against the actual B projections:

* The minimum vertex, lower near side and lower vertex are below B;
  the possible height-zero endpoint cannot equal B's lowest point
  because its first coordinate is 1 while p<1.
* The opposite vertex has first coordinate greater than 2, beyond B.
* At the far f side, minimizing f on B forces its u coordinate zero,
  giving first coordinate at most p<1.
* At the far j side, minimizing j on B forces its v coordinate one,
  giving first coordinate at most p-s+c<=c<1.

Thus VB is at R0+xi*f, 0<xi<=1. Its actual normal has positive y
and negative x, since a nonnegative x normal would again minimize
B at x<1. Writing the whole force as (-beta,gamma), both positive,
the original B feature is P+tau*u, 0<tau<=1, and gamma/beta<=c/s.
The weak ratio is the genuine B-owned side case; no tau is replaced.

Comparing the actual coordinates gives

    xi*(a-b) <= s-1+tau*(c-s)<0,

so a<b at every endpoint. If V owns its near -j normal, full V3
puts its third application at the actual opposite vertex and gives

    mu*(xi-1)=lambda*(b-a)>0.

This excludes the entire xi interval, including xi=1. The surviving
VB point is therefore the strict upper vertex R0+f, with
b*gamma-a*beta>0 and a<=c+s-1<5/12, b>9/10.

All three original V forces are present in this derivation. I
independently expanded the torque expressions about R0, using only
a^2+b^2=1; their signs and application locations agree with the source.

## 6. Complete VC feature cover, retaining loaded Y

Full V3 gives the actual third force

    F_VC=(lambda+beta,-gamma).

Its j component is positive, leaving exactly the far vertex, far
j-normal side, or lower vertex. Their full checks are:

1. At the far vertex, the complete torque is
   -b*gamma+a*beta+(a-b)*lambda, strictly negative.
2. At the owned far side R0+j+eta*f, 0<=eta<=1, the support-coordinate
   bound gives min(C.x)>=1+b+eta*a-a>=1+b-a>89/60>sqrt(2).
   This contradicts Y's actual diameter between A in x<=0 and C.
   No Y force or width is used, and both eta endpoints remain.
3. At the strict lower vertex R0+j, the full moment is
   (b-a)*gamma=a*lambda+(a+b)*beta. With the original B ratio it
   forces c>s and a<7/20. I checked both complete s/c ranges separated
   at 1/2, including equality. If n=(n_x,-n_y) is the actual VC unit
   direction, the exact ratio then gives n_y<(a+b)/sqrt(2)<b.
   The support-coordinate bound yields min(C.x)>1.

For parallel V, its full actual chart is [1,2]x[H-1,H], with
H-1<=z<=H<=1. Lower and right supports cannot touch B; a North
contact would require B's lowest point with p<1. A West VB force
makes VC East by full V3, placing C in x>=2 and violating Y's
diameter. A strict Northwest VB force puts VC at V's bottom-right
vertex, and the same bound gives min(C.x)>=2-n_y>1.

This exhausts every V frame, both original VX mean endpoints, every
VB/VC owner, and every actual VC mean. It establishes C entirely in
x>1 without using any C circle mask or loaded C2 concurrence.

## 7. Physical Y separation and the new center contradiction

Because Y touches A in x<=0 and C in x>1, its actual horizontal
projection contains [0,1] and has length greater than one. Hence Y
is oblique. The entire Section 4 SAT argument of the bypass theorem
uses only this projection containment and disjoint interiors, not
an unloaded equation at the projecting square. It therefore applies
to this actual loaded Y and X, giving Y in y>=0 or Y in y<=-1.

I checked the exact SAT numerator identity

    (1-a)*(a+b+1)-b*(a+b-1)=2*b*(1-a),

on a^2+b^2=1, including the zero-axis endpoint. It retains weak
separation and does not infer a new XY contact.

If Y were above X, both B and Y centers would have height at least
1/2 and first coordinate at least 1-sqrt(2)/2>0. A's actual center
has first coordinate at most -1/2 and height at most 1/2: this was
checked separately for its oblique right vertex E and its entire
parallel-side mean interval. Thus both displacements from A have
positive x and nonnegative y, and their dot product is positive.

The actual path B–A–Y consists of three boundary units. The newly
proved force-free theorem gives a negative dot product, a strict
contradiction. The only remaining physical position is Y below X.
This application retains A3, loaded Y2, all weights and all physical
corner masks. No circle force direction is used as a center direction.

## 8. The final A cover and its literal reflection

For oblique A, write its inward axes at E as (-a_A,b_A),(-b_A,-a_A).
I checked every lower, far vertex and far-side feature against B.
The two far-side minimizations have x>0, while all A points have
x<=0. The only contact is E+xi_A*(-a_A,b_A), 0<xi_A<=1, with a
strict Northeast actual normal. The B point is P+tau_A*v,
0<tau_A<=1. Actual coordinates yield

    xi_A*(a_A-b_A)<=c-1+tau_A*(s-c)<0,

so a_A<b_A. Every owned side endpoint is included in this weak-mean
calculation.

Reflecting (x,y) to (x,-1-y) preserves X and sends the actual below-X
Y above it. Its projection still contains [0,1]; its rightmost A
contact remains E at an allowed height in [-1,0]. The upper A axis
in the reflected chart is now (-b_A,a_A). The same complete physical
argument therefore gives b_A<a_A. It requires neither Y's force
equation nor a special far-right neighbor; the source states and
proves that degree-free scope explicitly. The contradiction is valid
for z=-1 and z=0 and for all original side means.

For parallel A=[-1,0]x[a0-1,a0], every B point with x<=0 has height
strictly greater than zero, so AB implies a0>0. Every Y point with
x<=0 has height strictly less than -1, so AY implies a0<0. The
strictness persists when B's lowest height is zero or Y's highest
height is -1, because their unique extreme vertices have x in (0,1)
and cannot belong to A. This closes the complete final frame case.

## 9. Independent exact arithmetic and physical endpoints

I recomputed the following exact positive reserves using independent
Fraction arithmetic, in addition to the displayed symbolic torque
derivations and full geometric feature checks:

| Comparison | Exact reserve |
| --- | --- |
| (29/40)^2-1/2 | 41/1600 |
| (162/5)^2-1041 | 219/25 |
| 1-5/8; 1-1341/1600; 1-3721/4000 | 3/8; 259/1600; 279/4000 |
| 275/128-2 | 19/128 |
| 5-(11/5)^2; 5-(111/50)^2; (9/4)^2-5 | 4/25; 179/2500; 1/16 |
| 5/4-(61/40)*(13/16) | 7/640 |
| 25/16-61/40 | 3/80 |
| (17/12)^2-2 | 1/144 |
| 119/144-(9/10)^2 | 59/3600 |
| (89/60)^2-2 | 721/3600 |
| (7/20)^2-1/10; (27/20)^2-9/5 | 9/400; 9/400 |
| 2/5-7/18; 2-(7/5)^2 | 1/90; 1/25 |

The identity 1+9/10-5/12=89/60 was also checked exactly. The proof's
strictness there comes from the independently strict b and a bounds,
not from incorrectly making that rational identity strict.

The numerical checks are not pose sampling and supply no new premise.
All actual masks, zero individual circle weights, coincident or
endpoint means, and unchanged positive magnitudes remain covered by
the hand arguments. No canonical slide, force replacement, deleted
edge, or post-extraction selection is used anywhere in this pair.

## 10. Exact accepted conclusion and review boundary

The new center theorem is fully accepted at its stated force-free,
arbitrary-degree, physical-boundary scope. The entire original oblique
B/X interface of H2_D0.L1234 is fully accepted in the declared radius
window. It retains loaded Y2 and all other original forces, degrees,
applications, masks and three extras.

The short whole-family parallel/oblique assembly remains a separate
exact join, reserved with rooted_blocks. This record does not tick a
ledger or extend either theorem to other pentagon masks. No source
correction, remote write, Lean compilation, CI run, or shared metadata
change was made during this independent audit.
