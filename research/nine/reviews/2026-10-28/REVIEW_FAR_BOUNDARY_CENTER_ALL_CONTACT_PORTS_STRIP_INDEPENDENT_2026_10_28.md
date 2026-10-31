# Independent review: a far boundary-center pair separates every pair of actual ports

Date: October 28, 2026 UTC. Reviewer: mixed_capacity_review.

**Verdict: PASS at the final frozen source below.** The qualitative and
quantitative whole-square theorems are correct on their entire stated
domains, including equality in the center-radius and center-angle
hypotheses. Both original H4 applications are literal. They impose a
necessary strip restriction on all physical return contact sets and
original means simultaneously; they do not close either original H4
load family or prove a pocket capacity.

One incidental attribution in the first submitted version was removed
during review, as documented in Section 2. It was not used in the new
strip proof or either strip application. No new mathematical estimate
was supplied by the reviewer to the adopted source.

## 1. Exact source and complete operative inputs

| Source | SHA256 | Scope checked |
| --- | --- | --- |
| FAR_BOUNDARY_CENTER_PAIR_ALL_CONTACT_PORTS_STRADDLE_ORIGIN.md | 73aac9b69b62aabaf94971abf97a1b2903cf3a0fed1cab9e8fc380fbf96678ee | Entire new source: both whole-square theorems, every endpoint, physical boundary implication and both original H4 joins |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Complete four-boundary-path proof, especially its strict minor endpoint angle and full physical masks |
| BALANCED_BOUNDARY_FAR_PAIR_AND_OPPOSITE_PORT_ORIGIN_STRIP.md | 72a915beaee37b435d993c6e77bd9833d717479b7b07ac014783d764cffa8605 | Complete Section 1 far-pair proof only; its old opposite-port strip and support-normal criterion are not premises |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 | Complete original graph/load domains, true degrees, physical refinements and graph-preserving reflection |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Complete same-nine lower-window join and the literal R>2 export used for the optional uniform numerical margins |

All four direct input pins match the current files. I read the entire
new source, the complete four-boundary-path proof, the full balanced-three
metric source underlying the far-pair theorem, the complete original H4
pocket/load source, the complete inner-pentagon graph/load cover and the
same-nine lower-window assembly. The accepted analytic measure components
retain their own full reviews; this review does not claim a fresh audit
of each independent measure calculation or an unrelated global prerequisite.

I also read the complete earlier independent review of the balanced
far-pair source. Its older strip proof is not transferred to the new
whole-square theorem, which is independently checked below.

## 2. The single review clarification

The initially submitted source was pinned at

    3c5a380f47496ba9213f7b7018dcc88440c66a681668f3d09aaf0ae940aabba5.

Its Section 6 additionally attributed a long-port conclusion at the
newly selected far pair to the old occupied-pocket/long-port source.
In the three-load family the old metric alternative can select a
different endpoint pair from the angular alternative used here.
The attribution therefore needed an additional same-pair comparison
if it was to be retained.

I pointed out this distinction. The author removed the incidental
claim and now states expressly that the pair is selected by the actual
angular alternative just proved and that no lower port-distance bound
enters this join. The uniform strip margins use only the diameter
upper bound |P-Q|<=sqrt(2) on the common actual D square.

I checked the revised paragraph. Reversing only that paragraph
reproduces the initial source hash. Neither whole-square theorem, its
proof, the selected angular pair, the original domain, nor the optional
numerical strip margin changed. The current source at the Section 1
pin is the reviewed version. Any future use of long ports at this same
angularly selected pair must supply its own exact comparison.

## 3. The full actual-point cone is proved without a contact hypothesis

Let sigma=1/sqrt(2). Every closed unit square of any orientation is
contained in the closed radius-sigma disk about its actual center.
The new theorem assumes only that both center radii are at least 5/4
and their minor angle has the specified lower bound. It does not need
the units to touch a circle, a force system, a chosen support normal,
a selected port or even their interior-disjointness for this local step.

For every P in C,

    |P|>=|c_C|-sigma>1/2,
    P.c_C>=|c_C|(|c_C|-sigma)>0.

Thus P is nonzero and the minor angle delta between P and c_C is
strictly below pi/2. The distance of c_C to the line OP is at most
|c_C-P|<=sigma. Hence

    sin(delta)<=sigma/|c_C|<3/5,
    cos(delta)>4/5.

Both strict inequalities remain true when |c_C|=5/4. The positivity
of P.c_C is essential: it chooses the acute cone rather than the
supplementary sine branch. It has been proved explicitly.

Writing gamma for the minor center angle and phi for angle(P,c_E),
the angular triangle inequality gives phi>=gamma-delta. Here
gamma-delta>0 and both sides belong to [0,pi]. Cosine is decreasing
on precisely that interval, so

    cos(phi)<=cos(gamma)cos(delta)+sin(gamma)sin(delta).

The cases delta=0 and gamma=pi are retained. No orientation of P
within its cone, no sign of its transverse coordinate, and no physical
point type has been selected. This establishes the common estimate
simultaneously for every vertex, side point, interior point and mean.

## 4. Entire qualitative theorem and strict boundary cases

Under gamma>=acos(-3/4), gamma is in the second quadrant or at pi.
Therefore

    cos(gamma)<=-3/4,
    0<=sin(gamma)<=sqrt(7)/4<2/3.

The sine bound uses monotonicity on [pi/2,pi], not a bound valid only
at the left endpoint. Its strict final comparison follows from
7<64/9. Multiplying the negative cosine by cos(delta)>4/5 reverses
the relevant inequality in the required direction. The complete
estimate is consequently

    cos(phi)<-(3/4)(4/5)+(2/3)(3/5)=-1/5.

Put u=P/|P|. For every Q in the other actual unit,

    u.Q<=|c_E|cos(phi)+|Q-c_E|
       <-|c_E|/5+sigma
       <=-1/4+sigma<1/2.

Together with |P|>1/2 this gives

    P.(P-Q)=|P|(|P|-u.Q)>0.

The symmetric calculation interchanges C and E without changing any
hypothesis and gives Q.(Q-P)>0. In particular P=Q is impossible,
so normalization by |P-Q| is legitimate. For e=(P-Q)/|P-Q|,

    e.P>0, e.Q<0.

These are exactly the strict inequalities saying that O's perpendicular
projection onto the line PQ lies inside the segment. No continuity
argument at gamma=acos(-3/4) or |c|=5/4 is needed; the proof is
strict there already because sigma<3/4. The origin itself cannot be
one of the points because their norms exceed 1/2.

## 5. Entire quantitative theorem and uniform chord margins

Under gamma>=acos(-4/5), the same full second-quadrant argument gives
cos(gamma)<=-4/5 and 0<=sin(gamma)<=3/5. Thus

    cos(phi)<-16/25+9/25=-7/25,
    u.Q<-(7/25)|c_E|+sigma
       <=-7/20+sigma<2/5.

Combining with |P|>1/2 proves

    P.(P-Q)>|P|/10,
    Q.(Q-P)>|Q|/10.

The strict 1/10 margins are uniform in both center radii, all unit
orientations and every actual point of both units. Center radii can
be arbitrarily large; replacing their lower bounds in the negative
projection terms only weakens the estimates. The proof imposes no
upper-radius condition. The closed angle and radius endpoints are
included for the same reason as in Section 4.

If P and Q also lie on one actual unit U, its diameter gives
0<ell=|P-Q|<=sqrt(2). Rotate about the unchanged origin to put the
actual chord in the form Q=(-L,h), P=(T,h). The proved scalar
products give exactly

    L,T>0, L+T=ell,
    L>|Q|/(10ell), T>|P|/(10ell).

No translation of the containing-circle origin is made. The sign of
h is free; the theorem has proved a projection strip, not the side
of the chord on which O lies.

For a physical boundary unit, any actual circle corner Z and any
point P of that same square give |P|>=R-sqrt(2). Therefore, for
R>=2,

    L,T>(R-sqrt(2))/(10sqrt(2))
       >=(sqrt(2)-1)/10>1/25.

The last strict comparison is sqrt(2)>7/5. The radius lower endpoint
R=2 is valid. This optional conclusion uses the diameter upper bound
on the port distance; no positive lower bound on that distance is
required. It includes every endpoint-valued original shared mean.

## 6. Every original physical boundary mask supplies the center premise

A physical circle corner is at distance exactly sigma from its own
center. Hence |c|>=R-sigma. Throughout R>=79/40,

    sigma<29/40,
    |c|>=R-sigma>5/4.

The exact squared reserve for sigma<29/40 is 41/1600. Thus both
whole-unit theorems apply whenever the caller supplies the relevant
minor center-angle bound. A corner is used because it is physically
on the circle; its selected coefficient need not be positive.

The conclusion therefore retains a physical two-corner unit with one
coefficient zero and every possible choice of nonnegative coefficients
with positive total weight. It also applies to a physically boundary
unit with zero total load when the center-angle hypothesis is supplied
in another way. No loaded-degree-two equation enters this implication.

## 7. Complete four-load H4 application

The original graph is exactly

    HA,HB,HC,HD,AB,BC,CD,DE,EA,
    (A,B,C,D,E)=(0,1,2,3,4).

The true degrees are H4, A3, B3, C3, D3 and E2. In L0124 the
positive circle loads are precisely A,B,C,E; H and D are unloaded.
The original component is entire, so summing all its complete force
equations cancels each pair force and gives

    F_E+F_A+F_B+F_C=0.

The four distinct physical boundary units have the actual path
E--A--B--C. The full four-boundary-path theorem applies to their
positive total circle weights, including every individual zero corner
coefficient. No equation at A, B or C is replaced by a two-force one.

I checked the full strict angle deduction in that theorem. Every real
circle corner and hence every actual resultant is strictly within
pi/12 of its own center. Physical angular-neighbor contacts order the
four centers and their resultants on the path. The closing resultant
gap is less than pi by their full positive balance, so the directed
endpoint center span is greater than 5*pi/6.

For the complementary bound, actual touching centers have distance at
most sqrt(2), both radii exceed 5/4, and each consecutive angle is
less than theta=acos(9/25). The exact triple-angle comparison gives
3*theta<7*pi/6. Thus whichever side of pi contains the directed
span, the actual minor endpoint angle is strictly greater than 5*pi/6.
This is the minor angle needed by the new theorem, not just a chosen
directed angular lift. The physical angular-order source's center
separation exceeding pi/5 already suffices to keep the two pi/12
correction intervals disjoint in this argument.

Since cos(5*pi/6)=-sqrt(3)/2<-4/5, the quantitative whole-unit
theorem applies to C and E. For every pair P_C in D intersect C
and P_E in D intersect E, it gives the original chord strip and
its scalar-product margins. Their common membership in D supplies
the diameter upper bound. The optional numerical margin follows
from the same-nine R>2 theorem, with all three extras retained.

This covers complete physical contact sets. It requires neither a
singleton CD/DE feature nor any particular original HD owner.
Positive shared segments, their full mean intervals, free normals,
D-owned sides and externally owned sides are all retained. Coincidence
of the third application with one return application is irrelevant to
this proof; it does not assume their distinctness. The two return
applications themselves cannot coincide by the proved strip theorem.

## 8. Complete selected-far-end application in the three-load family

In L124 the loaded bodies are exactly B,C,E. The full component
force sum is F_B+F_C+F_E=0, and BC is an actual contact. A and D
are unloaded true degree three; H remains unloaded true degree four.

The complete balanced-three source gives center radii in
(19/15,91/60), every resultant within pi/12 of its center, the same
circular order for the three directions, and every directed center
gap strictly less than 7*pi/6. I checked these actual-mask statements
in its full Sections 2--3; none assumes an endpoint degree.

For completeness, the operative far-pair proof is as follows. The
actual BC minor gap g is below theta=acos(9/25). It must be a
consecutive gap: if it contained the E direction, the complementary
directed gap would exceed 2*pi-theta>7*pi/6. If both minor E
endpoint angles were at most alpha=pi-theta/2, any major directed
gap would be at least pi+theta/2>7*pi/6. A directed gap of exactly
pi is also incompatible with that minor bound. All three consecutive
gaps would therefore be minor and have total at most
g+2*alpha<2*pi, a contradiction.

Thus one actual pair CE or BE has minor angle greater than alpha.
The exact half-angle value is cos(alpha)=-sqrt(17)/5<-4/5. This
is sufficient for the new quantitative theorem, with no use of the
old opposite-port strip in the same source.

The reflection i -> 3-i modulo 5 exchanges A,D and B,C, fixes E
and H, preserves the spoke set and every rim edge, and preserves
the complete load set {1,2,4}. If the selected pair is BE, reflect
the whole physical configuration, all normals, applications and loads.
That selected pair is then called CE and its intervening unloaded
end is called D. The theorem is applied to that same angularly
selected pair throughout. It does not assign a far bound to both
ends or transfer an owner assumption from the unselected end.

All actual CD/DE points now obey the complete strip and optional
uniform numerical margins. In particular the result remains valid
when the other unloaded end A is physically circle-clear. A's boundary
status is not used, and no proper concurrence at the true E2 is
invoked. Physical zero-weight contacts and the original H--E
closed-disjoint restriction remain as in the complete graph domain.

## 9. Current upstream pins and precise acceptance boundary

The additional current sources read at the operative scopes above are:

| Source | SHA256 | Use in this review |
| --- | --- | --- |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Entire proof read; actual radius, resultant-deviation, order and directed-gap statements checked for the far-pair input |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Entire original load cover read, including the precise four-spoke no-chord row, reflection and H--4 physical noncontact |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Complete current physical angular-neighbor and center-separation proof read |
| REVIEW_BALANCED_FAR_PAIR_OPPOSITE_PORT_STRIP_H4_INDEPENDENT_2026_10_28.md | 0b12724894db809969aac2777508bdeed669e0cd6d9fc4da4249fc9f1cca0814 | Earlier full independent review read after checking the operative arguments; no old strip hypothesis imported |

These current pins also match. Historical terminal-LF variants in older
review records remain separately reconciled; they are not substituted
for the current files listed here.

The accepted new export is simultaneous strict origin straddling for
every pair of actual points of the two units, with the quantitative
margins under the stronger angle condition, and its two literal H4
consequences. It does not determine the signed chord height, the
normal slopes, a circle mask, whether O lies in D, whole-extra
clearance, or a pocket capacity. Those require further actual geometry
and complete original equations.

No original H4 fine row, graph parent or coarse cell is closed. No
computational exclusion certificate is introduced or retired by this
necessary restriction alone. Every original unit, true degree, selected
normal, force, torque, physical corner and full side mean remains.
No Lean/Lake, CI, workflow, pose mesh, certificate execution, ledger
mutation, commit or remote write was used in this review.
