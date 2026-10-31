# Independent review: the entire S123 opposite-vertex owned side and its exact scalar cover

Date: October 27, 2026.
Reviewer: rooted_blocks, independently of the author.

**Result: ACCEPTED in full.** The original owned-side feature, its exact
finite rational scalar certificate, the local loaded-middle theorem,
and the final opposite-root-vertex assembly all pass. No correction is
requested. The scalar step is a complete finite rational cover; this
review does not describe that step as a short hand inequality.

## 1. Exact sources read and independently checked

I read the complete frozen sources and checker:

| Source | SHA256 |
| --- | --- |
| S_LEAF_C5_THREE_LOAD_OPPOSITE_ROOT_OWNED_BOUNDARY_SIDE_EXCLUSION.md | df3ce3f249533c1ffce206c64a2fd0d76beb205f63609f42cca6b187760e3837 |
| S123_OPPOSITE_OWNED_BOUNDARY_PORT_SCALAR_CERTIFICATE.md | 68b1fe0c41673ade16831afe54cc4f2534f7c630c342734c341bca97a650be6e |
| certificates/s123_opposite_owned_boundary_port_certificate.py | 8df8d227170e6d20fcd567fc461e1922ede1a4894b0d7396c3ac0b55fc3eecb0 |
| RADIAL_BOUNDARY_UPPER_CONTACT_LOADED_MIDDLE_SHORT_PORT_EXCLUSION.md | 4497b0c781a518ff6c04e92fe8f7b0b121965a740c14ccb1a56864c7754d8106 |
| S_LEAF_C5_THREE_LOAD_OPPOSITE_ROOT_VERTEX_COMPLETE_EXCLUSION.md | b448ef15567a80e7ed3416a5820bc2befb21918234e53c3723cd560472f322da |

I also re-read the complete current radial-root half-plane source
b64691f7 and checked its direct original-channel scope, including its
separate t=0 mean. The sharp physical contact-radius theorem is the
complete c0375a27 source already independently checked in this chain.
The full true loaded-degree-two proper-concurrence prerequisite retains
both physical boundary neighbors and was checked at every invocation.

The complementary strict-B-vertex source c057680a already passed my
complete independent review52eb9b1f. I checked its exact scope again
when reading the final two-owner assembly.

## 2. Full original graph and physical B mask

The actual graph remains A--B--M--C--U--A with its genuine S leaf
at A. The true A3 equation, the positive circle loads on B,M,C,
the actual unloaded side U2, and all three additional physical units
remain. No S13 contraction or artificial B--C edge appears.

For t>0, the original channel support at(d-a,-b), together with
both strict negative world components of n, gives epsilon<b.
For t=0, the actual db=2sqrt(epsilon) identity gives the same bound
without imposing the strict-channel vertex formula on its free original
mean. Thus the actual opposite A vertex P has norm<1. In particular
it cannot belong to a physical radial two-corner B, whose points all
have norm at least d>1. B is physically unique before any inside-unit
concurrence conclusion is used.

I independently computed det(m,P)=q(a-b) divided by the positive
normalizing factor. Its strict positivity fixes the j sign of the
actual circle corner. The complete B box, original lambda and eta,
and its actual shared mean follow exactly. The lower bound H>1/2
is valid even for A0<0: use p<=1 to obtain
H>[(37/50)-(1/60)]/sqrt(2)>1/2.

The statements S>W,0<eta<1 and0<=lambda<eta<1 are all justified.
The eta=1 endpoint would make P a unit distance from the real circle
corner, contradicting |P|<R-1. The exact lambda identity excludes
eta=0 and proves the strict difference lambda<eta. This retains the
incoming proper-length endpoint lambda=0 while proving that all
outgoing proper lengths in the actual return cover are nonzero.

## 3. Every scalar guard is derived at its original scope

The incoming properness yields RH<=|P|(H+1). With |P|<1 it gives
H<1/(R-1)<33/35. I checked the exact critical-radius comparison
17/4-(68/33)^2=17/4356.

For p<=13/40, the norm estimate uses the retained F0 term:
|P|<F0+1/5000, so F0/|P| is bounded below rather than replaced
by one. The resulting H/|P| estimate and the exact squared reserve
4845994921/4928400000000 force |P|/H<53/50. This contradicts
R<=|P|+|P|/H<103/50. Thus the lower ratio bound used by the
closed scalar box is valid.

I re-derived t/x=b(1-p)/[p(a-b)] in the strict-channel case.
The elementary positive-squaring bound on a gives the stated rational
majorant vbar. Its denominator is positive on the entire enlarged
box. For t=0 the actual rotation ratio is zero, and only the inequality
0<=t/x<=vbar is used. The genuine original channel mean is never
replaced by the strict-channel formula.

The full B2 equation gives negative j component for its outgoing
normal. Near vertex, owned -j side with its forced mean, and far
vertex are therefore the complete actual support cover. I checked each
point and direction formula. The strict lambda/eta inequalities exclude
no physical owner endpoint; they ensure the displayed direction vectors
are nonzero. Both remaining normals have positive first and negative
second A-axis coordinates, with downward slope at least p. Hence the
strict scalar vbar<p transfers their signs to the actual channel frame.

## 4. Independent audit of the integer interval proof

The certificate begins with a closed rational box containing every
actual scalar tuple. I checked every interval operation in the supplied
checker. The lower/upper multiplication rules use all four endpoint
products. Reciprocal endpoints round outward for a proven-positive
divisor. The square operation handles a zero crossing. Integer square
roots and the exact square test provide outward square-root bounds.
No floating-point arithmetic is imported or used.

Every discard is a literal impossibility under the displayed guards.
The strict tests H<=1/2,z<=0 and A^2+F^2>=1 match the actual
strict hypotheses. Intersections with the closed H,lambda,eta ranges
retain all actual endpoints. After H is bounded above by33/35, the
W radical is strictly positive, with exact reserve2329/4900.
Unresolved divisors lead to subdivision, never to a discard.

For the near return, I independently proved the automatic W<=1
restriction from the sharp physical contact radius. The exact identity

    (H+W)^2-(V-1)=2H(W-1)

is valid, and H>0. The additional H>=sqrt(13/4)-1 intersection
follows from S^2=V-W^2>=V-1. Equality W=1 remains. Intersecting
these necessary intervals may lose correlation but only enlarges the
enclosure of the actual point; it cannot remove a valid star.

The optional return discard compares an upper norm enclosure to a
lower enclosure of the smallest possible sharp contact radius. Its
inequality is therefore conservative in the correct direction. The
four rotated-coordinate tests use positive Q1,Q2 and monotonicity of
(Q1-vQ2)/sqrt(1+v^2), together with valid full-interval upper and
lower bounds on the second coordinate. They cover every original
0<=v<=vbar, not one selected direction.

The input bisection uses exact rational midpoints. Both closed children
are kept, and the largest weighted-width/tie rule matches the manuscript.
Thus the final binary tree covers the entire initial closed box. Running
the supplied checker reproduced every stated item exactly:

    accepted2833, impossible37, splits2869, maximum depth18;
    depth counts1,2,4,8,16,32,56,104,166,288,348,378,528,764,
                808,678,750,642,166.

The terminal identity is2870=2869+1. All six published enclosure
numerators and all six strict rational reserves also reproduced exactly.
No unresolved leaf is accepted or omitted.

## 5. A separately implemented exact arithmetic audit

I additionally wrote and ran a separate checker:

    certificates/review_s123_owned_boundary_port_independent.py
    SHA256 bf2a9265fd46076ebe0a225bfcd68b97542719d3b42378c73c07a7b500afa8fa.

It imports none of the author's interval implementation. Its ordinary
operations use exact Fraction endpoints without lattice rounding;
only square roots are enclosed, on the different and finer2^-48 lattice.
It reconstructs the complete closed-box cover, guard intersections,
feature discards, far support and all-direction return tests from their
mathematical formulas. Its full run gives the same terminal/split counts,
maximum depth and depth distribution, with the following independently
rounded-down positive lower bounds on the strict margins:

| Strict margin | Independent exact lower bound |
| --- | ---: |
| h_far-61/60 | 99772695757/70368744177664 |
| p-vbar | 15848907960399/140737488355328 |
| Q_n-1/8 | 84209877/35184372088832 |
| 3/4-Q_n | 19683516971239/281474976710656 |
| Q_f-1/10 | 112488131637725/281474976710656 |
| 9/10-Q_f | 930723713/140737488355328 |

This independently verifies the finite exact-arithmetic certificate.
The geometric and force hypotheses were checked separately in Sections
2--3 above; executing either checker alone would not establish those
original-scope obligations.

## 6. Full local loaded-middle proof and literal caller

I read and independently checked the entire4497b0c7 local source,
including its two separately exported scopes.

For actual support points of one unit with obtuse outward normals,
a distance<1 is impossible. Its complete vertex/side cover includes
same points, actual side interiors, side endpoints, incident sides and
opposite sides. This is a physical statement and needs no M equation.
In the strict-inner radial C case, the actual normals have negative
dot product. The caller's weaker1/10<Q_f<9/10 still gives the
same strict2/5 transverse chord bound. Its exact squared upper bound
13753/14400 is below one by647/14400. Thus this caller uses the
stated chord export legitimately; it does not pretend that Q_f>1/2
was proved by the scalar certificate.

For the C-owned upper-side case, the local proof requires only
Q_f<9/10 and g_n>0>g_f. If M owns the transverse axis, its
actual minimum-g port is on the impossible height3/2. Otherwise
its strict minimum-f vertex and two actual inward axes exhaust the
frame. The support signs force the stated near-side feature and
s<2/5,c>9/10. Comparing all actual corners proves that M's sole
physical circle corner is its right-adjacent corner before using
its unique-corner radial concurrence. The unchanged C line then gives
q_M.f>1, whereas the original incoming B proper ray gives
q_M.f<=Q_f<9/10. All C-side means and zero proper lengths remain.
No circle-mask assumption has been applied prematurely.

The original full C2 equation supplies the local C normal signs for
both physical corner weights, including an individual zero weight.
A positive n component would expose an unshareable real circle corner.
The strict-inner and full upper-side cases exhaust the actual C support.
Consequently the far B return and both remaining B returns are all
excluded with the full original M load present.

## 7. Complete opposite-vertex assembly and remaining scope

I read the entire b448ef15 assembly. A nonowned actual B normal is
strictly inside its vertex cone under the original point convention;
a B-owned axis, including any actual side endpoint mean, belongs to
the owned row. These are exhaustive. The c057680a strict-vertex source
and the now accepted df3ce3f2 owned-side source both retain the full
strict-channel domain and the entire t=0 mean domain separately.
Their exact two-row join therefore closes the entire original tilted
radial-C feature m.f1>0.

The assembly's pending-review wording may now be updated to cite this
review, without changing its mathematics. The actual A-owned direct
side mean m.f1=0 and the remaining high aligned S123 cases stay open.
No whole S123 fine or coarse closure is inferred here.

All nine original units, true degrees, positive circle loads, physical
masks, individual zero weights, actual normals and genuine means remain.
No numerical pose, finite sample, normal reselection, force deletion,
Lean compilation, CI, shared-metadata edit or remote mutation is used.

## 8. Final accepted-status assembly readback

I read back the final assembly
S_LEAF_C5_THREE_LOAD_OPPOSITE_ROOT_VERTEX_COMPLETE_EXCLUSION.md at
SHA256 fac056764dff34462a743372e323cfba9d533171f91f450fe4ff2f4aa91dee9e.
I compared it with the reviewed b448ef15 text. The only changes are the
accepted-status header, the explicit reference to this full review and
its independent checker, and removal of the now-satisfied owned-side
review condition from the conclusion. No mathematical statement,
original-domain row, endpoint, source scope or remaining obligation
changed. The entire final assembly remains independently ACCEPTED.

