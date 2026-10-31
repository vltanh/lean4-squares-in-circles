# Independent full review of the high-corner central/top-page theorem

Date: October 27, 2026.  
Reviewer: cert_final_review.  
Original comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

## 1. Verdict, exact target, and review scope

**PASS of the complete local theorem and all fifteen source sections.**
Every physical contact type, actual shared mean, central offset,
permitted CK owner, and continuous angle interval is covered. No
mathematical correction is requested. The result needs no force law at
H or K and introduces no computational certificate.

The unchanged exact target is

`HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md`

with SHA256

`580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b`.

It has 22,756 bytes and is saved under
`recovery_2026_10_27/research/nine/`. This is a fresh new source after
the workspace rollback, not a claimed restoration of older bytes.
I independently read its complete current bytes, recomputed the target
hash and length, and read all five complete direct original inputs.
All five prerequisite hashes match the target's table exactly.

Unlike a recovery review with unavailable newer prerequisites, this
local theorem has a complete present direct dependency bundle. Its
references to recent high-side work are explicitly provenance only.
Every needed geometric and scalar argument is reproduced in the
target. The theorem's intended original callers still have their own
chart and original-domain obligations; those callers are not accepted
merely by accepting this helper.

I independently reconstructed all support, force, and proper-line
arguments before checking the fixed arithmetic. A separate exact
sparse-polynomial/Fraction calculation verified thirty-one identities
and thirty rational values or reserves. It did not call the author's
checker or use sampled configurations, numerical optimization, a
symbolic-algebra package, Lean, or CI. The continuous argument is the
hand proof in the source, not an interval-box certificate.

I did not contribute the new high-corner proof. My earlier orthogonal
and free-central work supplied some motivation for its shared-contact
norm comparison. Before this target was frozen, I also warned against
using a nonexistent B-C edge in an original caller and confirmed the
need to keep the extra negative K axis. The target's complete proof
uses only the actual H-K-C triangle and independently retains that
axis. My audit below covers the entire new theorem, not just those
previously discussed portions.

## 2. Full local hypotheses and actual certificate convention

The theorem has three pairwise interior-disjoint contained unit
squares H,K,C. K physically touches the circle, with arbitrary degree
and arbitrary physical circle mask. C has a unique physical circle
corner, a positive circle load, and precisely the two genuine positive
pair forces HC and CK. H has arbitrary other contacts and forces.
No additional packing square is removed by this local contradiction.

The unchanged origin-centered coordinates are

    H=[h-1,h] x [G-1,G],
    -1/60<h<=0, 89/120<G<1,
    R_0=(h,G),
    U=(c,s), V=(s,-c), c,s>0, c^2+s^2=1,
    K=R_0+[0,1]U+[-a_0,1-a_0]V, 0<=a_0<1.

The actual central normal N satisfies N.U>0 and N.V>=0.
For a K-owned side contact it is U. The free central endpoint a_0=0
is also retained. The theorem does not quietly exchange the two
offset endpoints or alter N after extracting the stress.

HC is genuinely owned by the top side of H in direction E2. A
singleton HC is therefore a strict lowest vertex of C at a relative
interior point of that H side. A shared HC keeps its actual mean
throughout its complete physical segment. A point-only vertex/vertex
contact with a strict normal is not relabeled as this owned side.

If both page contacts are physical singletons, the theorem explicitly
assumes the already compatible fixed-point normal selection, or the
equivalent actual owner premise in an application outside that
certificate framework. This is a legitimate stated hypothesis, not a
new normal choice in the proof. The shared CK branch is proved
geometrically with every actual mean intact.

## 3. Section 2: true C2 concurrence and physical K corner cover

The boundary-neighbor version of proper concurrence applies at C
because K touches the circle. Since C has a unique physical circle
corner, its actual concurrence belongs to C and has the form

    q_C=r z_C=T+ell E2,
    Z-q_C=ell_K w,
    0<r<=1, ell,ell_K>=0.

The upper bound r<=1 follows from the actual unique corner's two
own coordinates; a positive radial dilation beyond that corner is
outside the square. This remains valid at all actual mean endpoints.
The proof uses no proper ray or two-force law at K.

Both minimum-U K corners are at distance at most one from R_0,
and |R_0|<61/60. Their norms are below 121/60, strictly below
the full radius lower bound. The exact squared reserve is 659/3600.
Thus only the two actual maximum-U corners K_1,K_2 can touch the
circle. This is a physical two-corner cover, not a claim that one of
them is the unique K circle corner.

## 4. Section 3: the entire shared HC normal cone and both K corners

For shared HC, C=[l,l+1] x [G,G+1] and the original mean
T=(x_0,G) has h-1<=x_0<=h<=0. A lower C corner cannot be a
circle point because its corresponding upper corner is farther from
the origin. Proper concurrence makes the actual circle's horizontal
coordinate have the sign of x_0. The unique physical corner cannot
have a zero own coordinate, so the x_0=0 endpoint is excluded by
the real circle geometry. The circle is C's upper-left corner.

The actual C force gives w_x>0. The actual H-K-C side-normal
theorem, used at C's CH side, gives w_y<=0. This is the entire
relevant normal cone, including the horizontal boundary.

For w_y=0, K's actual minimum support is S=R_0-a_0V, which
forces l+1=h-a_0s. For w_y<0, the C application is its actual
bottom-right corner at height G. K's complete support cover is S,
S+U, or the whole tied side S+[0,1]U. Every such point has height
at least G+a_0c. For a_0>0 this is impossible. At a_0=0 only S
can have height G, again giving the same actual support identity.
Neither an arbitrary shared mean nor a tied K face is discarded.

The actual C circle is consequently

    z_C=(h-a_0s-1,G+1).

I expanded both differences |z_C|^2-|K_i|^2. The two displayed
quadratics in a_0 are exact and concave on the entire closed interval
[0,1]. Both are positive at a_0=0. At a_0=1 the first is strictly
greater than the positive expression (1-c)(3+c), and the
second is manifestly positive. The negative coefficient
1-s-c is handled in the correct direction using G<1. The h=0
boundary is retained throughout.

Concavity therefore proves that both possible K circle corners are
strictly inside the radius of C's actual circle point. The other two
K corners were already controlled. This excludes the full shared HC
branch without using any K force law or selecting a K circle mask.

## 5. Sections 4--5: the complete singleton C circle and support chart

For singleton HC, the strict actual H-side application is
T=(-z,G), with z>0 and 0<z+h<1. The actual C axes are
e=(-q,p), f=(p,q), with p,q>0 and p^2+q^2=1.

All four possible C circle corners are considered. T itself is
already shared with H and cannot touch the containing circle.
The opposite corner is excluded using the actual proper ray:
r>=G/(z_C)_y and r<=1 imply

    2=|z_C-T|^2< (161/120)^2<2.

The last squared reserve is 2879/14400. The norm comparison is
legitimate because every coefficient being bounded is nonnegative;
the proof does not replace a signed component by its absolute value
without checking the sign. The adjacent corner T+f has a positive
minimum-e coordinate, so it also cannot be a containing-circle
corner. Thus the actual unique circle is T+e.

Its own coordinates are A+1 and -B, where

    A=Gp+zq>0, B=zp-Gq>1/2.

The exact radius identity gives A<d. The unchanged proper ray has

    q_C=[z/(z+q)]z_C, ell=B/(z+q)>0.

In particular the two C applications cannot coincide. The existing
fixed-singleton selector is therefore used only at two distinct
actual physical singleton applications. The radial-D coincident
exception has been ruled out geometrically, and no shared-side mean
is treated as a fixed point.

The inequality G<dp-q/2 excludes q>=39/100 on its whole interval.
Both rational radical replacements have the correct signs and give
the strict height reserve 19/60000. Hence p>23/25. The exact
expression

    F=z(p-q)-Gq-q^2
      =B(1-pq)-(A+1)q^2

has the uniform lower bound J(q)>J(39/100)=52379/4000000.
The derivative of J is strictly negative over the entire interval,
as claimed.

The actual transverse C force gives w.f>0. The three possible signs
of w.e therefore exhaust every actual C support: T+f, T+e+f,
or the full side T+f+[0,1]e. In the first case the actual proper
displacement is

    (T+f)-q_C=(p,-F/(z+q)),

which is strictly rightward and downward. This is the real contact
line and will determine the actual K slope; no auxiliary line is
substituted.

## 6. Section 6: every C-owned CK, including all shared means

The only C-owned axis allowed by w.f>0 is w=f. Its U component
is strictly positive. If its V component is negative, its K support
is R_0+(1-a_0)V, strictly below G, and it cannot meet C.

If its V component is nonnegative, equality of the two actual
supporting lines gives

    p(z+h)=1+a_0(ps-qc)>=1.

The actual interval 0<z+h<1 and p<1 make the left side smaller
than one. This contradiction also covers the whole tied K face
when f.V=0, and therefore every actual mean on a shared CK.
No angle subdivision or stronger owner convention is needed.

## 7. Section 7: all three permitted K-owned CK axes

At K the only legitimate triangle sign is w.N>=0. The source
uses the physical triangle H-K-C, with K-owned CK. Because
N.U>0 and N.V>=0, the complete remaining axes are U,V,-V.
The extra -V row is explicitly retained; no sign is inferred from a
nonexistent B-C edge or from an unrelated BK normal.

For w=U, a positive e component makes the C application higher
than G+1, while the entire K support side has maximum height
G+a_0c<G+1. A zero e component is the already excluded physical
C-owned/shared axis. A negative e component contradicts the actual
strictly downward proper displacement. Thus every U feature is
covered.

For w=-V, the e component is strictly positive. If the f component
is nonpositive, the actual C force has already excluded it. Otherwise
the C support is again above G+1, while K's entire maximum-V side
has height below G+1. This closes the extra axis over its full
original side position.

Only w=V remains. Its C application is exactly T+f, at the actual
K side point S+zeta U. Projection gives the exact two equations

    zeta*s=q-a_0c,
    z+h=p-(c/s)q+a_0/s.

The original strict singleton side position is kept, and subsequent
upper estimates harmlessly retain its closed endpoints. The real
proper-line slope is exactly

    k=c/s=F/[p(z+q)].

Its denominator is positive. The identity
p(z+q)-F=q(z+G+p+q)>0 proves 0<k<1 and c<s.

## 8. Section 8: the entire actual offset and the first maximum-U corner

The actual relative-interior H-side inequality gives

    a_0<q[c+s*q/(1+p)].

Since q/(1+p)<13/64 and c<s, the bracket's full angular function
is increasing up to c=1/sqrt(2). The resulting strict bound is

    a_0<3003/(6400sqrt(2))<1/3.

The final positive integer reserve is 757919. Every quantity squared
is positive. This restricts the actual original offset; it does not
choose a smaller representative of a contact side.

The first possible K circle corner has norm bounded by
|R_0|+sqrt(1+a_0^2). The source's exact rational upper bound
3703/1800 is below sqrt(17)/2 with reserve 57791/3240000 in
the squared comparison. Thus K_1 is strictly inside the disk.
Only the actual K_2 corner remains to be controlled.

## 9. Section 9: the complete k<=1/10 assumption is impossible

The actual support identity, a_0>=0 and h<=0 give
z>=p-q/10 under k<=1/10. The proof then covers the two complete
q intervals, rather than selecting a favorable representative.

For 1/3<=q<39/100, the exact radius is bounded below using
p>1-25q^2/48. I expanded the resulting cubic P(q) independently.
Its second derivative is negative throughout the entire interval.
Both endpoint excesses over 1105/256 are positive:

    33287/518400 and 4671227/72000000.

Concavity supplies a lower bound by the smaller endpoint value.
This is the correct direction for the radius contradiction.

For 0<q<1/3, the proof solves the unchanged slope identity for G.
The coefficient of z is positive before z is bounded below; its
lower bound exceeds 219/500. The expression decreases with k.
Substituting k<=1/10 and the actual lower z bound gives the exact
intermediate expression

    9/(10q)-(9/5)q-(119/100)p.

Using p<=1-q^2/2 has the correct sign because its coefficient is
negative. The resulting rational function decreases on the whole
interval and is at least 1757/1800>39/40 at its right endpoint.
Combining this with the actual circle equation and p>14/15 exceeds
the permitted radius with reserve 2263/11520.

Both intervals are therefore impossible. The equality q=1/3 is
included in the first interval, so no gap is left. The theorem has
proved k>1/10 on the entire original remaining row.

## 10. Section 10: the high-G part of the smaller-slope interval

For k<7/20, the actual support equation implies z>p-q/2.
Assuming G>=17/20, the exact C radius is bounded below by the
displayed quadratic B(q). Its derivation uses the exact p^2=1-q^2
before separately bounding the positive linear p and pq terms.
The result is

    B(q)=1769/400+(23/25)q-(253/96)q^2.

It is concave on the whole closed interval [0,39/100]. Both endpoint
excesses over 1105/256 are positive, 679/6400 and 4099/64000.
Thus the proof establishes the uniform implication

    k<7/20 implies G<17/20.

No value of the actual central offset, C mean, or original contact
force is suppressed to obtain this implication.

## 11. Section 11: all remaining K corners are inside the disk

Set t_0=1-a_0 in (2/3,1]. The remaining actual corner is

    K_2=(h+c+t_0s,G+s-t_0c).

Both coordinates are positive before h and G are replaced by upper
bounds. The first is greater than 2/3-1/60; the second is greater
than G because c<s. Consequently the squared-norm comparison has
the claimed direction and gives

    |K_2|^2<1+t_0^2+gamma^2+2gamma(s-t_0c).

For either allowed gamma, this is convex in t_0 on the entire
closed interval [2/3,1], so both endpoints suffice for an upper
bound. For each fixed positive t, the function

    (1-tk)/sqrt(1+k^2)

has derivative -(t+k)/(1+k^2)^(3/2), strictly negative. Its
use at both ends of each full slope interval is therefore valid.

For k>=7/20, gamma=1 gives both endpoint bounds strictly below
17/4. For 1/10<k<7/20, the already proved gamma=17/20 gives
the strict endpoint reserves

    43/10000 and 1787/3600.

The radical comparison 9/sqrt(101)<112/125 has positive squared
reserve 1319/1578125. The higher-slope radical comparison has
reserve 409/28736. All endpoints and strict inequalities are
handled consistently.

The two minimum-U corners, K_1, and K_2 are now all strictly
inside the containing disk. By convexity of squared norm, every
point of the actual square K is strictly inside. This contradicts
its physical boundary contact, independently of K's degree, circle
mask, or other forces.

## 12. Complete scope and original-caller obligations

The proof includes both physical HC types, every actual mean on a
shared HC, the a_0=0 endpoint and h=0 boundary, all singleton C
circle possibilities, every C-owned or shared CK, all permitted
K-owned CK axes, and the full remaining central offset and slope.
No K2 or H3 equation appears. No circle corner of K is chosen for
convenience: the proof bounds all four actual vertices.

The source's original-domain transfer discussion is correctly
conditional. In the stated B-owner chart, reflection of the first
H-frame coordinate maps the transverse K axis to minus V. The
actual offset is therefore a_0=1-rho, not rho. The map is
origin-preserving, so it does not change the containing circle or
the genuine radial force lines.

A caller must still establish h<=0, the strict G window, actual
central geometry and normal cone, genuine unique C2 law, and the
fact that HC is the H-owned top side. An oblique page from the
opposite upper root corner is outside this theorem. The unrelated
H-owned-HB northwest chart does not automatically inherit h<=0
from a theorem for a different central feature.

These are explicit original-caller obligations, not omissions in the
local result. No entire original hub-tip gate or ledger row is closed
by this helper review alone.

## 13. Exact reconstruction and input pins

The independent expansion record checked both complete shared-HC
norm differences and their endpoint forms; the actual C coordinate
rotation, radius and F identities; the full proper displacement and
actual support/offset equation; both complete low-k comparison
polynomials; the high-G quadratic; the final K norm and derivative
identities; and the exact reflection offset. Thirty exact values and
reserves include all final inequalities and the decisive radical
comparisons. These checks support, but do not replace, the full
geometric argument reviewed above.

All five complete direct original sources are present, were read in
full, and were independently rehashed:

| Complete source | Verified SHA256 | Scope checked |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual physical normals, strict singleton owner convention, complete force and moment aggregation, unchanged shared means |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Boundary-neighbor proper C2 lemma, unique-corner interior concurrence and positive radial sign |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Complete unique-circle normal-line calculation, strict own-coordinate facts, and the impossibility of sharing a containing-circle point |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Only the actual H-K-C side-owner signs, with zero dot products retained |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing compatible selection at two distinct fixed physical C2 singleton applications; no selection on a variable shared mean |

The exact target hash was checked both before and after this review.
No target bytes, earlier accepted bytes, ledger, remote source, Lean
file or CI workflow were changed. The complete local theorem is
accepted with zero new computational certificates.
