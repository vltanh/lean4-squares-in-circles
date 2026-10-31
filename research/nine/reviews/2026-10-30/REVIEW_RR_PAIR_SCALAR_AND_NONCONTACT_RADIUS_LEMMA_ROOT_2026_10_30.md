# Independent checks of the two contributed RR calculations

Date: October 30, 2026 UTC. Reviewer: root continuation.

**Accepted at the explicit scopes below.** I independently reconstructed
both calculations after reading the complete frozen sources and their
full review records. I did not contribute to their derivation. This
supplement resolves the disclosed contribution boundaries in those
reviews; it does not replace their complete topology, motion or caller
reviews and does not close a whole original mixed C7 mask.

| Reviewed source | SHA-256 | Scope independently reconstructed here |
| --- | --- | --- |
| RADIAL_RADIAL_TRANSMITTERS_CAN_SLIDE_OUTWARD_AND_CANNOT_FORM_A_CLOSED_TWO_BODY_BLOCKER_NETWORK_2026_10_30.md | 0fbcce339700b2d2e23fa30a516a64c2773e868b90ed60f695fcc93ac4cafff7 | Section 6's full continuous pair inequality and its exact Phi coefficient in Section 7. |
| RADIAL_RADIAL_TRANSMITTERS_HAVE_NO_NONCONSECUTIVE_BOUNDARY_CORE_CONTACT_2026_10_30.md | f87e7d86c332a8ba699311788a9eca0d0a2bf109db5e218aa54ff21274ceeb36 | Complete support/radius Lemma 2.1, including the side and vertex feature cover, both farthest-corner signs and the entire t interval. |

## 1. The pair inequality over its entire continuous domain

The hypotheses are R>2, d=sqrt(R squared-1/4)-1,
phi=atan(1/(2d)), a=-cos(4phi), s=sin(4phi),
H=(1+a+s)/2 and b_plus,b_minus>d-1/2.

The inequality 15/4>(29/15) squared has exact reserve 11/900.
Thus d>14/15 and both actual b values exceed 13/30.
Also d<61/60 gives tan(phi)>30/61>sqrt(2)-1,
where the last comparison follows from (91/61) squared>2.
So 4phi>pi/2. The upper tangent bound tan(phi)<15/28<1
gives 4phi<pi, proving a>0 and s>0 without a hidden angle branch.

The exact rational fourth-angle formula at tan(phi)=15/28 gives
minus cosine equal to 393119/1018081. Monotonicity of minus cosine
on (0,pi), and

    2*1018081-5*393119=70567>0,

give a<2/5. Since s<=1, H<=1+a/2. For
f(a)=(a+a squared/2)/(1+a squared), the derivative after multiplication
by its positive denominator has numerator 1+a-a squared. It is
strictly positive throughout [0,2/5]. Hence

    aH/(1+a squared)<=f(a)<f(2/5)=12/29
        <13/30<b_plus,b_minus.

The middle exact difference is 17/870. In the active transverse
axis case b_plus+a*b_minus=H, the actual motion
delta b_minus=-epsilon, delta b_plus=a*epsilon gives

    delta Phi=2epsilon*(aH-(1+a squared)*b_minus)
                     +(1+a squared)*epsilon squared.

Its linear coefficient is strictly negative by the just-proved bound.
This is the original squared-center quantity for the two actual units;
no independently recentered mean or replacement radius occurs.
The reflected case is identical. This verifies all of the contributed
scalar ingredient used in the separately reviewed complete motion.

## 2. The entire support/radius lemma

The square has minimum x=1/2, center y<=0 and an exposed contact
height greater than -1/10. At a vertex use the exposed vertex; at
a vertical side use its upper endpoint, which still exceeds -1/10.
The two inward sides then have exactly the complete parametrization
u=(a,b), v=(b,-a), a,b>=0 and a squared+b squared=1.
The side case is a=1,b=0. Write t=a-b and s=a+b.
The center condition gives -1/10<y<=t/2.

The own center projections are

    c.u=1/2+a/2+b*y>2/5,
    c.v=1/2+b/2-a*y>=(b squared+b+ab)/2>=0.

Thus the opposite corner p+u+v is indeed farthest, including the
two-corner equality in the second projection. Its norm squared is
(1/2+s) squared+(y-t) squared. The exact endpoint expansions are

    F(t/2)=9/4+s-3t squared/4,
    F(-1/10)=113/50+s+t/5.

Convexity in y bounds the whole allowed interval by those two values.
No positivity of t is required. Since -1<=t<=1 and s<=sqrt(2),
the larger uniform bound is 123/50+sqrt(2). Finally

    sqrt(2)<283/200,
    123/50+283/200=31/8,
    (79/40) squared-31/8=41/1600>0.

Therefore the entire square is strictly inside radius squared 31/8,
which is incompatible with being physically boundary in the original
radius window. This is a full feature and full interval calculation,
not a numerical check at selected orientations.

## 3. Independent literal joins at the disclosed contribution boundaries

I also read the entire current mixed shared-block source at
SHA-256 `e5761145e8f5f83fe4cfab2ddee8be20c75058ef25f8923cc052807a6f52ad77`.
Its construction explicitly covers a singleton shared block with
w=Jz and no internal work terms, and its full external determinant
argument still applies. In the exact two-RR cycle, a proposed free
positive DB edge has on D's side either the singleton block D or
the block D,U3. The latter cannot extend through radial A, whose
actual strict inner-vertex application is a singleton. D has one
positive circle atom and U3 none. Thus neither block meets the
necessary two-positive-atom-body alternative. This verifies the full
singleton/shared-block caller independently of the reviewer's earlier
discussion of it. Both actual completion neighbors of D remain.

For the bilateral theorem's canonical join, the original inward-blocker
theorem gives either a nonconsecutive core blocker or a central extra.
The new bilateral clearance removes every physically boundary core
blocker, including zero-total-weight ones. Each remaining core body
is consequently physically clear, unloaded and true degree two in
the unchanged entire simple cycle. The extra remains the actual
possible central square; capacity one does not make blockers at
different transmitters distinct. This is precisely the claimed join,
with no additional motion or graph contraction.

## 4. Review and accounting boundary

The complete outward/pair motion has its separate joint-pockets
review at SHA-256
`49a4b22bafdb85bae7d6aa3684a5a18b21db0cdcdeab78e98bdbe9c335d0f365`.
The complete noncontact theorem and its exact unique-load/generic-edge
callers have the separate common-certificate review at SHA-256
`20adcfd823f0f85eff8102422ce94187ab3ef3d6ff4e636d1341901e7f748eb5`.
Those reviews disclose their prior arithmetic contributions; this
noncontributor check supplies the complementary independent gate.

The actual central extra, third transmitter and exterior extra remain
in the mixed C7 remainder. No canonical motion of any such additional
body, whole-parent closure, original flag, Lean/Lake result or CI result
is inferred here. All checks are hand algebra and fixed exact identities.
