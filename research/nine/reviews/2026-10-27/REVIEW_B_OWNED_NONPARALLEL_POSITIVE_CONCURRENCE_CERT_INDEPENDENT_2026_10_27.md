# Independent full review: positive concurrence at a B-owned nonparallel S root

Date: October 27, 2026.  
Reviewer: cert_final_review.  
Comparison repository head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

## 1. Verdict and frozen scope

**PASS, without a requested correction, for the entire eight-section source**
`B_OWNED_NONPARALLEL_S_ROOT_POSITIVE_CONCURRENCE.md`, frozen at

`e1e66a399678a3c1b2b9d335a556b6391e27b6afd63d66ae926275ef0d098ba2`.

I read the complete target, independently reconstructed every physical,
force, moment, support and inequality argument, and read all three complete
present original inputs. I also reread the complete fresh genuine-neighbor
normal form and its complete independent review before checking the entire
original-domain join in Section 7. This verdict covers the theorem and its
precise original application, not just its scalar inequalities.

The theorem proves positivity of the actual radial concurrence on the
entire stated B-owned singleton-HB, nonparallel-B domain. Its new local
proof needs neither a force equation at H or K nor boundary status, a
physical circle mask, a degree restriction or a side owner at K/BK. It
retains the actual B3 law, both genuine occupied radial leaves, the physical
triangle H-B-K, and every actual support and shared mean. The explicit
nonparallel premise remains. No whole parallel-B exclusion, global C-mask
reduction, original gate closure or recovery of a missing older manuscript
is asserted by this review.

The source is a new proof from present original inputs. In particular this
is not a claim that the missing source at the old d563e080 pin has been
restored. No target bytes were changed during this audit.

### Independence disclosure

I authored the separately reviewed fresh normal form at 93cbef18, which is
used only in the target's final original-domain join. Topology independently
accepted that complete source at review 705bad0d. I did not contribute to
the new positive-concurrence argument before the target was frozen. The
new local theorem in Sections 1--6 is independently reviewed here from its
three present original inputs; the subsequent join retains the precise
scope and conditions of the earlier separately accepted normal form.

## 2. Complete present inputs and byte checks

Every item below was read in full, and its actual bytes match the displayed
SHA256. The local proof uses only the first three original mathematical
inputs; the last two items are the exact final caller join.

| Input | SHA256 | Verified use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine occupied S leaves, actual radial support application, and the entire inward unit segment |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | True B3 force/moment equations, strict physical singleton convention, unchanged actual shared means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | The actual nonobtuse normal relation at the owned HB side in the physical H-B-K triangle |
| POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md | 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce | Complete fresh eight-section original B-owned root chart and its separately stated assumptions |
| REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md | 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d | Complete independent acceptance of that precise fresh normal form |

Together with the target itself, all six frozen pins were rechecked by the
independent exact-audit record. No absent later manuscript is a logical
premise of the local theorem. The nonobtuse sign is used on H-B-K; no B-K-C
triangle or otherwise absent physical contact is assumed.

## 3. The entire support-height lemma

I reconstructed Lemma 2.1 for every support type of an arbitrary unit
square. Let the upward normal be m=(-c,s), with c>=0, s>0 and c^2+s^2=1,
and let Q be its actual minimum-m support point. The conclusion

    min_T y >= Q_y-c

is valid without a circle, force, owner, mask or degree condition.

For a strict minimum vertex, the inward orthonormal axes e,f have positive
m components. They cannot both have negative vertical components, since
their positive combination is m and m_y=s>0. If one axis e points down,
m.e>=0 forces e_x<0 and s(-e_y)<=c(-e_x). Both sides are nonnegative.
Squaring, then using the two unit identities, gives e_y^2<=c^2. This
squaring is safe and loses no sign condition. The other inward axis has
nonnegative height, so every actual point of the whole square lies at
height at least Q_y-c. The c=0 case admits no downward axis and is treated
without division.

For a minimum side, the actual downward tangent is e=(-s,-c), the inward
normal is m, and Q=V+tau e for the actual tau in [0,1]. The exact identity

    min_T y = V_y-c = Q_y-(1-tau)c

proves the same bound at every side position, including both endpoints and
c=0. The vertex and side cases exhaust the possible support faces. The
later use at K therefore needs no conversion of a free normal into a side
axis and no replacement of its actual application.

## 4. The actual B chart and low-radius endpoints

Both genuine leaves provide actual near-origin root points of radius at
most epsilon=max(d-1,0). Every point of either root has norm at most
epsilon+sqrt(2)<43/30<79/40<=R, so both roots are physically circle-clear.
The true B3 law therefore omits no B circle atom. No equation at H enters
this step.

Let n be B-to-H and m be B-to-K. The owned HB side and the actual H-B-K
triangle give n.m>=0. The positive B3 force equation implies e_B.n<0.
After the permitted whole-packing rotation n=-E1, the B support is x=h,
the actual near-origin points give |h|<=epsilon, and its genuine support
application satisfies d(e_B)_x=1+h.

I checked both lower-radius exits. If d<1, epsilon=h=0 and the last
identity is impossible. If d=1, the identity forces e_B=E1; the vertical
force equation then makes m horizontal, contrary to the explicit
nonparallel premise. A horizontal e_B is excluded by the same force
equation throughout the remaining domain. Thus d=1+delta with
0<delta<1/60. Reflection makes e_B point down, giving the actual lower-right
B leaf vertex and the full radius identity

    B=[h,h+1] x [-b,1-b],  p_B=(1+h,-b),
    (1+h)^2+b^2=d^2,  |h|<=delta,  0<b<31/120.

The estimate b^2<=4delta uses 1+h>=1-delta>0 before squaring. The strict
31/120 comparison has exact square reserve 1/14400. Neither a genuine
aligned leaf nor an alternate B orientation is silently discarded: the
force/ownership argument itself excludes an aligned B leaf in this chart.

The original strict singleton convention makes P=(h,p) an interior point
of B's left side and a strict maximum-x H vertex, hence -b<p<1-b. A
vertex/vertex contact with a freely selected cone normal cannot be
substituted for this actual B-owned side. The radial leaf line and actual
HB line intersect at q_B=-(p/b)p_B. Its definition is safe because b>0.
The actual B moment equation forces the unchanged BK line through this
same q_B. No auxiliary concurrence or normal is selected.

Finally n.m>=0 gives m_x<=0, and the positive vertical force equation gives
m_y>0. Thus the entire normal cover is the strict northwest row or E2.

## 5. The complete nonpositive-concurrence alternative

The contrary sign sigma<=0 is exactly p>=0. In the northwest row the
actual B support is Q=(h,1-b); its vertical displacement from q_B is
1-b-p>0. The real upward normal therefore has a positive proportionality
factor along Q-q_B, and its negative horizontal component gives

    (1+h)p < -h b.

In the vertical row the unchanged actual mean is
Q=(sigma(1+h),1-b), and Q_x>=h gives the corresponding non-strict
inequality. This keeps the physical singleton/shared alternatives and the
left endpoint of the shared mean. There is no owner premise at BK.

Both rows imply h<=0. With a=-h, the exact necessary domain is

    0<=a<=delta,  0<=p<=a b/(1-a).

For a>0, 1-a>59/60 and b/(1-a)<31/118<1/3, so p<a/3<1/180. Every
division has a previously established positive denominator. The
nonpositive domain has been reduced uniformly, without optimizing an
angle, selecting a mean, or imposing a force ratio at another square.

## 6. The zero endpoint and all genuine H leaves

At a=0, the actual interval forces p=0, so the strict rightmost H vertex
is the origin. In its inward orthonormal coordinates, a genuine radial
support has nonnegative coordinates; each positive direction coordinate
forces its application coordinate to be one. One positive coordinate
forces d=1, and two force d=sqrt(2). Both contradict 1<d<61/60<sqrt(2).
This endpoint is proved separately before any division by a.

For a>0, the actual H frame is

    H=(-a,p)+[0,1]u+[0,1]v,
    u=(-alpha,beta), v=(-beta,-alpha),
    alpha,beta>0, alpha^2+beta^2=1.

Its entire u coordinate is positive, since P.u=alpha a+beta p>0.
Consequently the real leaf has positive u component and must use the
maximum-u face. The far corner cannot be the genuine leaf: |P|<1/30
and its norm is greater than 41/30>d. The precise sharper bound
|P|<1/45 is retained before this convenient comparison.

I checked the complete three-sign cover in the other actual axis. A
positive v component uses the excluded far corner; a negative v component
uses P+u and requires P.v<0; a zero v component uses the full maximum-u
side and requires P.v<=0, including both endpoint applications. Therefore

    beta a-alpha p<=0,
    beta/alpha<=p/a<1/3,
    max_H y=p+beta<61/180.

This includes every genuine radial H vertex and every aligned H side
application. At p=0 the necessary sign is itself contradictory; keeping
the common height bound does not remove that endpoint. H retains all its
other physical contacts and forces; no H3 law is used.

## 7. Whole-K height and the actual-contact contradiction

If m=E2, the actual support puts the whole K above height 1-b>89/120.
In the northwest row, the real line Q-q_B gives the exact slope

    c/s = [a-(1-a)p/b]/[1-b-p].

The numerator is positive and at most a. The entire denominator obeys

    1-b-p > 1-31/120-1/180 = 53/72 > 2/3.

Thus c/s<1/40 and c<1/40. Applying the full support-height lemma at the
actual K support Q gives

    min_K y >= 1-b-c > 43/60.

This conclusion uses no K circle point, boundary premise, mask, force,
degree or side ownership. A genuinely free BK normal and a full support
side are covered by the proved lemma. Both BK rows therefore strictly
separate the entire physical K from the entire physical H, since

    43/60-61/180 = 17/45 > 0.

That contradicts the actual HK contact. It excludes the entire
nonpositive concurrence domain, not a collection of candidate poses.

## 8. Positive endpoints and original caller join

The result gives t=-p with 0<t<b and sigma=t/b in (0,1). For strict
northwest BK the actual support-line signs give h<q_Bx<h+1 and
-b<q_By<0, so q_B is strictly inside B and both real nonleaf rays have
positive offsets. For vertical BK, membership gives only q_Bx>=h; the
equality endpoint remains possible. Its BK ray is strictly upward, but
the HB offset may vanish. The source correctly does not transfer strict
interiority from the northwest row into this endpoint.

I compared the complete final join against all eight sections of the
fresh 93cbef18 normal form and the full 705bad0d independent review. The
same actual radius window, B-owned singleton convention, genuine leaves,
true B3 and explicit nonparallel condition occur in both. The present
theorem supplies precisely the formerly assumed positive sign, without
changing any original force or shared application.

The normal form's later detailed K chart separately uses physical K
boundary status and its original BK owner input. Those are retained in
the original hub-tip application; they are not falsely inferred from the
stronger local sign theorem. The original graph retains true H4/K3/B3/C2,
both genuine occupied S leaves, and all three extra physical units. A
whole parallel-B theorem, the global C-mask reduction and the exact
central-singleton original join remain separate obligations. This review
does not convert those obligations into accepted conclusions.

## 9. Independent exact reconstruction

The independent reproducible record is
`cert_positive_b_concurrence_exact_audit.py`, with output
`cert_positive_b_concurrence_exact_audit.json`, both in the recovery root.
It uses exact rational arithmetic and transparent polynomial expansion;
it uses no numerical sampling or symbolic-algebra black box.

All **12 complete identities**, **21 exact rational values or reserves**,
and **six frozen target/input/review pins** pass. The twelve identities
cover the support-axis squaring, the full actual support-side slider, the
real B-leaf budget, HB height at the concurrence, northwest and vertical
force-line horizontal displacements, the wrong-sign slope, the full H
frame and both inward projections, and both positive-chart endpoint
identities. These are independent whole-expression checks, not a repeat
of numerical evaluations at selected geometric configurations.

The exact values recorded independently are:

| Quantity | Exact value |
| --- | --- |
| Root diameter upper comparison | 43/30 |
| Root circle-clear reserve | 13/24 |
| Square reserve for sqrt(2)<17/12 | 1/144 |
| Square reserve for sqrt(2)>7/5 | 1/25 |
| Actual b square reserve | 1/14400 |
| Lower comparison for 1-a | 59/60 |
| Whole side-mean ratio comparison | 31/118 |
| Gap from that comparison to 1/3 | 25/354 |
| Actual p upper comparison | 1/180 |
| Whole P triangle bound | 1/45 |
| Gap between 1/30 and 1/45 | 1/90 |
| Opposite H vertex lower comparison | 41/30 |
| Opposite-leaf radius reserve | 7/20 |
| Whole H upper height | 61/180 |
| Vertical whole-K lower comparison | 89/120 |
| Vertical-to-common height reserve | 1/40 |
| Actual force-line denominator bound | 53/72 |
| Denominator reserve above 2/3 | 5/72 |
| Northwest normal ratio comparison | 1/40 |
| Whole K lower height comparison | 43/60 |
| Strict H-K height separation | 17/45 |

The analytic proof supplies the complete continuous-domain coverage.
This audit record validates displayed algebra, constants and source
identity; it is not a finite computational exclusion certificate. The
new theorem adds zero such certificates.

## 10. Final acceptance boundary

The entire fresh positive-concurrence theorem and its exact stated
normal-form join are accepted at the frozen target hash above. The proof
preserves every genuine H leaf, every actual BK support type and mean,
the zero wrong-sign endpoint, both positive-chart endpoint conventions,
and all physical units and original forces. No correction is requested.

No source, original gate, ledger, remote branch, Lean file or CI workflow
was edited by this review. Missing older whole-family reductions remain
explicitly separate; no full original-gate closure is claimed here.
