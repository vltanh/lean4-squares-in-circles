# Independent full review: side-transmitter bypass and unloaded endpoints

Date: October 27, 2026.
Reviewer: rooted_blocks, separate from the source author and root reviewer.

**Verdict: ACCEPT, with no mathematical or exposition correction.**

## 1. Exact reviewed source and scope

I read all 343 lines of

`CHORDED_HEXAGON_SIDE_TRANSMITTER_BYPASS_UNLOADED_ENDPOINT_SEPARATION.md`

at SHA-256

    4a979638b562040455e3058351db24358e7ecb093e5c0c1635dcd6438492eecd.

I also read the entire actual prerequisite `UNIT_BYPASS_NORMAL_CHANNEL.md`,
including its separately audited full transverse-separation Section 4,
and the original two-spoke/no-chord row and reflection in
`SIX_BODY_INNER_PENTAGON_LOAD_COVER.md`, Sections 1--3. I checked the
original `M6.B6.PENTAGON.LOAD_CONTRACT` and H2_D0.L134 gate in the unchanged
roadmap. This is a full local proof and original-gate audit, not an audit
of the source's concluding summary alone.

The new theorem is radius-free. Its decisive hypothesis is the complete
actual unloaded degree-three equation at A, with positive neighbors
S,T,B. No degree or force premise at the bypass T or the other endpoint D
is needed for that one-endpoint result. The actual side-transmitter scope
is restored explicitly when the theorem is applied at both endpoints.

The conclusion is the strict half-plane containment of the entire actual
external square, not merely a center bound or an absent positive edge.
It therefore contradicts the actual closed physical contact 34 in the
original graph. All three additional units remain; no condition on them
is required.

## 2. Actual support-point and reach facts

The support-point inward-segment fact holds for every original application
on a closed support face. In the unit's own coordinate intervals, a
nonzero normal component points into its corresponding minimizing
endpoint, and a zero component fixes that coordinate. This includes a
side endpoint and an arbitrary shared-side weighted mean.

For a minimum support point p and n_x<0, I independently checked

    max_K (x-p_x) <= |n_y| < 1.

At a vertex, both inward perpendicular edges cannot have positive
x-component while also having nonnegative n projection: positive e_x
would then be a positive combination of them and have nonnegative
n projection. For the sole possible positive-x edge w, the support
inequality gives

    |n_x| w_x <= |n_y| sqrt(1-w_x^2),

and hence w_x<=|n_y|. The other edge cannot increase the maximum.
At a side, the inward normal edge has negative x-component and the
transverse interval has length one, giving the same bound for every p.
For n_x=0 the weak reach bound one is valid.

For n=(c,d), 0<c<d, the forward reach bound c+d is also complete.
With at most one positive-x inward edge the bound one suffices. With
two, the support condition gives tan(theta)<=c/d<1, and the increasing
function cos(theta)+sin(theta) on this range has maximum c+d. In the
side case the normal and transverse contributions are at most c and d.
No mean-centering premise is used in either bound.

## 3. Full original A force sign and geometric feature cover

Because the same physical T touches D, it reaches x>=1. Its actual A
port has x<=0. The backward reach bound excludes n_x<0. The complete
unloaded A equation

    alpha e_x+beta n+gamma m=0

then gives m_x<0, using all three strictly positive magnitudes.

When A owns the horizontal axis, every m support is on x=-1. Its
entire neighbor B has x<=-1+|m_y|<0. This includes both corner and
variable side applications, with no information about n_y needed.

In the oblique chart u=(-a,b), v=(-b,-a), a,b>0, a^2+b^2=1, P=0 is
the unique rightmost vertex. If n_x=0, weak reach forces p_T=P, where
no vertical normal belongs to the outward cone; hence n_x>0.

I checked every actual A support feature. The lower side and vertex
have y<0, contrary to T lying above the transmitter. The opposite
vertex has x=-a-b<-1 and cannot reach a point with x>=1 within unit
diameter sqrt(2). The two opposite side normals have negative x and
were already excluded. Precisely P, the upper P--U side with normal
-v, and the upper vertex U with a positive-x/positive-y normal remain.
All endpoints are included in the stated overlaps between cases.

At P, the actual inward-normal segment into T gives n_y>=0; in the
other two features n_y>0. Thus m_x<0,m_y<=0. Its v projection is
strictly positive, so the complete external support cover is exactly
W, V, or the actual V+[0,1]u side with normal m=v. At W the strict
backward-reach conclusion is immediate since a+b>1.

## 4. Coincident ports and the complete owned-side torque calculation

If p_T=P, both first forces have zero torque about the same actual
P. The full A torque gives det(p_B,m)=0. Since P lies in A and p_B
is the m support, p_B=lambda m with lambda>=0; lambda=0 contradicts
the actual normal cone at P, so lambda>0.

In own coordinates a nonzero component of m is positive and its support
coordinate is one. Thus p_B is U,V,or W. If p_B=U, m=u, the full
equation projected on v gives beta n.v=alpha b>0, incompatible with
n being an outward normal at P. The p_B=V projection on u is identical.
Only W remains. This argument covers the zero transverse component and
both coincident actual pair applications without changing either mean.

For p_T=lambda u, n=-v, 0<lambda<=1, the m=v entire shared-side
alternative is excluded by projecting the full equation on u. If
p_B=V, its actual torque is -alpha a, while the T torque is
-beta lambda. Both are strictly negative. Their sum cannot be zero.
Only W remains. I checked the endpoint lambda=1 as well as the open
side; lambda=0 is exactly the preceding full coincident case.

## 5. Upper-vertex force and torque algebra

Let p_T=U=u and n=(c,d), c,d>0. The actual unit T contains u and a
point with x>=1, so 1+a<=sqrt(2), giving a<1/2 and b>a. This uses
the original point, not a selected mean moved toward a convenient end.

If m=v on the whole opposite parallel side, the original application
is v+rho u with 0<=rho<=1. The backward reach bound gives

    max_B x <= -b-rho a+a < 0.

Both rho endpoints and every internal mean are therefore covered.

For p_B=V with its remaining normal, I expanded the full torque using
det(u,v)=1 and obtained the exact source identities

    K=ad+bc, L=bd-ac,
    beta det(u,n)+det(v,-alpha e_x-beta n)
       =-beta K-alpha a+beta L,
    alpha a=beta(L-K)>0.

Hence t=c/d<(b-a)/(a+b)<1. The previously proved forward reach bound,
with the strict monotonicity of (1+t)/sqrt(1+t^2), gives

    1+a <= c+d < sqrt(2)b.

Substituting b^2=1-a^2 and factoring yields

    (1+a)^2-2b^2=(3a-1)(a+1)<0,

so 0<a<1/3. The strict endpoint is retained rather than replaced by
an estimate allowing equality.

From the same full force equation the actual external normal has

    |m_x|/|m_y|=(b-a-bt)/a=D0/a,
    |m_y|=a/sqrt(D0^2+a^2).

The strict t bound gives

    D0>a(b-a)/(a+b)>a^2/b.

For the second comparison its exact numerator is

    b^2-a^2-2ab=1-2a^2-2ab>1-2/9-2/3=1/9>0.

All divisions have strictly positive denominators, and b<1 justifies
ab<1/3. This gives |m_y|<b, so the actual V support has max_B x<0.
No load, normal, or application at B,T,D is used beyond physical
containment of the displayed contacts. The W, variable-side and V
alternatives now exhaust the upper-vertex case.

## 6. Both endpoints and the exact original graph join

The complete unit-bypass theorem supplies reserve exactly one from
the actual unloaded S degree-two channel and its actual unit bypass T.
Its full transverse-separation conclusion puts T on one transverse
side. Reflect that coordinate if necessary and translate the unchanged
common channel height to zero. The actual S transverse interval is then
[k-1,k], 0<=k<=1, precisely as required in the new one-endpoint theorem.
There is no assumption of contact between S,T or of a common frame
for the other units.

Applying at A gives B wholly in x<0. The rigid reflection x->1-x
applies the same original theorem at D and gives C wholly in x>1.
These strict closed-set statements exclude both B=C and any physical
BC contact. They do not merely exclude a positive BC multiplier.

For the actual H2_D0.L134 graph the identities are exactly

    S=H, A=0, D=2, T=1, B=4, C=3.

H is unloaded of true degree two with neighbors 0,2; 0 and 2 are
unloaded of true degree three, with full neighbor sets H,1,4 and
H,1,3. Thus all positive forces required by the local theorem are
present with positive magnitude. The loaded 1,3,4 equations are never
shortened or otherwise used. The actual original rim edge 34 gives
the forbidden physical intersection of C and B.

The graph-preserving reflection fixes the load set 134 and exchanges
the endpoint/external roles, already covered by the two applications.
All original physical circle masks and individual zero weights remain,
including any physical boundary contact of an unloaded body. All three
additional actual squares remain unrestricted. The proof needs no
radius, minimization, embedding, circle-load split or selected-normal
perturbation beyond the original actual force data.

## 7. Accepted consequence and limits

The complete new one-endpoint theorem and its two-endpoint corollary
are accepted at the exact true unloaded degree-three scope. They exclude
the whole original gate `M6.B6.PENTAGON.H2_D0.L134`, with its complete
retained-domain contract.

The source correctly does not claim the other H2_D0 load orbits or the
whole six-body parent. Its separate comparison with the double-channel
three-load theorem does not delete any load or infer a larger closure.
No higher-degree endpoint may borrow this result after dropping a
force; no arbitrary square may replace its actual balanced transmitter.

No correction was requested. This independent acceptance is a full
mathematical and original-gate review, separate from the root audit
and from any eventual ledger or publication action.
