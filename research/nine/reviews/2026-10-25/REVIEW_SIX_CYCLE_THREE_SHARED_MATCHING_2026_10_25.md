# Independent review of the whole three-shared alternating-C6 exclusion

Date: October 25, 2026.
Reviewer: root, independently of the author.

**Verdict: PASS for the entire three-share physical family.**
Together with the accepted zero-share and double-share exclusions,
every remaining all-unique/shared alternating C6 has exactly one or
two genuine shares. The complete three-extra completion problem for
those families remains open. No original roadmap gate closes here.

## 1. Exact saved sources and independent arithmetic

I read the complete frozen mathematical source and checker:

    SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md
    SHA256 bcf265c14b2a7e0182768baf105f010ee7637c7868d258323007b2b63ba9b4da
    SIX_CYCLE_THREE_SHARED_MATCHING_CHECK.py
    SHA256 675561de22034b529186770b64eeb0ee6c0819b8370fc6841ca44d4aea0d5353
    SIX_CYCLE_THREE_SHARED_MATCHING_CERTIFICATE.json
    SHA256 a4be8b12fde8fb9e6bd0a339b7dca46fa0485ab9a87a3ab5d03483d44e52fff9

I reconstructed the original support-value formula, matching reflection,
weighted chord bound, every scalar comparison and normalization, and the
entire angle map. A separate exact Fraction implementation with its own
quadratic-field class rebuilt the q numerators directly from the
uncollected lower chord sum minus the actual support value. It constructed
the final polynomial by the pairwise-square form of the variance, then
compared every ordinary coefficient with the saved certificate.

The independent implementation reconstructed all 45 Bernstein
coefficients, proved each strict >1/100 comparison and reconstructed
every ordinary coefficient from the complete inverse identity.
Everything matched. The persistent author checker also passed.
Its JSON regenerated in an independent directory was byte-for-byte
identical to the saved certificate. No sampled angle or numerical
configuration is a sign premise.

## 2. Original matching and reflected physical scope

The accepted strict-turn normal form gives at most one genuine share
per load, and the independently reviewed double-shared-channel theorem
gives at most one per transmitter. Three marked interfaces in the
original alternating six-cycle therefore form one of its two perfect
matchings. There is no extra graph pattern.

The explicit reflection and label reversal are consistent:

    S'_i=T S_(-i), f'_i=-T f_(-i-1),
    F'_i=T F_(-i).

Reflection reverses orientation, and reversing the cyclic indexing
reverses it again. Thus the original counterclockwise convention and
the actual turn at the reflected load are preserved. Incoming and
outgoing interfaces interchange, carrying every actual mean, physical
corner, magnitude, transverse position and all three extras with them.
This covers the complete outgoing matching without a new normal
selection or force extraction.

## 3. Complete mean-preserving force value

For an incoming shared interface, the original chart has
u_i=J n_(i-1), v_i=n_(i-1). The next normal has components
(sin(theta_i),cos(theta_i)). The original force F_i therefore
has negative u_i and positive v_i components. Physical uniqueness
fixes its circle corner at p_base+v_i, while the other actual
singleton is p_base+u_i.

The shared application p_base+t_i*u_i retains 0<=t_i<1.
The endpoint t_i=0 is allowed, and t_i<1 follows from the prior
distinct-application theorem. Its scalar product with the incoming
normal is independent of t_i. Thus the two support contributions
are exactly mu_(i-1) and mu_i*(cos(theta_i)-sin(theta_i)).
The original transmitter displacement contributes sum mu_i.
Their sum gives

    R*sum |F_i|=sum mu_i*(2+sin(theta_i)-cos(theta_i)).

I checked the cyclic indexing and signs against the original
support-functional identity. Every term R|F_i| uses a strictly
positive true unique-circle load. No physical radial mask is
included implicitly.

## 4. All positive magnitudes are covered by one inequality

The scalar normalization sum mu_i=1 is legitimate by homogeneity
and does not change the physical certificate. For every adjacent
positive pair a,b, the force chord has the exact radicand
(a+b)^2*s^2+(a-b)^2*(1-s^2). Concavity of the square root gives
the displayed chord lower bound on its whole interval.

The strict comparison sin(3pi/8)<37/40 has the correct positive
squaring branch and exact reserve 3761. The affine sine lower
bound is valid for every x=-cos(theta) in [0,1/sqrt(2)]:
the remaining bracket is bounded below by
1/2-69/(100*sqrt(2))>0, with exact squared reserve 239.
The theta=pi/2 equality of this affine bound is retained.

Because each normalized adjacent sum is at most one, the quadratic
chord correction is at least (3/40) times the sum of squared adjacent
weight differences. The exact three-weight identity makes that
3*(3/40)*sum(mu_i-1/3)^2. No ratio restriction on positive weights
is inserted.

I independently collected the linear terms and obtained the exact
q_i shown in the source, including the next-angle index and the
coefficients 163/400 and -237/400. Completing the three squares
gives the lower remainder

    qbar-sum(q_i-qbar)^2/(12*K*c)
      =B/(36*K*c),

where K=79/40, c=3/40 and 12*K*c=711/400.
All denominators are positive. The final strict result follows
from B>0 even when the earlier weak inequalities are equalities.

## 5. Entire angle domain and complete exact certificate

The substitutions theta_0=pi-alpha, theta_1=pi-beta and
theta_2=alpha+beta identify exactly the closed comparison triangle
alpha,beta>=pi/4, alpha+beta<=3pi/4. They imply both upper
bounds pi/2. The half-angle rectangle map is onto this entire
triangle, including the collapsed x=1 edge and every 90/135-degree
comparison boundary. No angular interval is omitted.

The displayed sine/cosine numerators and their common denominator
L=Da*Db have the correct signs for all three theta values.
Da>0, H>0 and Db>0 on the full rectangle, so L never vanishes.
The q numerators satisfy Q_i=L*q_i exactly. Consequently the
clearing identity is globally

    G=L^2*B.

I verified this normalization algebraically; no isolated evaluation
is used to infer it. The independently rebuilt pairwise-square
polynomial agrees coefficient by coefficient with the author's
variance form and full saved ordinary polynomial.

The exact polynomial has bidegree (8,4). Every one of its 45 tensor
Bernstein coefficients is strictly greater than 1/100, and the
complete inverse recovers all ordinary coefficients. The author's
floor table also passes its exact rational-square sign check.
The nonnegative tensor basis sums to one, proving G>1/100 on the
entire closed unit rectangle. Positive L^2 gives the required B>0.

## 6. Exact physical conclusion and limits

The strict scalar inequality gives R<79/40 when applied to the
unchanged original force chords |F_i|. Their sum is positive
because every actual circle load is positive. This contradicts
the entire original radius window, including its lower endpoint.

The proof is independent of all original transmitter sliders and
of all three completion-square locations; these are retained.
Both perfect matchings and every actual shared mean endpoint
are covered. Thus all three-share cores are excluded as a whole.

The prior all-singleton theorem covers zero shares, so exactly
one or two genuine shares remain, with at most one per load and
per transmitter. The required original completion capacity for
those cases, the one-radial strict-obtuse family, the coarse C6
parent, unrestricted theorem and original equality remain OPEN.
No new gate ID, force reassignment, mask collapse, Lean
compilation or CI is used.
