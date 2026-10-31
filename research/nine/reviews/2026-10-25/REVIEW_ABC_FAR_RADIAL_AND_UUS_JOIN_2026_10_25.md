# Independent review of the far-radial ABC proof and the complete UUS join

Date: October 25, 2026.

**Verdict: PASS.** The complete saved analytic and original-domain proof in
ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md is valid at the scope
stated below. Its join with the previously accepted whole-feature theorems
exhausts the four original UUS gates listed in Section 5. This review does
not edit a gate or claim the remaining UUU family, the whole ABC orbit, a
coarse cell, or the global nine-square theorem.

## 1. Precisely identified sources and review roles

The hashes below identify the reviewed pre-acceptance snapshots. Later
edits change only acceptance status, pointers to the accepted complete
join and explicit statements that older unused proposals remain unproved.
Root separately regenerated all 2256 pressure coefficients and all 52
monotonicity coefficients, including their full inverse identities;
all four saved coefficient artifacts matched exactly byte for byte.

The principal saved source reviewed in full has SHA-256:

```text
a87ead5222aa7ebca42ed77b3b083a7a33339714dc9dd2f21212fd1eee21e681
ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md
```

This is the corrected version retaining **all three** arbitrary completion
squares. H,A,B,C,X,Y are six actual bodies. The earlier opening phrase
"two arbitrary extra squares" was a scope typo, corrected before this hash
and before acceptance. No mathematical change was required by this review.

The reviewer independently derived and checked the analytic identities and
inequalities of Sections 1--8 and the rational denominator identities in
Sections 9--10. The reviewer authored the displayed three reduced exact
polynomial packets; a separate reviewer independently reconstructed all
three from the scalar formulas, including alternative larger numerators,
and checked every forward and inverse coefficient identity without reading
the author's checker or coefficient data. The root also independently read
the complete source, rederived the scalar chain and denominator identities,
ran the persistent checker, and verified the saved coefficient data.

The scalar prerequisites have separately passed full independent reviews:

| Source | SHA-256 |
|---|---|
| ABC_FAR_RADIAL_A_MONOTONICITY_WORKING_2026_10_25.md | f31de4c51868c78b67dacdf81599af781ac259c4816af6981a4055580be55c42 |
| ABC_UPPER_LEFT_FAR_RADIAL_ENDPOINT_BOUND.md | 76456f210cb3e05c7f77c3d0df9c539beb4af84b3954f64df3590982343ff99f |
| ABC_UPPER_LEFT_FAR_RADIAL_DOMAIN_WORKING_2026_10_25.md | eb6a38468aa76909ca2706011ff63f5a5a54eb471a45a2093dff51d4b59128c0 |

The last source is used only for its proved exact domain and lower-corner
contradiction. Its unproved centered-H sufficient comparisons are **not**
premises of the accepted block-pressure proof.

## 2. Full original-domain and analytic audit

The actual component is H--A--B--C--H together with the intact H--X--Y--H
petal. H has true degree four, A/B/C/X/Y their true degree two, and H is
physically circle-clear. A and B are physically unique. C is physically
radial with its original nonnegative individual weights of positive total.
The complete radius interval is q in [6241/1600,1105/256]. No HB contact is
introduced, and no body is assigned another body's degree.

The review checked the following complete chain.

1. The H-owned negative-endpoint chart comes from Section 1 of
   NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md, before that source's
   radial-middle specialization. Its actual A2 concurrence gives
   rho=c/[c+s(a/b-1)], with a>b>3/5, c,s>0 and 0<u<v. The original H-side
   parameter remains 0<r<1. No bound from the left A-owned branch is used.

2. The strict far B vertex and incoming AB application are distinct fixed
   physical singleton points on a unique B of true degree two. The existing
   compatible fixed-tip selection therefore makes BC C-owned. The strict
   physical normal convention puts its point in the relative interior of
   that C side. The outer radial face width obstruction and the local
   inner radial face boundary-neighbor lemma in C7_FORCE_POLYGON.md exclude
   the two radial-axis alternatives. That lemma needs only the actual
   boundary neighbor B, not a seven-cycle. Thus the entire surviving C has
   C=[-1/2,1/2]k+[-K,-d]Jk and W=-k/2-MJk with d<M<K.

3. Both original physical B-corner alternatives are covered. For
   epsilon_B=0, proper concurrence gives
   kappa_B(M+t-p)=M with 0<kappa_B<1, hence t>p. The exact circle identity
   K^2-M^2=2+p+t+2M(t-p) then exceeds 2+sqrt(2), whereas M>d gives a value
   below 91/30. This is a full contradiction without any C weight or HC
   restriction. For epsilon_B=1 the complete interval is 3/2<beta<K, with
   every original offset and sign retained in the displayed parametrization.

4. The monotonicity lemma applies to the entire scalar beta interval, not
   merely the physically feasible subinterval. The continuous beta=K value
   is a comparison endpoint only. Its a value is positive; therefore the
   independently reviewed endpoint bound gives the original b>9/8. The
   original a>b simultaneously gives b<sqrt(q/2)<3/2. No radial tie is
   assigned to the actual unique B.

5. The whole-domain M and half-angle bounds used by the new proof are
   valid: M>(1+t)/(2p), d>(1+t)/(2p), z=t/(1+p)<31/91,
   t<5/8, p>3/4, and M<p+1/2<3/2. Their derivations use the genuine circle
   identity, d<M, and the entire q window. The two narrow rational strips
   in Sections 4 and 6 are enlargements containing every original point.
   The lower strip reserve is exactly
   53/14400+t^2(13/60-t^2/4)>0. The two upper coefficients 88/161 and 33/56
   are the respective positive square-root tangent coefficients.

6. The sign B0=6L(a-1)-h(7a-1)>0 is proved before using any polynomial
   packet. The reviewer rederived the exact L(M*)>4/3 numerator, the identity
   2L-3=t[2M^2-3-Mz]/(M+t), the reserve 73/1638, and the original-domain
   H_B<11/8 contradiction. Its endpoint reserve is 4759/262144. These give
   h/L<1/4 when h>0; a>11/8 then gives B0>3L/32. For h<=0 the same sign is
   immediate. The square-root chord b>=(8/21)b^2+9/14 has exactly the
   required direction on the complete b interval. Thus the rho packet
   proves rho>6/7, without an assumed pressure sign at C.

7. The reviewer rederived the monotonicity in rho of P dot n and the
   concavity in b of its lower numerator. Both complete endpoint
   comparisons are strict. The exact nonbalanced endpoint reserve is
   3591/40000, and the balanced comparison has 39^2-16*85=161. Therefore
   c_H dot n=P dot n-1/2>0. The convex squared norm of S_r retains the full
   original H position and has endpoint values 5/2+2u and 5/2+2v. Actual
   negative A pressure consequently implies q<5/2+14/sqrt(85)<201/50.

8. The k_j computation uses the actual A concurrence
   q_A=[L/(L+s)]z_A. Direct determinant expansion gives
   sign(k_j)=sign((L+s)(ps+tc)-pb). Multiplying by
   (L^2+h^2)^2 and using b^2=q-a^2 gives exactly N0+N1*b with the displayed
   N0,N1. Both polynomial signs apply on the full narrower strip. Since
   N1<0, the same lower chord reverses in the required direction, yielding
   N0+N1*b<=Nchord<0. Thus the original k_j is strictly negative.

9. The original k_y<0 and k_x<0 give k_n<0. Since z_A dot n>0 and
   z_A dot j<0, negative A pressure together with c_H dot n>0 forces
   c_H dot j>0. Hence c_H dot k<0. The reviewer checked the true origin
   moments, including m_A=det(P,n)>0, and the unchanged identity
   mu*m_A=gamma*L=eta*M. Cancelling only the internal AB force gives the
   actual block sum F_A+F_B=gamma*L(n/m_A-k/M), whose H-pressure is strictly
   positive. No fictitious HAB or HBC triangle is used.

10. RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md gives positive H-pressure for
    the true radial C load at its actual HC contact. Its conclusion holds
    separately for both physical circle corners and therefore includes
    either individual zero-weight endpoint. BOWTIE_CELL_CLOSED.md Section 2
    gives positive pressure for the intact HXY petal while allowing H's
    other neighbors. Summing the genuine component equations gives
    F_A+F_B+F_C+Mpetal=0, contradicting their positive H-projection.

This is an entire far-return exclusion. It does not assume a particular HC
side, owner, singleton, shared interval, or original mean. The physical C
weights and all three completion squares remain throughout.

## 3. Exact polynomial audit and persistent artifacts

All three packet definitions and denominator identities (18),(21) were
checked against the original rational scalar formulas. On each closed
rectangle U>0, M>0, Znum>0 and D>0, so every cleared factor has its stated
sign. Exact division by U^2 in each k_j packet is verified; no zero factor
on the domain is discarded.

| Packet | Degrees in (lambda,z) | Number of coefficients | Verified normalized lower bound |
|---|---|---:|---|
| rho | (11,64) | 780 | every coefficient >9/10 |
| negative N1 | (8,38) | 351 | every coefficient >9/10 |
| negative Nchord | (14,74) | 1125 | every coefficient >9/10 |

The complete inverse polynomial identities include all ordinary powers,
including absent monomials. The separate reconstruction of the k_j
polynomials first produced larger cleared numerators; direct polynomial
multiplication verified that these equal D^2 times the reduced numerators.
There is one whole rational rectangle for each implication, not a sampled
pose or angular partition. The exact row minima reported in the manuscript
match the attached data.

Persistent artifact hashes:

```text
5e1230ae9ec3e03ff2d1fe40c6006f93d5608356005cb7c3c0879c54ef605a13
ABC_UPPER_LEFT_FAR_RADIAL_PRESSURE_CHECK.py
07a7e756f3de200eaa280bea1f3f297c7ea7131b52dadac1d49db8aa80848823
ABC_UPPER_LEFT_FAR_RADIAL_RHO_CERTIFICATE.json
739f202d0e33fd309605300cf2b3f2438da8122986aaa6911868e66fb0de72c0
ABC_UPPER_LEFT_FAR_RADIAL_KJ_COEFFICIENT_CERTIFICATE.json
7bd0710cdc34dd7762d5f872292b5d77b8c47327e87309a03061051eb922f815
ABC_UPPER_LEFT_FAR_RADIAL_KJ_CHORD_CERTIFICATE.json
c1be1918a4262e2db13a6ec1195390e7edac95cf36d1e74395ff2c431d14a0fc
ABC_FAR_RADIAL_A_MONOTONICITY_CHECK.py
53108ff1aa31e5cc336a54f867d3dd7875664a39d88b030069f5d113730c9ffa
ABC_FAR_RADIAL_A_MONOTONICITY_CERTIFICATE.json
```

The last two artifacts preserve the separate independent reconstruction of
the prerequisite monotonicity lemma and all 52 of its exact coefficients.
No Lean compilation, CI, or numerical sample is a premise of this review.

## 4. Exhaustive upper-left return join

The complete B fan is Section 2 of
NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md. Its true B2 equation
forces k dot f<0. Thus exactly the following actual support alternatives
remain; an axis normal belongs to the side row even when its original mean
is a side endpoint.

| Full original BC feature | Complete exclusion |
|---|---|
| Strict near B vertex W0 | NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md |
| Strict far B vertex W1 with k_y>=0, including equality | NEGATIVE_H_OWNED_UPPER_LEFT_NONNEGATIVE_VERTICAL_RETURN_EXCLUSION.md |
| Strict far B vertex W1 with k_y<0, either physical B-corner alternative, radial C | ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md |
| Minimum-f side, strict B-owned singleton | NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SINGLETON_EXCLUSION.md |
| Minimum-f side, genuinely shared, every original mean and its endpoints | NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SHARED_EXCLUSION.md |

At a strict vertex, compatible selection is used at unique B2; it is never
used at radial C. At the minimum-f side the strict physical convention
leaves precisely the singleton or positive-length shared alternatives.
The two side sources exhaust all radial orientations without presuming
C owns a strict singleton normal. Every row retains the true H4/petal
component and every original HC owner and mean.

The four previously accepted return sources were reread for their complete
scope and their joins. Their reviewed SHA-256 values are:

```text
638292d93835c0f336c9549250107f39fab964cd72a00a35806ebc460f943b13
NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md
fc5bcc17dd0c2a9c0729a35e53833ce5d74f3b836d26f231688519e73b85d03d
NEGATIVE_H_OWNED_UPPER_LEFT_NONNEGATIVE_VERTICAL_RETURN_EXCLUSION.md
eb4040b595d817776e02aaa2cbeceff019d65ad261af36d71141c7abefc1bd74
NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SINGLETON_EXCLUSION.md
96ab49965a566f485861d09fd86428b27690fd83f9b7e671cc5d1e50d25c450c
NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SHARED_EXCLUSION.md
```

All five rows hold on the entire original q interval. Therefore the
original low interval q<17/4 and high interval q>=17/4 are both exhausted,
with no gap at q=17/4, k_y=0, a side-normal limit, or a zero radial weight.

## 5. Exact four-gate UUS assembly

UUS is the physical mask in order **(B,A,C)**: B is unique, A is the
negative unique endpoint, and C is radial. The negative-endpoint reduction
is the existing BOUNDARY_THREE_PATH_RESULTANT_CONE.md Section 4 applied to
the genuine ABC boundary path and intact petal. In this mask C has positive
H-pressure, so the distinguished negative endpoint is indeed A; no middle
body or circle weight is relabeled.

For H-owned singleton HA, Section 1 of
NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md gives the exhaustive AB
fan: the left A axis, upper A axis, or strict upper-left A vertex. The
compatible fixed-tip theorem at A rules out a free AB in the strict vertex
case, because its HA point P and AB point T are distinct fixed physical
singletons. Thus that case is exactly the B-owned upper-left family closed
by Section 4 above.

The other AB features are already accepted whole domains. The review
checked their stated hypotheses, actual degrees and complete output scope:

* The small-coordinate left-axis theorem covers a<=3/2 for singleton and
  shared AB. For a>3/2, the full left-singleton near-return theorem gives
  the exact near/side fan and excludes its far vertex. Its radial-C side
  exit covers every remaining side orientation and original mean. These
  are NEGATIVE_H_OWNED_LEFT_SINGLETON_NEAR_RETURN_EXCLUSION.md and
  NEGATIVE_H_OWNED_LEFT_SINGLETON_SIDE_RADIAL_EXIT.md, with the stated
  previously accepted tilt/domain prerequisites. Hence all left A-owned
  singletons are excluded at every radius for UUS.
* NEGATIVE_H_OWNED_UPPER_AXIS_SINGLETON_MIDDLE_EXCLUSION.md excludes every
  upper A-owned singleton at all original radii and both C masks.
* NEGATIVE_H_OWNED_SHARED_LEFT_MIDDLE_EXCLUSION.md and
  NEGATIVE_H_OWNED_SHARED_UPPER_MIDDLE_EXCLUSION.md exclude the complete
  two genuinely shared AB features, with every original mean. In
  particular their radial-C exits do not discard an individual weight.

Consequently the entire original H-owned UUS family is excluded.

For the full UUS mask, the remaining HA owner classes are also already
accepted whole domains. Their source statements and joins were checked:

* If HA is free, NEGATIVE_ENDPOINT_FREE_SHARED_RADIAL_MODULE.md forces
  B to have two physical circle corners, contradicting the actual unique
  B mask. That module applies to true A2/B2 and the physical HC contact,
  with arbitrary additional forces at H and C.
* An A-owned singleton HA is excluded at all radii by
  NEGATIVE_A_OWNED_UNIQUE_MIDDLE_EXCLUSION.md. Its lower-radius proof
  retains the original HC contact and both C masks; its high-radius
  dependency includes q=17/4 and does not assume an HB chord.
* For shared HA, NEGATIVE_UNIQUE_ENDPOINT_OWNED_CONTACT_DOMAIN.md forces
  a strict northwest singleton AB, so it is either B-owned or free.
  The B-owned case is exactly the all-original-mean extension of
  NEGATIVE_A_OWNED_UNIQUE_MIDDLE_EXCLUSION.md. The free case is
  NEGATIVE_A_OWNED_SHARED_FREE_UNIQUE_MIDDLE_EXCLUSION.md. The high-radius
  side-owned theorem separately includes every shared mean. These source
  statements use the same compatible certificate and keep H4/A2/B2/C2.

This is the full physical HA owner partition. The preceding paragraphs
use previously accepted whole theorems as dependencies; they are a fresh
scope and assembly audit, not a claim to have repeated every older proof's
independent internal arithmetic in this review.

It is therefore mathematically justified for the maintainer to close
exactly these four **existing** original gates after accepting the source:

1. M6.TB4.C4.LABC.NEGATIVE_OWNER.UUS.H_OWNED.LOW.AB_B_OWNED
2. M6.TB4.C4.LABC.NEGATIVE_OWNER.UUS.H_OWNED.HIGH.AB_B_OWNED
3. M6.TB4.C4.LABC.NEGATIVE_OWNER.UUS.H_OWNED
4. M6.TB4.C4.LABC.UUS

No new gate is introduced. The physically unique C mask UUU retains its
strict downward far-vertex and minimum-f side obligations. Thus neither
M6.TB4.C4.LABC.NONPARALLEL nor the whole ABC orbit nor its coarse parent is
closed by this join. No parent-cell count changes are warranted here.
