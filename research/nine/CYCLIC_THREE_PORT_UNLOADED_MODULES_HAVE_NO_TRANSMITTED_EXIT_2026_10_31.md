# Every exit of a cyclic unloaded three-port module is a direct hub contact

Date: October 31, 2026. Author: four_chain continuation.

**Status: complete new hand proof, frozen for independent review.**
No mathematical program, numerical pose, Lean, build or CI is used.
This manuscript changes no earlier proof, original identifier or status.

## 1. Exact original scope and theorem

Keep all nine actual closed unit squares with pairwise disjoint open
interiors in the same disk centered at O, with

\[
R^2\le Q=1105/256.
\]

Retain one unchanged complete physical force-and-torque certificate.
Every positive body-pair force keeps its original magnitude, support
normal, actual application or full shared-side mean. Every physical
circle corner and its individual coefficient remains. Unloaded means
zero total selected circle load; it does not mean physically circle-clear.

Let K be connected in its induced original positive graph, entirely
unloaded, with a full original positive cut of exactly three edges.
Assume its induced cycle rank is at least one. A hub is an actual
member of K of full positive degree at least three. A reduced exit arm
is the original path from its hub to an actual outside terminal, whose
internal bodies are genuine full-degree-two unloaded members of K.
An exit is transmitted when that arm has at least one internal body.

**Theorem. No reduced exit arm is transmitted.** Equivalently, all three
original cut edges are incident in K to three distinct actual hubs.
Their full degrees, the cycle rank, all internal chords and channels,
and all outside terminal identities and degrees are unrestricted.

In particular the theorem covers every location of a transmitted exit
in every cyclic three-port module, including arbitrary higher degrees
and cycle ranks. It is not merely a statement about a selected cycle
after other forces have been deleted.

## 2. Exact accepted inputs and elementary channel bookkeeping

The two geometric inputs are:

1. `THREE_PORT_CYCLIC_DISTINCT_EXITS_AND_FORCE_CONCENTRATION_2026_10_31.md`,
   Theorem 1: the three reduced exits of a cyclic full three-cut unloaded
   module end at three distinct actual hubs. Its original full-cut
   and contact-free endpoint prerequisites remain unchanged.
2. `DOMINANT_UNLOADED_CONTACT_PAIR_IS_CENTRAL_2026_10_31.md`: if an actual
   direct unloaded pair AB has magnitude d, one distinguished original
   exit force at each endpoint, and all other incident magnitudes total
   r_A+r_B<2d/29, its original common application p obeys |p|<15/16.
   Consequently every actual unit Z in the same disk obeys
   dist(p,Z)<469/240<2.

The entire new work argument and the full residual cut contradiction
are printed below. No occupied-cross theorem or planar embedding is
used in this new proof. The original contact means never change.

An unloaded body cannot have full degree one. Along any original path
of full-degree-two unloaded bodies, complete translation propagates one
magnitude and one signed normal. Torque propagates collinear actual
applications. Each internal body's support width in that normal is at
least one. A returning channel is impossible because its positive
signed widths would telescope to zero displacement.

Thus suppressing only these genuine paths gives a connected reduced
hub multigraph. The suppression is bookkeeping on the same original
equations. All internal bodies and their actual widths remain in the
work calculation. Every reduced exit ends at a hub; a path between
two outside terminals with no hub would be an entire separate component
of K and could not occur in the present connected cyclic K.

For a reduced internal channel e with k_e original internal transmitters,
its propagated magnitude is mu_e. The actual endpoint centers satisfy

\[
n_e\cdot(c_j-c_i)
 =h_i(n_e)+h_j(n_e)+\sum_{U\text{ internal}}2h_U(n_e)
 \ge1+k_e,                                      \tag{1}
\]

where h_i is the actual centered support halfwidth. The identical formula
holds for an exit arm, using its actual outside endpoint. This proof
allows any k_e>=0; it does not need to replace a long channel by an edge
or invoke the usual at-most-one-transmitter simplification.

Every original center has |c|<M=91/60. Indeed the farthest corner gives
|c|^2+|c|+1/2<=Q, and

\[
(91/60)^2+91/60+1/2-Q=31/57600>0.
\]

Let W be the total magnitude of internal reduced channels, C>0 the
total magnitude of the three exits, and put

\[
N=\sum_{\text{internal }e}k_e\mu_e,\qquad
A_{\rm exit}=\sum_{\text{exit }e}k_e\mu_e.
\]

Dot the complete reduced hub equations with their unchanged centers
and sum. Every internal channel contributes its full signed support
gap; move every exit gap to the same side. Formula (1) and the actual
outside-center bound give

\[
W+N+C+A_{\rm exit}<MC,
\qquad
W+N+A_{\rm exit}<\frac{31}{60}C.                 \tag{2}
\]

Repeated outside terminal identities do not affect this sum. No force
at an outside terminal is used or shortened. The strict sign comes
from its actual center bound and C>0.

## 3. A transmitted third exit forces one original pair to dominate

Assume, for contradiction, that one exit is transmitted. Name its
actual hub H and its magnitude z>0. By the distinct-exit theorem name
the other two actual exit hubs A and B. These are three different
original squares. The internal bodies on their exit arms are disjoint
from each other and from every other reduced channel.

Partition ALL internal reduced channel magnitudes as follows:

- P is the sum over channels whose two hubs are A and B.
- J is the sum over channels with exactly one endpoint in {A,B}.
- K_0 is the sum over channels with neither endpoint in {A,B}.

Consequently W=P+J+K_0. Apply complete translation at A and B, using
the triangle inequality for their respective distinguished exit forces.
Every A--B channel is counted twice and every J channel once, giving

\[
C\le 2P+J+z.                                    \tag{3}
\]

Since the H exit is transmitted, A_exit>=z. Combining (2) with (3)
therefore gives

\[
60(P+J+K_0+N+A_{\rm exit})<31(2P+J+z),
\]

and hence

\[
29J+60K_0+60N+29z<2P.                            \tag{4}
\]

Let d be the magnitude of the original DIRECT AB pair, with d=0 if
that pair is absent. There is at most one such pair in the original
body-pair graph. Every other reduced AB channel contains at least one
actual transmitter. If V=P-d, then V>=0 and N>=V. Substitute P=d+V
in (4), subtract 2V, and group the exact nonnegative remainders:

\[
\boxed{
29(J+2V)+60K_0+60(N-V)+29z<2d.
}                                               \tag{5}
\]

The left side is strictly positive because z>0. Thus d>0: AB is an
actual original direct contact, not an edge introduced by suppression.

At A and B distinguish their one original force along their respective
exit arms, acting at the actual immediate neighbors. All other original
incident forces except the AB pair have magnitude sum

\[
r_A+r_B=J+2V<2d/29.                              \tag{6}
\]

This equality counts every such original incidence: a channel incident
to A or B begins with its original positive force of its propagated
magnitude. No full degree is lowered and no weak positive force is
deleted. Equation (6) invokes the dominant-pair theorem at the actual
common application p of AB. It yields

\[
\operatorname{dist}(p,Z)<2
\quad\text{for every actual original square }Z. \tag{7}
\]

The derivation does not assume that AB is the only direct pair among
the three exit hubs. Direct AH and BH contacts, and arbitrary additional
internal channels, were fully included in J and K_0.

## 4. The unchanged residual full cut forces distance at least two

Remove A,B and the internal bodies on their two exit arms from the
vertex set K. This is only a choice of a region on which to sum the
unchanged equations; no physical body or original force is removed
from the packing.

Every remaining positive component not containing H has a nonempty
full cut only to A and B. The cut is nonempty by original connectedness.
An internal body of either removed exit arm has exactly its two arm
neighbors, so there is no hidden extra terminal from those arms.

Such a component is impossible: A and B contain p. If I is its complete
internal support work and C_cut>0 its total cut magnitude, dotting all
its complete unloaded translations with c_i-p gives

\[
0\le-I-C_{\rm cut}/2<0.
\]

Here every cut normal n from i to its terminal satisfies
n.(c_i-p)<=-h_i(n)<=-1/2. This common-point argument permits arbitrary
cut multiplicities and original mean endpoints.

Therefore all remaining members form one connected unloaded region L
containing H and its entire transmitted exit arm. Its FULL original
cut consists of arbitrary original edges to A,B and exactly the third
original cut edge T--Z, where Z is outside K. Orient that edge from T
to Z with original unit normal u and magnitude z.

Because this exit is transmitted, its last internal body T has genuine
full degree two. Its only neighbors are its predecessor on that arm
and Z. That predecessor is H or another internal arm body, never A
or B. Thus T has no original positive edge to A or B. This remains
true when AH or BH is itself a direct original pair.

Let F be the set of ALL members of L positively adjacent to A or B.
Summing all translations on L gives total outward force -zu to A,B.
Since T is not in F, summing the complete translations over F gives
vector sum zu over its edges to L minus F. Their magnitude sum is
therefore at least z. The full internal support work on L obeys

\[
I_L\ge z,                                       \tag{8}
\]

because each actual internal pair contributes its magnitude times a
support gap at least one. If C_L is the total magnitude of the complete
cut of L, its A/B portion has magnitude sum at least z, so C_L>=2z.

Now dot every complete translation on L with c_i-p. At a cut to A or
B the terminal contains p, giving the same support bound as above.
At T--Z insert its actual support identity. The full sum gives

\[
z\left(\min_{x\in Z}u\cdot x-u\cdot p\right)
\ge I_L+\sum_{\mathrm{full\ cut}}\mu h_i(n)
\ge I_L+C_L/2
\ge2z.                                         \tag{9}
\]

Thus every actual x in Z satisfies u.(x-p)>=2, and

\[
\operatorname{dist}(p,Z)\ge2.
\]

This contradicts (7). All outside terminals and internal components
have been accounted for, including repeated outside terminal identities.
The assumed transmitted exit is impossible, proving the theorem.

## 5. Whole unicyclic consequences and exact remaining rows

In
`THREE_PORT_UNICYCLIC_UNLOADED_MODULES_AT_MOST_FIVE_WITH_COMPLETE_INTERNAL_ENDPOINT_SCOPE_CORRECTED_2026_10_31.md`,
t counts transmitted triangle links and s counts transmitted exit arms.
The full necessary table before the latest exclusions is

\[
(t,s)=(0,0),(0,1),(1,0),(1,1),(2,0),
\]

with two inequivalent exit positions in (1,1). The present theorem
excludes EVERY s=1 row, including both original positions in (1,1),
with every original transmitter width, mean and external terminal.

The whole (2,0) row is already excluded by Section 8 of
`THREE_PORT_RANK_TWO_AND_ALL_SUBCUBIC_MULTICYCLE_EXCLUSION_2026_10_31.md`.
Consequently only

\[
\boxed{(t,s)=(0,0)\quad\text{or}\quad(1,0)}
\]

remain in the original unicyclic table. They have respectively three
or four actual module bodies and three direct original exits.

The broader theorem excludes transmitted exits at arbitrary cyclic rank
and arbitrary hub degrees. It does not exclude these two remaining
unicyclic geometries, every direct-exit higher-degree module, cuts of
size four or more, or an original nine-square coarse parent without
a separate complete caller. No original status follows merely from
the reduction in this manuscript.

All mathematics above is a continuous hand argument. The complete proof
requires an independent source-level review before adoption. File hashes
and document inventories record identity only.
