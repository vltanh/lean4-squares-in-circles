# Root review: complete D-leaf C5 separated-load exclusion

Date: October 26, 2026.

**Result: PASS for the entire original M6.B5L.C5.L13.D obligation.**
I independently read the full saved source
D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md, its separate review, and
the local proper-concurrence, unique-corner turn and parallel-load
prerequisites. The proof is an exclusion of the actual six-body core,
so it includes every placement of the three additional physical units.
The S companion remains open.

## 1. Root force and concurrence are genuinely preserved

The true D root A contains zero in its open interior. The actual
A--U--C endpoint half-planes and the sharp unit-center bound give
0<h_A(n) and h_A(n)+w_U<=d. The complete widths 1 and sqrt(2)
therefore force w_U=1, d>1 and h_A(n)<=delta. The positive horizontal
widths of A give |n_x|<1/15 and |n_y|>14/15. Reflection fixes n_y>0.

The unchanged root equation includes the real positive leaf force.
It makes the other cycle normal have negative vertical component.
Torque puts the intersection of the two nonparallel cycle lines on
the actual leaf line. Before its radial sign is known, its proper
lengths are a/n_y and b/(-m_y), both positive. This is not a
degree-two or falsely loaded-root argument.

I reconstructed both sign cases in Section 2. When B and C are
nonparallel, their true degree-two proper radial concurrences and
the actual reserves give three positive channel coefficients. A
zero direct coefficient would identify a genuine positive B radial
point with a multiple of the independent leaf direction. The exact
triangle coefficient of the external leaf resultant at A is
ell_AC*ell_BA/(ell_AC+ell_CB+ell_BA)>0.

With one parallel loaded body, its two original applications keep
their distinct transverse coordinates and original positive weights.
The local parallel classification makes both outward normals opposite
the actual circle resultant. Its torque fixes opposite nonzero
transverse signs. The other true concurrence supplies nonzeroness;
the remaining positive proper connection and full endpoint equations
then give the same positive sign for q_A and the leaf resultant.
No concurrence is invented at the parallel body.

## 2. Turns and the direct-neighbor local extension

The negative-n_x alternative gives q<-1/4+1/14<0 and is impossible.
Thus n_x>=0, the direct normal is (-c,-t) with c,t>0, and the actual
direct port is (-s,-b). The exact support gives a<1/56 and b>55/56.
It follows that its norm is strictly above rho=R-sqrt(2) and strictly
below sqrt(d^2+1/4). These two different comparisons are both used.

The original common moment is mu*q*n_y>0. The root turn is strictly
between zero and pi/2. At a nonparallel loaded body, positive proper
radial concurrence gives a positive turn below pi; a parallel body
has directed-force turn pi. Three such turns make exactly one full
circuit. The argument does not need bounded radial concurrence.

The local unique-corner theorem at C applies to its real transmitter
neighbors. B has a direct neighbor, so I checked the separately
supplied gap: coincident nonparallel applications would put q_B at
the opposite radial-D vertex, of norm rho, contrary to the actual
direct-port norm. The remaining own-axis support cover is exactly
the local calculation in SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md,
Section 1. It uses no force equation at A. Its three ordered
non-axis vertex pairs and the identity X(1-X)+Y(1-Y)>=0 give
theta_B<=3pi/4, and a turn above pi/2 puts both ports on one inner
side. Original side means and their endpoints are included.

These bounds exclude unique/unique immediately by the genuine turn
sum. For radial B, the strict small direct-port norm instead puts
that port inside its inner face and forces its actual radial axis
to be the original direct normal. No individual circle weight is
changed.

## 3. Every ordered radial mask and width is exhausted

For radial C, outer or tangential channel supports are excluded by
the actual far-body width and containment. If n_x>0, the actual root
point is (rho,a). An inner-axis C contact would give it norm below
3/5; an inner-vertex contact would make its far norm too large.
The displayed strict squared comparisons are valid on the full
radius window. Hence n_x=0 and the original ports are (q,a) and
(q,a+1). The correct C frame satisfies u>=0, v>60/61 and a
negative transverse incoming coordinate, including the inner-axis
mean case.

For reserve-one V, positive common moment selects the plus inner
vertex of C. Its actual displacement to B puts B's other port
strictly above a, while its direct port has height a-1. If B is
radial, both ports must lie on its inner face; if B is unique, the
turn sum forces its turn above pi/2 and invokes the checked same-side
bound. Both contradict separation greater than one.

For diagonal V, the original compatible endpoint convention gives
the common endpoint axes. Only C's inward radial axis remains.
B's original support toward A then fixes its e-coordinate, forcing
e dot (p_CU-p_BA)=sqrt(2). The actual difference is (q+s,2),
whose projection exceeds 120/61>sqrt(2). All original diagonal
means remain arbitrary. This excludes every physical-radial C mask.

The final unique-C/radial-B mask has d=sc+bt>1. Since b>s and
s+b<sqrt(2), the exact symmetric decomposition forces t>c. A
strictly positive n_x would instead force c/t>1, so the root
channel is again vertical. A reserve-one V then requires a center
gap greater than 3/2+3/(2sqrt(2))>1+sqrt(2), contradicting its
actual reserve and the two unit circumradii. A diagonal V puts
C's actual root port below height sqrt(2)-1/2<1, while its real
root channel fixes height a+1>1. Both full width alternatives fail.

## 4. Original-gate audit

The original label covers cycle 0-1-2-3-4-0, root 0, block loads
1 and 3, and a genuine D leaf. The source uses exactly those roles:
A=0, B=1, V=2, C=3, U=4. It keeps A's true degree three, the
positive leaf force, both true unloaded transmitters, every actual
B/C mask and zero individual corner-weight endpoint, the entire
side-interior D-root slider and every original contact mean.

No completion hypothesis was needed to exclude the core, so all
three physical extras are retained. The gate can be checked without
adding a new ID. The S companion, C5 parent, larger rooted-block
parent, coarse cells, unrestricted theorem and equality classification
remain open. This proof and review add no computational certificate,
Lean compilation, workflow run or numerical premise.
