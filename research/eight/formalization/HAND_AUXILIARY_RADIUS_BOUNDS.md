# Auxiliary radius bounds and the exact stationary interface

## 1. Radius, squared radius, and the public constant

The packing problem concerns a disk radius R. Throughout the
stationary equations and the geometric certificate chain,
\[
                              q=R^2
\tag{1}
\]
is the squared radius. The exact optimal constant is q*, and
the optimal radius is \(R_*=\sqrt{q_*}\).

The rational endpoints below are proof bounds on q. They are
not substitutes for q* in the stationary coordinates or in an
equality packing. In particular the number denoted r in
\[
                              r=\sqrt{q-u^2}
\]
is a corner coordinate in the stationary chain; it is not the
containing radius R.

The main theorem can name the stationary triple constructed in
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
and use its exact equations without displaying these arithmetic
bounds. This appendix supplies its certified branch and the
domain checks for downstream theorems. That presentation does
not claim uniqueness of the stationary equations on unspecified
radical or angle branches.

## 2. Exact catalog and existing aliases

For this interface only, use the descriptive names in the
first column. Existing certificate files keep their original
symbols and exact numbers.

| Interface name | Exact value | Existing aliases | Role |
|---|---:|---|---|
| \(q_{\mathrm{broad}}\) | \((79/40)^2=6241/1600=3.900625\) | \(q_b\) in stationary existence; q_minus in the broad stationary-family proof | Lower endpoint of the broad analytic strip for positive radicals, position convexity and stationary-envelope uniqueness. |
| \(q_{\mathrm{low}}\) | \(19577/5000=3.9154\) | \(q_L\), qL; lower endpoint 3.9154 in several force estimates | A certified squared radius below q*; lower endpoint of same-radius transport bounds and stationary force rectangles. |
| \(q_{\mathrm{trial}}\) | \(1957767069/500000000=3.915534138\) | \(q_U\) in stationary existence; \(Q_1\), Q1 elsewhere | A fixed rational trial with negative circle defect; sharp rational upper endpoint used in several nominal stresses and entry estimates. |
| \(q_{\mathrm{cap}}\) | \(9789/2500=3.9156\) | \(Q\); \(Q_0\) in stationary existence and several terminal notes; 3.9156 in force rectangles | Fixed ceiling for central-core, frame, word, owner and diagonal classifications, and a common numerical upper bound for local geometry. |

All terminating decimals in this table are exact rational
numbers. The established inequalities are
\[
 \frac52<q_{\mathrm{broad}}<q_{\mathrm{low}}<q_*
 <q_{\mathrm{trial}}<q_{\mathrm{cap}}<4.
\tag{2}
\]
The actual interval endpoints in the variable-radius
[primary-pair transport theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
are \(q_{\mathrm{low}}\) and \(q_{\mathrm{trial}}\).
The
[complete primary-owner entry theorem](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md)
works on \(q_{\mathrm{low}}\le q\le q_*\). Thus q* itself is
an allowed actual working ceiling for both theorems.

There are two historical notational traps.

* Section 1 of the older
  [fixed-ceiling transfer note](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md)
  writes \(q_-=7831/2000=3.9155\). It is different from both
  \(q_{\mathrm{low}}\) and \(q_{\mathrm{broad}}\). The new assembly
  imports that note's unconditional fixed-ray monotonicity and
  its fixed-witness boundary argument; it does not import the
  historical lower bracket or its old small-mismatch capture
  hypothesis.
* The
  [stationary force and square-completion note](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md)
  calls an input squared ceiling \(r_0\). Its inequality
  \(r_0\ge q_*\) is about squared radii, despite the letter r.
  Its \(Q_0\) is \(q_{\mathrm{cap}}\). Local polynomial
  coefficients called \(Q_0'\), \(Q_1'\), etc. in the same note
  are not radius constants.

These are an alias map, not instructions to replace numbers
inside established certificates.

## 3. What each bound proves

### 3.1. The broad stationary strip

[Stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md),
Sections 1--2, works on the single product
\[
 q_{\mathrm{broad}}\le q\le q_{\mathrm{cap}},\qquad
 \frac{87}{100}\le u\le\frac{11}{10},\qquad
 0\le t\le\alpha,\qquad \alpha=\arctan(1/5).
\tag{3}
\]
It proves that all four circle radicals are positive, that
\(F_{uu}>0\), and that the position derivative has opposite
strict signs at the two u endpoints. Consequently the actual
position minimum exists uniquely and is interior throughout
this strip.

The same note, Section 6, combines this with
[stationary geometry](STATIONARY_GEOMETRY.md) and the broad
critical-point argument in
[the stationary-family proof](../HUMAN_FAMILY_CLOSURE.md).
Every actual envelope critical tilt is a strict minimum. There
is at most one such tilt; the radius minimum is strictly
decreasing in q. This identifies the constructed stationary
zero uniquely on the certified branch.

The broad lower endpoint is an analytic device, not a universal
lower-bound theorem for arbitrary packings by itself. Its square
form means that the corresponding radius is the simple rational
number \(79/40\).

### 3.2. The lower sign and rational upper trial

The same stationary existence proof defines the actual minimum
\[
 H(q)=\min_{0\le t\le\alpha}
            \min_{87/100\le u\le11/10}F(q,u,t).
\tag{4}
\]
One continuous circle stress proves
\[
                 H(q_{\mathrm{low}})>0.
\tag{5}
\]
A single explicit rational chain and a rational half-angle
trial prove
\[
                 H(q_{\mathrm{trial}})<0.
\tag{6}
\]
The intermediate value theorem gives a zero between them.
Interior endpoint signs give \(F=F_u=F_t=0\), and the preceding
uniqueness argument selects q*.

The exact choice of the lower endpoint has a transparent role
in its sign proof. The stress mass exceeds one, its polynomial
lower envelope exceeds \(-1/8000\), and
\[
 q_{\mathrm{trial}}-q_{\mathrm{low}}
       =\frac{67069}{500000000}>\frac1{8000}.
\]
The resulting positive reserve is
\[
 -\frac1{8000}
       +(q_{\mathrm{trial}}-q_{\mathrm{low}})
       =\frac{4569}{500000000}>0.
\tag{7}
\]
The upper trial's exact rational coordinates and integer circle
comparisons are retained in Section 4 of the existence proof.
They need not appear in the main stationary model.

The upper trial also gives an actual eight-square packing, as
checked independently in Section 7 there. It is an upper-bound
witness, not the sharp equality configuration. The latter is
evaluated at the actual stationary triple.

### 3.3. The fixed geometric ceiling

The central-core, pair-gap, exterior-frame, word and owner
proofs are certified at \(q_{\mathrm{cap}}\). Their numerical
supports, potentials and scalar comparisons were proved for
that ceiling or below it. Some actual boundary classifications
specifically require their outer states to be on that ceiling.

The bridge from an actual q* boundary cycle to the fixed
ceiling is the unconditional fixed-ray expansion in Section 2
of
[the transfer theorem](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md).
Its proved squared-radius range is
\[
                              \frac52\le q\le4.
\tag{8}
\]
By (2), expanding from q* to \(q_{\mathrm{cap}}\) is eligible.
Every initially feasible signed axis survives. Frames, rays,
signed ratios, cyclic gaps and radial kinds also survive.

Returning to the already known q* cycle transfers the
classification facts without replacing its actual outer-circle
equations. The
[sharp-ceiling assembly](HAND_SHARP_RADIUS_BOUNDARY_ASSEMBLY.md)
spells out this order.

The value 4 in (8) is only the upper endpoint of this elementary
expansion lemma. It cannot replace \(q_{\mathrm{cap}}\) in all
the owner, frame and scalar certificates without new proofs.

### 3.4. Force estimates and local entry domains

The stationary force estimates use the fixed rectangle
\[
 q_{\mathrm{low}}\le q\le q_{\mathrm{cap}},
 \qquad .895\le u\le.94,\qquad
 .1\le \tan t\le.164.
\tag{9}
\]
The constructed stationary triple lies in that rectangle by
the position and tilt theorems. Positive anchor masses and
contact weights then follow from the proved whole-rectangle
comparisons.

Other local entry proofs use \(q_{\mathrm{trial}}\) as a sharper
upper bound or \(q_{\mathrm{cap}}\) as a coarse support bound.
The hard-owner theorem initially separates the trivial
\(q>q_{\mathrm{trial}}\) range and uses a lower working ceiling
when stated for arbitrary q. Those steps are internal to its
general statement. Applying it at q* requires only (2), with
no new working floor in the unrestricted assembly.

## 4. The core radius and frame cap are auxiliary geometry

Use
\[
        \rho_{\mathrm{core}}=\frac1{12},\qquad
        \vartheta_{\mathrm{cap}}=\frac7{10}.
\tag{10}
\]
Their meanings differ from those of the squared-radius
bounds.

| Constant | Quantity and units | Exact role |
|---|---|---|
| \(\rho_{\mathrm{core}}\) | A length, measured in unit-square side lengths | The central square contains the closed disk of this radius in its open interior. Exterior squares avoid this core; the necessary boundary reduction may put an exterior square on its boundary. |
| \(\rho_{\mathrm{core}}^2=1/144\) | Squared length | Squared distance in the rounded true-core equation. It is not a containing-disk ceiling. |
| \(\vartheta_{\mathrm{cap}}\) | An angle in radians | A strict real-frame spread and positive/negative error-variation bound obtained from the exterior-frame and cyclic-return proofs. It is not the stationary tilt t*. |
| \(1/2\), \(1\) | Half a side and a side | Structural unit-square geometry used in every support width and contact equation. These do not come from a proof cutoff. |

For sorted own-frame center magnitudes \(a\ge b\ge0\), the
true-core boundary is exactly
\[
              (a-1/2)_+^2+(b-1/2)_+^2
                        =\rho_{\mathrm{core}}^2.
\tag{11}
\]
Its flat side therefore has
\[
              a=\frac12+\rho_{\mathrm{core}}=\frac7{12}
              \qquad(b\le1/2).
\tag{12}
\]
The shifted flat-core corner coordinate used in several
negative-primary transports is
\[
                         1+\rho_{\mathrm{core}}=\frac{13}{12}.
\tag{13}
\]
These are derived aliases of the chosen core radius, rather
than additional independent geometric constants.

True-core avoidance gives the lower primary-coordinate bound
\[
                  a\ge\frac12+
                          \frac{\rho_{\mathrm{core}}}{\sqrt2}.
\tag{14}
\]
A core center has norm at most
\(\sqrt2/2+\rho_{\mathrm{core}}<4/5\), which is the only
core-size input needed by the fixed-ray expansion proof.

The value \(\vartheta_{\mathrm{cap}}\) comes from the actual
orientation-tour budget in
[the exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md).
The scalar transport inequalities are proved on its full
angle domain. Their hypotheses cannot simply be enlarged
to \(\pi/4\) because the frames live modulo quarter turns.

The symbol h is overloaded in older notes: it can mean this
fixed cap, \(\tan t\) in a stationary computation, or the
orientation cost
\((|\sin\phi|+|\cos\phi|-1)/2\). The interface uses
\(\vartheta_{\mathrm{cap}}\) for the fixed bound and keeps
the other meanings local.

The choice \(\rho_{\mathrm{core}}=1/12\) is not a padding
requirement in the original packing problem. Likewise
\(\vartheta_{\mathrm{cap}}\) is a conclusion of capture, not
a restriction imposed on the original square orientations.

## 5. Derived outer-circle symbols

For an actual squared ceiling q, define
\[
 \begin{aligned}
 R(q)&=\sqrt q,\\
 a_{\max}(q)&=\sqrt{q-1/4}-1/2,\\
 c(q)&=\sqrt{q/2}-1/2.
 \end{aligned}
\tag{15}
\]
On a sorted outer q state,
\[
 (a+1/2)^2+(b+1/2)^2=q,\qquad
 c(q)\le a\le a_{\max}(q),\qquad 0\le b\le c(q).
\tag{16}
\]
The uniform-radius transport note calls these \(R_q,a_q,c_q\),
and also uses
\[
 A_q=a_q+1/2=\sqrt{q-1/4},\qquad
 d_q=A_q-1=a_q-1/2.
\tag{17}
\]
Fixed-ceiling marker proofs often write
\(a_0=a_{\max}(q_{\mathrm{cap}})\) and
\(c_0=c(q_{\mathrm{cap}})\). They are support coordinates
evaluated at a chosen ceiling, not separate radius bounds.

In particular an actual outer E at q* satisfies
\[
 a_E\ge c(q_*)\ge\max\{b_H,b_D\}
\]
whenever H,D are sorted and contained at that ceiling. A core
E has \(a_E\le1/2+\rho_{\mathrm{core}}\). These are the two
branches of the hard-owner radial alternative.

## 6. What can be simplified without changing any certificate

The
[exact-sharp-ceiling assembly](HAND_SHARP_RADIUS_BOUNDARY_ASSEMBLY.md)
makes one substantive proof simplification. For a hypothetical
packing at original squared ceiling \(q_{\mathrm{orig}}\le q_*\),
construct the fixed-witness boundary representative directly at
q*. After classification and conditional source equality, apply
the stationary dual to the untouched original centers:
\[
 q_*\le
 q_*+\sum_i\mu_i|p_i-P_i|^2
 =\mathcal D
 \le q_{\mathrm{orig}}.
\tag{18}
\]
This removes the lower-floor operation
\(\max(q_{\mathrm{orig}},q_L)\) and the separate low-radius
case from the unrestricted proof. The internal lower estimate
still certifies that q* belongs to the established entry domains.

The remaining simplifications are presentation choices with
precise scope.

* The main constant can be the unique stationary triple
  constructed on the certified branch (3). Its arithmetic
  isolation belongs here. The stationary equations need not
  be accompanied by a long rational radius interval in the
  theorem statement.
* A simple descriptive consequence is \(79/40<R_*<2\).
  It is not, by itself, a replacement isolating domain for the
  stationary equations. No uniqueness statement on every
  branch with \(R<2\) has been proved here.
* The core-generated slider cutoffs in an economical equality
  chart can be omitted from a public model that instead imposes
  actual disk containment and all pairwise separating-axis
  constraints on the displayed five-parameter family. Such a
  fully geometric domain is exactly feasible by definition.
  It must retain all those constraints; deleting the core
  cutoffs from a reduced domain without restoring its omitted
  exterior-pair checks would require a separate proof.
* For squares of common side length \(\ell>0\), rescaling gives
  optimal radius \(\ell\sqrt{q_*}\). Every squared proof ceiling
  scales by \(\ell^2\), every core length by \(\ell\), and angles
  are unchanged. This is an exact similarity, not a new
  numerical parameter range.

No existing certificate number is modified or claimed
unnecessary inside its original proof.

## 7. Parameterized interface and its limitation

The final logical interface is independent of the particular
decimal endpoints. For a proposed squared ceiling \(\sigma\),
suppose one has:

1. A stationary configuration at \(\sigma\) with positive
   normalized anchor masses, positive contact weights, and
   zero forces on its free intermediates.
2. A fixed-witness boundary construction and classification
   valid for every packing contained at \(\sigma\).
3. A necessary-cycle entry and source-equality theorem at
   \(\sigma\) that returns the original physical frames and
   initially selected normals to their stationary values.

Then exactly the argument of (18), with \(\sigma\) in place
of q*, proves every original containing squared radius at
least \(\sigma\). The original-center stationary dual also
classifies its equality cases once the remaining feasible
parameter domain is supplied.

This is a parameterized implication between proved geometric
statements. It does not assert that the present force weights,
marker coefficients or transport certificates work unchanged
on an arbitrary neighborhood of radii, core sizes or frame
caps. The numerical audit needed to instantiate it at q* is
precisely the map above. Enlarging that instantiated domain
would require checking the affected certificate hypotheses;
the cleaner public interface makes no such enlargement.

