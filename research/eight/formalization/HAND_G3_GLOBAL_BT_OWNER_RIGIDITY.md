# Every global BT witness has owner 2 or 3

## 1. The unrestricted owner conclusion

Work on the actual G0--G2 boundary cycle at
\[
 Q=9789/2500,\quad c_0=\sqrt{Q/2}-1/2,\quad
 R=\sqrt Q,\quad \kappa=49/50,\quad T_*=16761/4520.
\tag{1}
\]
Retain the same G1 marker at each shared vertex and its
original signed separating witnesses. Normalize E by
\(y_E=-b_E\le0\), as in the surviving quarter-word theorem.
No mismatch bound, tangent cut, frame ordering or other
unproved owner restriction is assumed.

**Global BT-owner theorem.** Every originally feasible BT
witness has owner 2 or 3. In addition,
\[
                              y_B<0.
\tag{2}
\]
The assertion includes weak separating contacts and all
ties between original witnesses.

The proof excludes each original BT0/1 witness individually.
Its complementary return path includes every GA and EH
owner, every remaining HG witness, both intermediate signs,
and both radial kinds. Thus no preferred mixed owner is
an input to the exclusion.

## 2. A common charge and the completed BT0 case

Suppose an original BT0/1 witness is feasible. The global
zero--quarter propagation theorem
HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER.md gives
\(y_A=b_A>0\). The generic quarter-owner sign theorem
also gives \(y_T=b_T>0\). The global DE theorem already
gives \(y_D=-b_D<0\) and DE owner 2 or 3. The original
AB and TD witnesses have owner 0 or 2 by zero-primary
exclusion. B may still have either sign in this argument.

Write the four consecutive errors as
\[
 v=d_{AB},\quad x=d_{BT},\quad w=d_{TD},\quad y=d_{DE}.
\]
The charge to be bounded is
\[
                  C_4=\pi+v+x+w+y+\kappa b_A+F_E.
\tag{3}
\]
The global linear-A return theorem proves
\[
                         2\pi-C_4>103/40.
\tag{4}
\]
Consequently it suffices to prove \(C_4>T_*\), since
\[
                       T_*+103/40=710/113>2\pi.
\tag{5}
\]

For BT0, the two complete path theorems already give this:

- HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md covers every
  DE2 witness, and either DE owner when E is outer. It also
  covers a positive DE3 error for core E by the zero-type
  dual comparison.
- HAND_G3_GLOBAL_BT0_CORE_E_DE3_PATH_EXCLUSION.md covers
  core E with negative DE3, using the saturated-prefix
  monotonicity and aligned-prefix base scalar proved in
  its two companion notes.

These cases exhaust all original DE witnesses and radial
kinds at E. Their AB comparisons retain both original
owners and both B signs.

## 3. The DE2 tail can use a TD multiplier at least 3/5

The negative-BT1 comparison needs the TD multiplier c in
\([3/5,\kappa]\). This section verifies that the completed
tail bounds can meet that condition without weakening
their conclusion.

In the DE2 path theorem, let q denote the sum of retained
negative errors in the tail, with \(0\le q\le.7\). Keep
its same E-chart choices
\[
\begin{array}{c|ccc}
\text{E chart}& C\text{ or }L&M&H\\ \hline
e&.9449&.797&.64\\
m&0&.0458&.134\\
c_{\rm old}(q)&.567+.445q&.52+.365q&.46+.25q .
\end{array}
\tag{6}
\]
Here \(F_E-eb_E\ge m\), exactly as proved there.
Replace only the TD weight by
\[
                         c(q)=\max\{3/5,c_{\rm old}(q)\}.
\tag{7}
\]
Each choice satisfies \(3/5\le c\le\min(\kappa,e)\).
Thus all its preceding support, positive-error and
negative-error concentration arguments remain valid.

Above the joining point, its two final scalar functions
\(B(q),D(q)\) are unchanged and strictly exceed \(T_*\).
The three joining points are respectively
\[
                         33/445,\qquad16/73,\qquad14/25.
\tag{8}
\]
Below the join c is constant at 3/5. The norm-concavity
lemma of that path theorem makes both B and D concave
on this whole lower interval. It therefore suffices to
check zero and the join; the latter is already covered
by the original affine scalar proof.

At zero the two functions agree:
\[
 B(0)=D(0)=\pi+\frac52\kappa+\frac65+\frac32 e+m
       -R\{\sqrt{\kappa^2+9/25}+\sqrt{e^2+9/25}\}.
\tag{9}
\]
Use \(\pi>3.14159\), \(R<1.979\), and the rational upper
bounds
\[
 \sqrt{\kappa^2+9/25}<1.14909,
\]
\[
 \sqrt{e^2+9/25}<
 \begin{cases}1.11931,&C,L,\\ .99761,&M,\\ .87727,&H.\end{cases}
\tag{10}
\]
The positive-square reserves are, with common denominator
\(10^{10}\), respectively
\[
                         78281,\quad188661,\quad167121,\quad26529.
\]
The resulting exact positive margins in (9) above \(T_*\)
are respectively
\[
 \frac{3274333}{282500000},\qquad
 \frac{86314891}{1130000000},\qquad
 \frac{472446557}{2825000000}.
\tag{11}
\]
This proves the full DE2 tail with (7).

An outer E with negative original DE3 still supplies an
actual DE2 witness by Section 4 of that path theorem.
A positive original DE3 error can still be set to zero
in its dual because every e in (6) is at most kappa.
All these cases therefore inherit the strengthened tail.

For core E with negative DE3, the completed separate tail
already chooses \(c=.6+.4p\), where p is its retained
negative prefix-tail error. It lies in \([.6,.88]\).
Thus both complete tails now have the needed multiplier.

## 4. Nonnegative original BT1 error

Suppose \(x\ge0\). Apply
HAND_G3_POSITIVE_BT1_DUAL_COMPARISON.md with the tail
multiplier chosen for its remaining errors. Give BT weight
\(\kappa\cos x\), and choose the eventual AB multiplier
\(\kappa\) for \(v\ge0\), or \(\kappa\sec(-v)\) for \(v<0\).
The comparison is independent of this choice and of the
original AB owner.

Its signed B support retains the primary lower bound
\(a_B\ge447/800\); its circle subadditivity bound is valid
on that domain. Thus the subsequent negative-AB comparison
does not invoke a primary restriction that was discarded.
The positive-T support uses its full sorted disk.

The result has BT error zero and BT weight kappa. The
same original-AB comparisons then remove v, after which
the remaining full-circle T/D expression is the completed
BT0 tail at BT error zero. Section 2, or its strengthened
weights in Section 3, gives \(C_4>T_*\).
Every operation here compares dual lower bounds; no
altered frame configuration is asserted to be feasible.

## 5. Negative original BT1 error: all AB branches

Put \(x=-z<0\). First remove positive TD and DE errors
in the weighted expressions using the same pointwise
comparisons as in the completed tails. They do not change
AB, BT, or any center. Negative DE3 at an outer E is
converted to the actual DE2 witness as before.

The remaining TD error is \(-u\le0\), and the tail
multiplier c is fixed during the following prefix
comparisons. It depends only on those unchanged tail
parameters and satisfies \(3/5\le c\le\kappa\).

The exact prefix alternatives are as follows.

1. For either AB owner with \(v\le0\),
   HAND_G3_NEGATIVE_BT1_PREFIX_COMPARISONS.md proves
   \(b_A+\sec z\,a_T\ge R_1(z)\), together with a
   nonnegative remainder in the angular charge.
2. For AB0 with \(0\le v\le z\), the same note gives
   the necessary cap at \(r=z-v\), with the exact
   prefix angle \(-r\), and a positive extra charge
   when v is positive.
3. For AB0 with \(v\ge z\), its direct full-circle
   comparison gives the aligned-prefix charge already.
   No stronger coordinate cap is used in this branch.
4. For AB2 with \(v\ge0\),
   HAND_G3_POSITIVE_AB2_NEGATIVE_BT1_SOFT_CAP.md retains
   the additional charge
   \((2-\kappa)(b'-c_0)_+\), where \(b'=1+y_B\).
   Its complete support argument gives the same
   aligned-prefix charge without assuming \(b'\le c_0\).

In the first two alternatives,
HAND_G3_NEGATIVE_BT1_HIGH_PRIMARY_DUAL_TRANSPORT.md
uses the actual necessary cap and the same T circle.
It shows that the negative prefix parameter can be
removed for either TD owner. Its c restriction is
satisfied by Section 3. The fourth alternative joins
that same theorem on its genuine high-primary domain
and proves its complementary domain by a strictly
positive envelope derivative. All four alternatives
therefore give the aligned-prefix full-circle bound.

The D/E data and tail parameters are unchanged.
Their retained negative errors total less than .7 by
the global total-variation theorem. The strengthened
DE2 tail of Section 3, or the complete core-E/DE3 tail,
now proves \(C_4>T_*\).

This exhausts both original AB owners, every sign of v,
every original TD/DE owner, both B signs and both radial
kinds at every vertex.

## 6. Close the cycle and recover the B sign

Sections 2, 4 and 5 prove \(C_4>T_*\) for every originally
feasible BT0/1 witness. Equations (4)--(5) contradict the
exact full charge \(2\pi\), so neither original owner
can be feasible. All remaining BT witnesses have owner
2 or 3.

The generic quarter-owner sign theorem in
HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md then forces
the source B to have strictly negative signed tangent.
This proves (2). For an actual boundary cycle at
\(5/2\le q<Q\), the unconditional fixed-ray expansion in
[the fixed-ceiling transfer theorem](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md),
Section 2, preserves every initially feasible signed axis,
frame, center ray, quarter increment and radial kind while
expanding outer centers to Q and fixing core centers. Thus
each original lower-radius boundary witness and the B sign
are subject to the same exclusion. This transfer is applied
after any initial recession boundary construction.

This is a global quarter-owner theorem. It does not yet
choose the GA/EH mixed owners, prove the needed ordering
or align arbitrary original zero edges. Those remain
separate entry steps for the unrestricted sharp theorem.
Every scalar premise above is a displayed continuous
inequality or a whole-interval rational polynomial
bound; no configuration mesh, generated row inventory,
Lean compilation or numerical acceptance result is used.
