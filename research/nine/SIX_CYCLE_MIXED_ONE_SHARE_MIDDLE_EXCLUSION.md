# Mixed unique-corner C6: the middle one-share placement cannot close

Date: October 26, 2026.

**Status: complete hand contact-type exclusion, accepted after independent
saved-source and physical-scope review.** See
`REVIEW_C6_CONTACT_TYPE_CLOSURES_ROOT_2026_10_25.md`. This excludes one complete
placement of a genuine share in the all-unique alternating all-side C6.
It does not exclude the entire one-share family, the two-share family,
or their three-extra completion obligations. No original roadmap gate
is newly checked by this source alone.

Retain all nine physical squares, every original positive force, every
actual shared mean, the selected common certificate and each physical
circle mask. The three alternating loaded units have one actual circle
corner each. The three intervening unloaded transmitters retain their
true degree-two equations and side-normal reserve one. The three extra
squares and all their original geometric constraints remain present.

Use the strict-turn and actual side-mean normal forms in
`SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md` and
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`.

## 1. Precisely the contact type being excluded

Write `f_i=mu_i n_i`, with `mu_i>0`, and let the counterclockwise turn
from `n_(i-1)` to `n_i` be `theta_i`. Thus

\[
 \pi/2<\theta_i\le3\pi/4,\qquad
 \theta_0+\theta_1+\theta_2=2\pi.
\tag{1}
\]

The directed inner side of loaded square `i` has unit direction `u_i`,
actual application chord `ell_i u_i`, and far-corner bit `chi_i`.
The exact channel equations imply

\[
                 \sum_{i=0}^2(n_i+\ell_i u_i)=0.
\tag{2}
\]

A cyclic relabeling and, if needed, a reflection followed by reversal
of the whole cycle reduce any nonconstant bit pattern to

\[
                (\chi_0,\chi_1,\chi_2)=(1,1,0).
\tag{3}
\]

Under the reflection the directed side reverses and its base changes
from `b` to `T(b+u)`, so the actual corner bit becomes `1-chi`.
This operation also carries the genuine share and its actual mean.

This source considers precisely the case in which the only shared
loaded unit in (3) is unit 1. Its share is outgoing, on the original
interface `S_1 W_1`. Units 0 and 2 are nonshared. Consequently

\[
 \ell_0=\ell_2=1,\qquad
 0<\ell_1\le1,\qquad u_1=-Jn_1.
\tag{4}
\]

Here `J` is counterclockwise rotation by `pi/2`. Formula (4) is the
actual mean-preserving shared normal form. In particular the genuine
endpoint-mean share with `ell_1=1` remains in this domain.

## 2. Angular bounds for the two unchanged singleton units

For clarity, the elementary angular bounds from
`SIX_CYCLE_ALTERNATING_UNIQUE_SINGLETON_EXCLUSION.md`, Section 4,
are reproduced here. At a nonshared loaded unit rotate the incoming
normal to `(1,0)`, and write its incoming and outgoing positive force
magnitudes as `a,b`. The support vector determining `u=g/|g|` is

\[
 \begin{array}{ll}
 g=(a+b\sin\theta,\ a-b\cos\theta),&\chi=1,\\
 g=(b(\cos\theta+\sin\theta),\ a+b(\sin\theta-\cos\theta)),
      &\chi=0.
 \end{array}
\tag{5}
\]

For `pi/2<=theta<=3pi/4`, its angle `eta` from the incoming normal
satisfies

\[
 \theta-\pi/2\le\eta\le\pi/4\quad(\chi=1),
 \qquad
 \theta-\pi/4\le\eta\le\pi/2\quad(\chi=0).
\tag{6}
\]

These follow directly from the positive coordinates in (5), or by
comparing the slopes with the indicated endpoint rays. The boundary
`theta=3pi/4` is included; a zero first coordinate in the bit-zero
formula gives `eta=pi/2`.

Now rotate the full packing so that the force-normal angles are

\[
 \arg n_0=0,\quad \arg n_1=\theta_1,
 \quad\arg n_2=2\pi-\theta_0.
\tag{7}
\]

At unit 0, the bit-one interval in (6) gives an absolute angle for
`u_0` in `[3pi/2, 9pi/4-theta_0]`, a fourth-quadrant interval on
which sine increases. At unit 2, the bit-zero interval gives an
absolute angle for `u_2` in
`[7pi/4-theta_0, theta_1+pi/2]`, contained in `[pi,5pi/4]`,
where sine decreases. Therefore

\[
 (u_0)_y\le-\sin(\theta_0-\pi/4),\qquad
 (u_2)_y\le-\sin(\theta_0+\pi/4).
\tag{8}
\]

No formula for a nonshared unit has been applied to the shared unit 1.
For that actual unit, (4) instead gives

\[
 (\ell_1u_1)_y=-\ell_1\cos\theta_1\le1/\sqrt2.
\tag{9}
\]

The sign in (9) uses `-cos(theta_1)>=0`; shortening the actual
positive chord can only decrease this upward component.

## 3. Strict vertical contradiction

Take the vertical component of the left side of (2). Equations
(4), (7)--(9) give

\[
\begin{aligned}
 \sum_i(n_i+\ell_i u_i)_y
 &\le \sin\theta_1-\sin\theta_0
       -\sin(\theta_0-\pi/4)+1/\sqrt2
       -\sin(\theta_0+\pi/4)\\
 &=\sin\theta_1+1/\sqrt2-(1+\sqrt2)\sin\theta_0\\
 &<1+1/\sqrt2-(1+\sqrt2)/\sqrt2=0.
\end{aligned}
\tag{10}
\]

The last inequality is strict because `theta_1>pi/2`, hence
`sin(theta_1)<1`, while `sin(theta_0)>=1/sqrt2`. This contradicts
the exact closure (2).

Even if the unnecessary lower-turn boundary `theta_1=pi/2` is added
to the estimate, it introduces no unhandled equality case: equality
in the last numerical bound forces `theta_0=theta_2=3pi/4`, but
then (4) gives `(ell_1u_1)_y=0<1/sqrt2`. Thus all permitted
upper-turn endpoints and all genuine shared-mean endpoints are
already covered by the same projection argument.

## 4. Exact remaining scope

Every packing of this original contact type would satisfy (2), so
the contradiction holds independently of the positions of the three
extra squares. They have not been removed from the packing or replaced
by another force-bearing object. The proof also leaves all positive
force ratios unrestricted, because it uses only the full local
angular intervals and the actual shared chord.

After reducing a mixed one-share word to `110`, a sole share at
loaded unit 1 is therefore impossible. Sole shares at loaded unit 0
or at loaded unit 2 are separate original possibilities and are not
excluded here. The constant-bit one-share placement is also not
excluded. No conclusion about their three-extra exterior allocations,
the complete two-share family, the obtuse one-radial family, the
unrestricted sharp bound, equality classification, or the earlier
prerequisite-chain audit is asserted.

This is a single entire contact-type proof. It introduces no angular
cells, numerical proof premise, coefficient packet, Lean compilation,
or CI action.
