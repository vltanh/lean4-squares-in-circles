# Nonnegative E-primary total: signed combination and two fixed-stress exclusions

## 1. Local statement and exact scope

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10},
 \qquad a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,
\]
and write
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 S(f,g)=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\}.
\tag{1}
\]
The E state has nonpositive signed tangent, with magnitudes
\[
 0\le b_E\le a_E,\qquad
 (a_E+\tfrac12)^2+(b_E+\tfrac12)^2\le Q.
\tag{2}
\]
It may be outer or true core; no radial-boundary equality is
needed for the following comparison. Retain actual DE3 and EH1,
with signed errors
\[
 u=d_{DE},\qquad v=d_{EH},\qquad e=u+v\ge0,
 \qquad |u|,|v|\le h,\qquad e\le h.
\tag{3}
\]
The signs of u and v may differ. No order of the D, E and H
frames is assumed. In the usual normal signs their exact projections
are
\[
 \begin{aligned}
 P_{DE3}&=a_D+a_E\sin u+b_E\cos u,\\
 P_{EH1}&=a_H+a_E\sin v-b_E\cos v.
 \end{aligned}
\tag{4}
\]

Define, for \(0\le t\le h\),
\[
                   j(t)=W(t)-1-S(\sin t,1-\cos t).
\tag{5}
\]
Then the exact local charge inequality is
\[
\begin{split}
 &W(u)+W(v)-2-a_E(\sin u+\sin v)
                         -b_E(\cos u-\cos v)\\
 &\hspace{45mm}\ge j(e).
\end{split}
\tag{6}
\]
In particular, the two actual inequalities in (4) imply
\[
                         a_D+a_H\ge2+j(e).
\tag{7}
\]
With any common positive multiplier \(\lambda\), the same statement
holds with both sides of (6) multiplied by \(\lambda\).
The equality of the two multipliers is part of this assertion.

This is an algebraic charge comparison. It does not replace an
original owner or construct a new E frame. Sections 5--7 join it to
two already proved fixed stresses on explicit original-owner scopes.

## 2. The signed comparison is the existing half-angle lemma

Apply the local inequality (4) in
[the signed A-primary combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md)
with the substitutions
\[
             a_A=a_E,\qquad y_A=-b_E,\qquad (u,v)=(d_{DE},d_{EH}).
\tag{8}
\]
Its circle and sorting hypotheses are precisely (2). Its intermediate
force becomes
\[
 a_A(\sin u+\sin v)+y_A(\cos v-\cos u)
 =a_E(\sin u+\sin v)+b_E(\cos u-\cos v),
\]
which is the E force in the sum of (4). Thus that lemma proves (6)
on the whole signed domain (3), including opposite signs and zero
total. No further numerical inequality or angle subdivision is needed.

For clarity, its half-angle proof uses
\[
 C=\cos(e/2),\qquad S_0=\sin(e/2),\qquad
                         \Delta=\frac{|u-v|}{2}.
\]
The signed force in (6) is at most
\(2S_0(a_E\cos\Delta+b_E\sin\Delta)\).
For two nonnegative errors, the resulting lower charge decreases
on \(0\le\Delta\le e/2\). For opposite signs it increases on
\(e/2\le\Delta\le h\). Both branches therefore reduce to the
same intrinsic endpoint \(\Delta=e/2\), which gives (5).
These monotonicity statements use only the exact bounds
\(a_E\le a_0<1.415\), \(b_E\le c_0<.9\), and the Taylor
reserves printed in the cited proof.

If both u and v are nonzero, the comparison (6) is strict.
For \(e>0\), the corresponding half-angle lies strictly inside
one of the two monotonicity intervals. For \(e=0\) and
\(u=-v\ne0\), the exact E force vanishes and the charge is
\(\cos u+|\sin u|-1>0=j(0)\).

## 3. The two single-primary endpoints

The orientation of the E tangent matters when the two intrinsic
endpoints are kept separately. At \((u,v)=(t,0)\), the E force is
\[
                       a_E\sin t-b_E(1-\cos t).
\]
For \(t\ge0\) it is at most \(a_0\sin t\), attained at the
axis point \((a_0,0)\). Hence the DE3-only endpoint has the lower
charge
\[
       j_{DE}(t)=\frac{\cos t-1}{2}
                              +(\tfrac12-a_0)\sin t.
\tag{9}
\]
At \((u,v)=(0,t)\), the force is
\(a_E\sin t+b_E(1-\cos t)\), so its exact support charge is j(t).
Since the axis point is allowed in (1),
\[
                              j(t)\le j_{DE}(t).
\tag{10}
\]
Thus (6) uses the weaker of the two endpoint charges; it does not
equate their supports.

For an explicit expression, let
\[
                 t_0=2\arctan\frac1{2\sqrt{Q-1/4}}.
\tag{11}
\]
The exact sorted-circle support in (5) gives
\[
 j(t)=
 \begin{cases}
  \displaystyle\frac{\cos t-1}{2}
                       +(\frac12-a_0)\sin t,&0\le t\le t_0,\\[3pt]
  \displaystyle\sin t-2R\sin(t/2),&t_0\le t\le h.
 \end{cases}
\tag{12}
\]
Indeed the support direction has slope \(\tan(t/2)\). Its maximizing
point stays on the axis until that slope reaches
\(1/(2\sqrt{Q-1/4})\), then lies on the circle interior.
Since \(\tan(t/2)<1\) on the present interval, it does not reach
the diagonal endpoint. The two formulas agree at \(t_0\).

## 4. The residual variation domain

Suppose these are the two original E edges in a real-frame cycle
whose errors satisfy
\[
              \sum_i d_i=0,\qquad
              \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{13}
\]
Delete u and v from the algebraic angular expression. The remaining
errors have signed sum \(-e\). If their positive and negative
variations are P and N, then
\[
                    N=P+e,\qquad P<h-e,\qquad N<h.
\tag{14}
\]
The first equality is their signed sum. For the second inequality,
\(u_++v_+\ge e\); for the third, deleting their negative parts
can only reduce the original negative variation.

Under equal DE/EH multipliers, the D and H forces in (4) are already
unrotated. One may therefore remove the two E angular arguments from
that force collection and retain the lower E charge \(\lambda j(e)\).
Any subsequent concentration argument may insert those missing arguments
as virtual zeros and use the enlarged domain (14). Its remaining
circle forces and its scalar endpoint bounds must still be proved
for this D/H force collection. Nothing in (6) transfers a full-cycle
exclusion solely from the analogous A calculation.

This local statement covers either E radial kind and every signed
allocation with \(d_{DE}+d_{EH}\ge0\). Negative signed total and
unequal DE/EH multipliers are outside its scope.

## 5. A uniform linear lower bound for the E charge

The full shifted-circle support gives
\[
                      j(e)\ge\sin e-2R\sin(e/2).
\tag{15}
\]
On the entire interval \(0\le e\le h\),
\[
                            j(e)\ge-\frac{1021}{1000}e,
\tag{16}
\]
strictly for \(e>0\). Here is one exact Taylor verification.
The square reserve
\[
                (1979/1000)^2-Q=\frac{841}{10^6}>0
\]
allows \(\overline R=1979/1000\). For \(e>0\), the cubic
lower sine polynomial at e and quintic upper sine polynomial
at \(e/2\) give
\[
\begin{split}
 \frac{j(e)}e
 &>1-\overline R
       +\left(\frac{\overline R}{24}-\frac16\right)e^2
       -\frac{\overline R}{1920}e^4\\
 &\ge1-\overline R
       +\left(\frac{\overline R}{24}-\frac16\right)h^2
       -\frac{\overline R}{1920}h^4\\
 &=-\frac{1021}{1000}+\frac{3138807}{6400000000}.
\end{split}
\tag{17}
\]
Both nonconstant coefficients are negative, so the second step
holds on the whole interval. At zero, (16) is an equality.

For the cycle statements below, an **E-primary total e** means one
of these three explicit cases:

* DE3 has error \(e\ge0\), while EH0 has any error;
* EH1 has error \(e\ge0\), while DE2 has any error;
* DE3 and EH1 are both retained, with arbitrary individual signs
  and sum \(e\ge0\).

For one primary, set only its angular argument to zero in the
secondary-owner expression. The remaining E secondary error is
unchanged. Its extra charge is at least j(e): for EH1 this is
the exact support (5), and for DE3 use (9)--(10). For two primaries,
set both arguments to zero and use (6). In every case the change
in the signed angular sum is \(-e\), and positive and negative
variation can only decrease when the designated arguments are
deleted. These are virtual angular changes inside the stress, not
new actual witnesses.

## 6. Fixed-stress exclusion with nonpositive A/T alternatives

Retain an original G0--G2 boundary cycle at Q, with sorted outer
H, G, B and D having signed tangents respectively positive,
negative, negative and negative. E is nonpositive; A and T may
have either sign and either radial kind. Retain BT2 and either
HG0 or HG2. Allow

* GA2 with any error, or GA3 with nonpositive error;
* AB0 with any error, or AB2 with nonpositive error;
* TD0 with any error, or TD2 with nonpositive error;
* any E-primary case listed in Section 5.

**There is no such original cycle.** Multiple allowed primary
alternatives may occur simultaneously, and no frame order is assumed.

Use the fixed weights and angular charge
\[
 k=\frac{31}{40},\qquad l=\frac{31}{20},\qquad
 c=2,\qquad L=\frac{21}{20}.
\tag{18}
\]
Section 2 of
[the negative-intermediate fixed-stress theorem](HAND_G3_NEGATIVE_INTERMEDIATE_ERRORS_FIXED_STRESS_EXCLUSION.md)
records the charged version of the secondary-owner estimate:
\[
       \mathcal C(\mathbf d)+L\sum_i d_i>\frac7{10000}
\tag{19}
\]
whenever positive and negative variation are each at most h.
Its individual circle bounds do not require a zero signed sum.

Let S be the sum of the magnitudes of the selected nonpositive
GA3/AB2 errors, with absent alternatives contributing zero. If
TD2 is selected, write its error as \(-w\), \(w\ge0\); otherwise
put \(w=0\) and retain the actual TD0 argument. Algebraically
delete these selected arguments and the E-primary argument or
arguments in Section 5. The resulting vector has
\[
                  \sum_i d_i^{\mathrm{virt}}=S+w-e.
\tag{20}
\]
All its positive and negative variations are still at most h.
Thus its reference stress exceeds
\(7/10000-L(S+w-e)\).

The same negative-intermediate theorem supplies the pointwise
gains, with its separate positive secant weights on the negative
A-primary inequalities,
\[
 \operatorname{gain}_A\ge\frac{1121983}{10^6}S,
 \qquad
 \operatorname{gain}_T\ge\frac{409}{350}w
                 =\left(L+\frac{83}{700}\right)w.
\tag{21}
\]
For the second bound, its exact gain is at least
\(2(\sin w+\cos w-1)\); the concave chord and
\(\sin h+\cos h-1>.409\) give (21), including \(w=0\).
The E multipliers remain equal to one, so its independent gain
is at least j(e). All three changes are differences from the
corresponding virtual inequalities at the same original states;
their gains therefore add without altering one another's scope.

Combining (16), (19)--(21), the actual positive stress is greater than
\[
 \begin{split}
 \frac7{10000}-L(S+w-e)
       +\frac{1121983}{10^6}S+\frac{409}{350}w+j(e)
 \ge\frac7{10000}
       +\frac{71983}{10^6}S+\frac{83}{700}w+\frac{29}{1000}e>0.
 \end{split}
\tag{22}
\]
Actual feasibility makes that same stress nonpositive, a contradiction.
All four circle supports still concern the unchanged original H, G,
B and D states. No marker or nonneighbor condition is asserted for
the virtual arguments.

## 7. Fixed-stress exclusion with a small nonnegative A total

Retain the same original four outer states, BT2, either HG owner,
and any E-primary case from Section 5. At A allow any of

* GA2 and AB0, with arbitrary errors, putting \(a=0\);
* one of GA3 or AB2 with error \(a\ge0\), and the other A edge
  with its secondary owner and arbitrary error;
* both GA3 and AB2, with arbitrary individual signs whose sum is
  \(a\ge0\).

Assume
\[
                              0\le a\le\frac16.
\tag{23}
\]
At TD allow TD0 with any error, or TD2 with nonpositive error.
**This original-owner class is also impossible.**

Use the second fixed family
\[
 k=\frac{39}{50},\qquad l=\frac{63}{50},\qquad
 c=\frac95,\qquad \lambda=\frac{103}{100}.
\tag{24}
\]
Section 3 of
[the positive-intermediate TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md)
proves that each charged circle increment is nonnegative on its
whole angular domain. Its zero-angle baseline is greater than
\(13/400\). Consequently its virtual four-circle expression obeys
\[
             \mathcal C(\mathbf d^{\mathrm{virt}})
               +\lambda\sum_i d_i^{\mathrm{virt}}>\frac{13}{400}
\tag{25}
\]
without requiring that the signed sum vanish.

The one-primary support comparison, or the signed A-combination
theorem when both A primaries occur, contributes at least lj(a).
Section 5 contributes j(e). If TD2 has error \(-w\le0\),
the secant comparison in Section 2 of
[the nonpositive-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md)
adds at least \((9/10)cw\). Otherwise put \(w=0\) and keep
the actual TD0 argument. After these deletions,
\[
                   \sum_i d_i^{\mathrm{virt}}=w-a-e.
\tag{26}
\]
Deleting any collection of the designated arguments preserves the
required individual upper bounds on both total variations. This
also applies when either combined pair has opposite signs.

The actual stress is therefore greater than
\[
 \frac{13}{400}+\lambda a+lj(a)
           +\lambda e+j(e)+\left(\frac9{10}c-\lambda\right)w.
\tag{27}
\]
On (23), the already proved low-A estimate in the cited TD0
theorem gives
\[
                  \frac{13}{400}+\lambda a+lj(a)>
                                   \frac{49}{15000}.
\tag{28}
\]
Equations (16), (24), and (28) make (27) strictly greater than
\[
                    \frac{49}{15000}+\frac9{1000}e
                                             +\frac{59}{100}w>0.
\tag{29}
\]
This is the required contradiction for the entire class in Section 7.

Sections 6--7 do not cover a positive original TD2 error, an
A-primary total exceeding \(1/6\), or a negative E-primary total.
The local inequality (6) remains available independently of these
two fixed-stress corollaries.
