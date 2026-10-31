# Fresh independent review of the restored near-root coupled-return inequality

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## Decision and exact scope

**PASS: the entire scalar theorem and the conditional physical
corollary in the source below are valid as stated.** This is a fresh
complete review of the restored source, not a recovery of the lost
review formerly pinned at
9da65e51c67cd62d8db8fe9441bff9680739c896cab8f374c4431185de2e2704.
No claim of equality to those old review bytes is made.

| Source read in full | Exact SHA-256 reviewed |
| --- | --- |
| COUPLED_NEAR_ROOT_RETURN_REACH_UNIFORM_RADIUS_EXCLUSION.md | f4a7e45f09afe40d3f30c47fcae17d1235a7f36270c44f3041a1bcc9a0d6b5bc |

The reviewed theorem is self-contained. I checked every operative
premise, derivative, interval transition, sign and endpoint in all
five sections. There is no operative imported geometric theorem
inside the scalar proof. The physical corollary explicitly assumes
the original geometric data it needs.

The accepted scalar domain is exactly

    59/60<=a<=61/60, 0<=y<=31/120,
    0<=q<=4/15, 0<t<=a,

with the source's unchanged reach inequality (R). No positivity of
y-(a-t)q is required. The conclusion is the strict inequality

    (a+t/l)^2+(1-tq-y+(1-tq)/l)^2>1105/256,
    l=sqrt(t^2+(1-tq)^2).

This review gives no original graph-family closure. The true
geometric entry conditions and the t>a branch remain separate
obligations for a caller.

## 1. Rectangle relaxation and the second-coordinate derivative

I independently differentiated the relaxed function

    F(t,s)=(A+t/l)^2+(s-Y+s/l)^2,
    l=sqrt(t^2+s^2),

using A=59/60 and Y=31/120. Its derivative is exactly

    F_s/2=s-Y+s/l+[t^2*(s-Y)-Ats]/l^3.

The original s=1-tq lies in [S,1], where S=164/225, and
t<=61/60. Both terms being squared have positive arguments.
Consequently replacing a by A and y by Y gives a genuine lower
bound on the target expression.

The source's estimate s/l>1/2 follows from the strict reserve

    3S^2-(61/60)^2=151261/270000>0.

The bound ts/l^3<=1/(2s) follows from 2ts<=l^2 and l>=s.
The positive term t^2*(s-Y) can safely be dropped. Finally,
s-Y+1/2-A/(2s) is increasing in s>0, and its value at S is

    87383/295200>0.

This verifies strict s-monotonicity over the full rectangle, rather
than merely over one selected curve.

## 2. Complete high interval

For 3/8<=t<=61/60, the substitution s=1-(4/15)t is a lower
bound by the proved s-monotonicity. Along this line,

    (t/l)'=s/l^3, (s/l)'=-t/l^3.

These identities reproduce both printed formulas for G' and G''.

The necessary signs are valid uniformly. The quantity
B=t-(4/15)s is increasing and is 27/200 at the lower endpoint.
For N=s*(A-t)+tY, the bound s*(A-t)>=-1/30 holds whether
A-t is positive or negative, because s<=1 and t<=61/60.
It gives N>=61/960>0. Therefore the last term in G'' is
strictly negative and may be discarded in the displayed direction.

The length squared is increasing because its derivative is 2B.
The stated endpoint length bound 13/10 and the lower bound
343/1800 for A*k+1-Y-3kt give

    G''/2<-7723/494325<0.

Thus the minimum of G on its entire closed interval is at an
endpoint. At t=3/8 the exact length is 39/40 and the source's
reserve is

    G(3/8)-1105/256=2471/748800>0.

At t=61/60 the length is strictly below 251/200. The substituted
lower bounds 610/753 and 1312/2259 for t/l and s/l are valid,
and the positive endpoint reserve is

    4323176011/816492960000>0.

Both comparisons square positive expressions. This closes the whole
high interval without any use of reach.

## 3. Complete small interval and the reach implication

For 0<t<=3/8 the completed-square identity for l^2 is exact.
It gives u<=sqrt(241/225)t<(25/24)t; the strict last comparison
has squared reserve 67/4800.

Starting from (R), replacing the first circle term by 1/2 and
-y/(1+q^2) by -Y is valid even when y-(a-t)q has either sign.
Because t<A and q>=0, the final nonnegative factor may be bounded
using 1/(1+q^2)>=225/241. This reproduces

    u>=29/120+(225/241)*(A-t)q.

Together with the strict speed bound it forces t>29/125.
The ratio t/(A-t) is increasing, has endpoint value 45/73,
and multiplies a positive factor. Thus the linear estimate

    tq<=K*(t-t0), K=1205/1752, t0=29/125,

has the correct direction. The identity
C=1+Kt0=50789/43800 is exact.

The relaxed second coordinate C-Kt decreases from 1 to
315937/350400>9/10>S, so the earlier rectangle monotonicity
does apply on the entire segment. This is an essential domain
check before passing to H(t)=F(t,C-Kt).

I independently derived

    H'/2=C*N/l^3-K*(s-Y+s/l),
    N=A*s-t*(s-Y), s=C-Kt.

Here N>0 since A>t and s,Y are positive. Its derivative is
negative on the whole interval, with lower bound

    -N'>=279019/262800>0.

To prove H'<0, the source multiplies only by positive quantities.
Using l>=s and s-Y>0 gives the valid lower bound

    K*[(s-Y)s^3+s*t^2+s^3]-C*N

for the expression whose positivity implies H'<0.

The two intervals [29/125,3/10] and [3/10,3/8] cover the
whole domain with a harmless overlap at 3/10. The source's
bounds on s follow from its decreasing affine formula, and its
bounds on N follow from the established monotonicity of N.
The t bounds are lower bounds. In every positive product the
substitution reduces a nonnegative factor, while replacing -CN
uses genuine upper bounds C<29/25 and the stated upper bound
for N. Thus the directions in both rows are correct.

The resulting strictly positive reserves are respectively

    6850199/76800000,
    20269/640000.

I also checked every printed rational endpoint identity establishing
those row bounds, including both N bounds and s(3/8)>9/10.
This proves H'<0 uniformly. It follows that

    H(t)>=H(3/8)>F(3/8,9/10)>1105/256.

The middle comparison is strict by the already proved
s-monotonicity. It connects the small interval to the exact
endpoint already proved in Section 2 without a missing gap.

## 4. Endpoints and physical application

The two t intervals overlap at 3/8 and cover every allowed positive
t<=a<=61/60. The reach argument excludes t<=29/125 in the small
interval; it does not silently omit a feasible endpoint. The proof
also retains q=0, y=0, a=59/60, a=61/60 and t=a. All denominator
lower bounds are strict, and the final conclusion remains strict
at all admitted endpoints.

For the conditional physical use, write

    P_D=(-a,y+tq-1), n_D=(-u,-v).

The asserted point P_D+n_D belongs to the actual unit D whenever
n_D is its inward unit minimum-support normal at the actual point
P_D. At a side, translating the unchanged side mean by that inward
unit axis reaches the opposite side. At a vertex, writing n_D in
the two inward orthonormal square axes gives coefficients in [0,1].
This also includes a side endpoint and a non-owned vertex normal.

Its squared norm is exactly

    (a+u)^2+(s-y+v)^2,

so the scalar conclusion directly contradicts containment in any
disk with radius squared at most 1105/256.

The actual upper-side estimate

    tau>=1/2-(y-(a-t)q)/sqrt(1+q^2)

and actual TD reach imply (R): the former is an upper bound
for 1-tau, so the displayed expression in (R) is at least the
actual reach expression. The direction of this implication is
correct, including equality.

No force equation at D is used, no degree is reduced and no TD mean
is changed. In particular the corollary is valid with every original
D owner possibility and actual side endpoint. It does not manufacture
the upper-side hypothesis or the parameter bounds. Those must be
proved in the physical caller, as the source explicitly states.

## 5. Verification boundary

The full mathematical argument above was checked by hand. Exact
rational recomputation confirmed all printed constant identities
and endpoint reserves considered in the audit; that arithmetic is a
transcription check, not an exclusion certificate.

There was no Lean compilation, CI, numerical pose search or sampled
parameter proof. The PASS is solely for the exact source and its
stated full scalar/conditional scope.

