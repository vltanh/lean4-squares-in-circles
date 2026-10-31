# Independent review of the complete adjacent-C side exclusion

Date: October 25, 2026.
Reviewer: root, independently of the author.

**Verdict: PASS for the entire saved beta>3/2 side theorem and its
join with the accepted beta<=3/2 side theorem.**
Every original C-owned or shared HC side after the strict B-owned
minimum-f BC singleton is excluded. The strict R0/j endpoint is the
only remaining adjacent-circle-C feature after the separately reviewed
whole R1 exclusion. No whole ABC gate is closed by this review alone.

## 1. Exact sources and original scope

I read the complete frozen source and checker:

    ABC_UNIQUE_SINGLETON_ADJACENT_SIDE_EXCLUSION.md
    SHA256 8af0f03527b540ca1cb3ec539ceb46b9ae1deadda5564434f9744db3b2737fac
    ABC_UNIQUE_SINGLETON_ADJACENT_SIDE_CHECK.py
    SHA256 013f02b9e28d330fbe7a87a6f3c91735c80ecc33671ff8647ac086db805dbb65

I also reread the complete original adjacent fan
ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md, including its full
circle-corner cover, proper C2 concurrence, actual HC side mean and
accepted beta<=3/2 side exclusion. The independently reviewed
ABC_UNIQUE_SINGLETON_SIDE_FRONT_RETURN_REDUCTION.md gives the same
whole-beta front-side reduction; the new source additionally proves
that reduction in full within its own Section 3.

The original H4/A2/B2/C2 cycle, intact HXY petal, all nine physical
squares, all three extras, actual positive forces, unique physical
circle masks and every shared mean are retained. The argument does
not add an H/B edge or apply a fixed-tip selection to a variable mean.
The radius interval includes both original endpoints.

## 2. The full high-beta circle comparison

From beta>3/2 and the upper radius bound, 0<W<23/16 follows exactly.
The actual adjacent C circle equality and Y=W(1-tau/beta) give

    Y*C0-X*S=X+W^2*z*(1-z/2), X=beta-1, z=tau/beta.

I independently expanded the squared-circle identity to check this
sign and all factors. Since C0<1 and X,S>0, its right side is
strictly smaller than Y.

At tau=1/2, multiplying K-Y by 8*beta^2 gives precisely the displayed
W-quadratic. I expanded its discriminant independently:

    16*beta^2*(-4*beta^2+6*beta-1).

The bracket is -1 at beta=3/2 and strictly decreasing thereafter.
The leading coefficient is positive. Hence K-Y is positive at
tau=1/2 for every W, while its tau derivative is positive on the
entire actual 0<tau<1, beta>3/2 interval. This proves tau<1/2
without restricting an actual orientation or circle-coordinate branch.

Under the contrary assumption C0<=tau+1/2, monotonicity on the positive
unit quadrant gives S>=sqrt(1-(tau+1/2)^2). Substitution in the exact
circle identity has the stated inequality direction and gives F<=0.

I differentiated F in beta independently. Its negative term is

    (W*tau/beta^2)*(W*(1-tau/beta)+tau+1/2).

On the whole enlarged comparison rectangle its factors are bounded
by 23/72 and 39/16, respectively. Thus the uniform derivative reserve
85/384 is positive. Lowering beta to 3/2 is valid throughout that
enlarged domain.

The concave semicircle lies above its endpoint chord
sqrt(3)*(1/2-tau), itself at least 3/4-(3/2)*tau.
I independently rebuilt J directly by substituting this chord into
the defining F at beta=3/2, rather than copying its collected
coefficient list. I then reconstructed all nine tensor Bernstein
coefficients and every coefficient of the complete inverse identity
using separate Fraction arithmetic. They agree with the frozen
source. Their minimum is exactly 1/48, so the one whole-rectangle
identity gives J>=1/48>0. The contradiction proves C0>tau+1/2 and
therefore delta_B+C0>3/2.

I read and ran the persistent checker as well. It passes every
coefficient, inverse, discriminant identity and rational reserve.
No sign sampled at a finite set of configurations is used.

## 3. Original front support and the full remaining side

The actual side normal is m=C0*f+S*g and its mean is
R=Q+theta*S*e+t. These are consequences of the true C2 concurrence;
they keep the entire physical shared-HC interval and its endpoints.

If m dot n<=0, then D<0 and -D/E>=C0/S, while m dot j>0.
Every permitted H support point therefore has the same top-j
coordinate, including the whole side at m dot n=0.
I independently expanded R-T and its j coordinate. The theta terms
cancel exactly, leaving the strict bound

    r-u<E*(1-1/S)<0.

The original negative-A pressure gives r>u on every beta, by the
independently reconstructed norm-square reserve 241/3200.
Thus all surviving side means satisfy m dot n>0 and lie on H's
front n side: R=P+t_H*j with r-1<=t_H<=r<1.
No mean is fixed at an endpoint in making this inference.

The exact f displacement and the circle comparison now imply

    -D*t_H=c-delta_B-C0-theta*S^2<c-3/2<0.

For D<=0 the actual m dot j is positive, so the support fixes
t_H=r>0 and the left side is nonnegative, a contradiction.
For D>0 the equation gives t_H*D>3/2-c. Cauchy's inequality applied
to the actual c,s and u,v gives

    c+D=c*(1-u)+s*v<=sqrt(2-2u)<sqrt(2)<3/2.

Consequently t_H>1, contradicting its whole original interval.
This includes m dot j positive, negative and zero, including every
shared-HC mean. There is no omitted D=0 or shared-normal equality.

## 4. Whole feature join and remaining obligation

The independently accepted original fan excludes this same entire
HC side for beta<=3/2, including equality. The present theorem
covers beta>3/2. Their union therefore excludes the whole side
feature throughout the original radius and parameter domain.

The complete fan has only that side, R1 and R0 after the adjacent
circle-corner choice. The separate full-beta front-return theorem
excludes R1. Accordingly only the original strict R0/j endpoint
remains. It still retains aC>w>1/2, the exact A/B/C circle and
concurrence identities, negative A pressure, actual H/B separation,
all containment constraints, true positive forces, intact petal and
all three extras. This review makes no assertion that that remaining
endpoint is impossible.

No gate, parent mask, coarse cell, unrestricted theorem or equality
classification is closed here. No new ID, force reselection,
physical-mask substitution, Lean compilation or CI was used.
