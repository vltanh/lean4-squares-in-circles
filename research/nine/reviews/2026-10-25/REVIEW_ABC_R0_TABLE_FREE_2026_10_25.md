# Independent review: the complete ABC R0 scalar is table-free

Date: October 25, 2026.

**Review result: PASS at the complete original scalar-replacement and
physical-assembly scope.** A separate reviewer read the saved sources,
reconstructed the algebra and global inequalities, and checked the
unchanged two-ratio pressure join. No missing angle, ratio interval,
Taylor sign or denominator condition was found.

This review accepts replacement of the current **270-coefficient
large-ratio packet by zero coefficient checks**. It does not close a
new geometric gate, strengthen the unrestricted nine-square theorem,
or complete the older prerequisite-chain audit. No Lean compilation or
CI was run.

## 1. Sources and exact scope reviewed

The saved manuscripts reviewed are:

1. `ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md`, including the entire angular
   comparison and both ranges of its negative-endpoint proof;
2. `ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md`, including the entire
   unbounded positive-endpoint inequality;
3. Section 2 of `ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md`, the existing
   table-free proof for every \(0\le x\le1\);
4. Sections 1--4 of `ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md`, for the
   exact scalar definition, original physical ratios, B2 torque
   correction, positive corrected denominator and retained pressure
   reserve.

The new large-ratio proof covers exactly

\[
 x\ge1,\qquad -1/\sqrt2\le d\le1/\sqrt2,
 \qquad e=\sqrt{1-d^2}.
\]

It does not assert that \(d\) varies along physical packings. All
comparisons are inequalities on a larger scalar domain containing
every unchanged physical ratio and angle. The point \(x=1\) belongs
to both scalar arguments; neither a tail nor an angular endpoint is
left to continuity from an unproved open interval.

## 2. Original scalar identities and positivity

The target remains

\[
 F(x,d)=Kp/\sqrt a-q/\sqrt b-x/2+(8+16d)/25>0,
 \qquad K=79/40,
\]

with precisely the original \(a,b,p,q\). Their positivity holds
throughout the full domain. In particular \(a=(x-d)^2+e^2>0\),
\(b\ge2x^2+1>0\), and the displayed expressions for \(p,q\)
have positive numerators at every endpoint.

I reconstructed both square identities independently. For the second,
write \(q=b+dx(1+d/e)/2\). Its square divided by \(b\) has
linear-in-\(x\) part

\[
 2e-2d+d+d^2/e=e+1/e-d,
\]

using \(d^2+e^2=1\). The remaining term is exactly
\(d^2x^2(1+d/e)^2/(4b)\). Thus the new upper comparison concerns
the original \(q/\sqrt b\), not a modified scalar.

## 3. The first-term Taylor bound is global for both angle signs

For \(L=x^2+1\), \(t=dx/L\) lies in the whole closed interval
\([-r/2,r/2]\), where \(r=1/\sqrt2\). Direct differentiation
gives

\[
 \phi'(t)=\frac{-1/2+3t/2}{(1-2t)^{3/2}},\quad
 \phi''(t)=\frac{3t/2}{(1-2t)^{5/2}},\quad
 \phi'''(t)=\frac{3/2+9t/2}{(1-2t)^{7/2}},
\]

and hence the asserted

\[
 \phi''''(t)=\frac{(15/2)(2+3t)}{(1-2t)^{9/2}}>0.
\]

The fourth Taylor remainder contains \(t^4\), so its nonnegative
sign is valid for negative as well as positive \(t\). This point
is essential; no asymptotic truncation is being used.

I also expanded the exact identity

\[
 d^3-(3d-r)/8=(d-r/2)^2(d+r)\ge0.
\]

It supplies the stated affine minorant \(P_*(x,d)\) on the full
closed angle interval. Its endpoints produce exactly the coefficients
\(-rx^3/(8L^{5/2})\) and \(+rx^3/(16L^{5/2})\) in the two
endpoint functions.

## 4. The second-term bound and angular concavity retain the whole domain

The identity

\[
 e+1/e-2=d^2\frac{1-e}{e(1+e)}
\]

and the decreasing factor on \([r,1]\) prove the complete
quadratic comparison with coefficient \(3\sqrt2-4\). The convex
function \(U(d)=(1+d/e)^2\) has

\[
 U''(d)=\frac{2(e^2+4d^2+3de)}{e^6}
       =\frac{2((e+3d/2)^2+7d^2/4)}{e^6}>0.
\]

Its endpoint chord is consequently an upper bound, including the
negative-(d) half:
\(U(d)\le2(1+\sqrt2d)\). That chord is nonnegative on the
entire interval, so replacing \(d^2\) by \(1/2\) preserves the
inequality direction. Replacing \(b\) by \(2x^2+1\) in the
positive denominator also preserves it. These steps give exactly
the stated quadratic \(B_*\).

At \(d=-r\), its square root is exactly \(\sqrt2x+1\). At
\(d=r\), it is exactly
\((2x^2+1+rx)/\sqrt{2x^2+1}\). No endpoint upper estimate has
been substituted for those exact values.

The curvature test is sound: \(C>x/5\), \(B_0\ge2x^2\), and
\(|B_1|<x\) imply

\[
 4CB_0-B_1^2>8x^3/5-x^2>0\qquad(x\ge1).
\]

Also \(B_*>0\), already forced by the bound on the strictly
positive \(q^2/b\). Therefore \(\sqrt{B_*}\) is convex and the
entire lower comparison \(G\) is concave in \(d\). A concave
function on an interval is at least the smaller endpoint value,
which is the required direction in

\[
                       F(x,d)\ge\min(M_-(x),M_+(x)).
\]

## 5. The whole negative endpoint passes

On \([1,3/2]\), the tangent lower bound for \(\sqrt{x^2+1}\),
the lower bound \(x/\sqrt{x^2+1}\ge r\), and the upper bound
\(x^3/(x^2+1)^{5/2}<1/4\) have the appropriate signs for the
three terms. The resulting affine bound has negative slope. Its
value at \(3/2\) is bounded strictly below by the displayed
positive reserve

\[
                       991/896000>1/1000.
\]

I checked that reserve independently with exact rational arithmetic.
The uses of \(\sqrt{13}>18/5\), \(\sqrt2<99/70\), and
\(r<99/140\) all have the correct lower-bound direction.

For \(x\ge3/2\), the two Taylor/tangent bounds and the negative
denominator term reconstruct exactly the quartic in the source after
multiplication by \(8x^3>0\). I independently translated it by
\(x=t+5/2\) and recovered all four displayed coefficients
\(A,B,C,D\). The radical enclosure gives their asserted strict
bounds. Thus

\[
 P'(x)>0\quad(t\ge0),\qquad
 P'(x)>2t^2+3/10>0\quad(-1\le t\le0).
\]

These two domains exhaust the tail. The exact value
\(P(3/2)=(22871-16101\sqrt2)/400>6971/28000>1/5\)
was independently reconstructed. No critical point or finite sampling
is needed. Therefore \(M_->0\) for every \(x\ge1\).

## 6. The whole positive endpoint passes

All five Taylor/tangent inequalities in the positive-endpoint source
hold globally for \(t\ge0\). In particular, the negative third
derivative of \((1+t)^{-1/2}\) makes its quadratic Taylor expression
an upper bound, which is the needed direction under a negative
multiplier. The tangent lower bound for \((1+t)^{-5/2}\) remains
valid even when its right side is negative at small \(x\).

Independently inserting these inequalities into \(M_+\) gives exactly
the six coefficients \(A,B,C,D,E,F\) of its displayed lower bound.
For example the positive inverse-square contribution is
\(5Kr/16+1/8=79r/128+1/8\); the negative inverse-fourth contribution
is \(11Kr/32+3/64=869r/1280+3/64\). Both combinations have the
stated signs.

All six rational relaxations were checked independently. They yield
the exact quintic

\[
 P(x)=90x^5-639x^4+950x^3+840x^2-375x-795.
\]

On \([1,3/2]\), direct differentiation gives the stated shifted
derivative and the lower bound \(1425>0\), with \(P(1)=71\).
On the full tail, I independently expanded the exact identity

\[
 P(x)=(x-15/4)^2Q(x)
      +(26025/128)(x-15/4)+44085/512.
\]

The cubic satisfies \(Q'(x)>0\) on the whole tail and
\(Q(3/2)=2463/8>300\). Multiplication by the square preserves its
lower bound even when \(x-15/4\) is negative. The remaining
quadratic has positive leading coefficient and negative discriminant,
since its linear coefficient is less than \(204\) and
\(204^2<4\cdot300\cdot80\). The strict constant bound also
handles \(x=15/4\). This proves the full unbounded tail, hence
\(M_+>0\) for all \(x\ge1\).

## 7. Small ratios and the unchanged physical pressure reserve

I checked the existing small-ratio proof as part of the join. Its
two square-root comparisons hold with positive radicands; its
angle comparison is concave; and both endpoint functions decrease
on \([0,1]\). The two elementary endpoint reserves
\(1119/4000\) and \(423/5000\) follow with the displayed rational
square-root bounds. Thus the joined proof covers every \(x\ge0\).

In the original physical R0 chart, the actual angle satisfies
\(-r<D<r\), and both positive force ratios
\(\mu/\gamma\), \(\eta/\nu\) are arbitrary. The replacement
therefore applies at precisely

\[
                  (x,d)=(\mu/\gamma,D),\qquad
                  (x,d)=(\eta/\nu,-D).
\]

It leaves the actual B2 torque identity and corrected pressure
identity unchanged. The corrected total denominator is positive,
so replacing \(R\ge K\) by \(K\) is still legitimate. The same
two-force Cauchy estimate gives

\[
 K-\sqrt{2434}/25>1/640,
\]

with the independently checked exact squared reserve
\((1263/640)^2-2434/625=569/10240000>0\). Hence the original strict
conclusion remains

\[
 c_H\cdot F_{\mathrm{block}}
             >\sqrt{\gamma^2+\nu^2}/640>0.
\]

No uniform positive lower bound for each scalar endpoint as
\(x\to\infty\) is required to retain that pressure reserve;
strict scalar positivity at the two actual finite positive ratios
is exactly the premise used in the original join.

## 8. Acceptance and retained limitations

The new manuscripts replace the accepted 270-sign packet completely.
The larger 1,559-sign proof and the 270-sign checker can remain as
historical alternatives, but neither is a dependency of this scalar
proof. The validation arithmetic checked only the displayed short
identities and rational comparisons; no generated sign table is a
mathematical premise.

This is not an assertion that every remaining certificate elsewhere
in the repository has been removed. Nor does it add a physical case,
delete a positive force, change a shared mean, or enlarge the original
ABC/C4 assembly beyond its previously declared scope. The true
A2/B2/C2 equations, arbitrary permitted H degree, actual corner
masks, all original nine bodies and every completion square remain.

The unrestricted nine-square bound, classification of all original
equality packings and older full prerequisite-chain audit retain
their separate open status. No Lean compilation, CI or workflow
dispatch was performed for this review.
