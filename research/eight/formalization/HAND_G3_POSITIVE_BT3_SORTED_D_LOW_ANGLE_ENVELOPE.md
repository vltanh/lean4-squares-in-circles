# The sorted-D block and the low-total positive-BT3 envelope

## 1. Definitions and the two conclusions

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad L=\frac16,\quad K=.6692,\quad C=1.1642,
\]
\[
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,\qquad
 r=c_0+\frac12,\quad d=c_0-\frac12.
\]
All decimal constants in this note are exact rationals. Use
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 \phi(t)=\cos t+\sin t\quad(0\le t\le h),
\]
\[
 S(f,g)=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\frac12)^2}-\frac12\right)+gb\right\}.
\tag{1}
\]
For \(c\in[1,C]\), define the exact two-angle D increment
\[
 \begin{split}
 D_c(x,y)={}&c\{W(x)-1\}+W(y)-1+(1+c)c_0\\
 &-S(c\sin x+\cos y,c\cos x+\sin y).
 \end{split}
\tag{2}
\]
In particular \(D_c(0,0)=0\): the sorted zero-angle support is
\(S(1,c)=(1+c)c_0\), including the weak tie \(c=1\).

For \(0<p\le q\), \(p/q\ge1/2\), write
\[
 \begin{split}
 N_{p,q}(s)&=\sqrt{p^2+q^2+2pq\sin s},\\
 U_{p,q}(t)&=p\{\phi(t)-1\}-R\{N_{p,q}(t)-N_{p,q}(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)-R\{N_{p,q}(-t)-N_{p,q}(0)\},\\
 M_{p,q}(z)&=p\{\phi(h-z)-1\}+q(\cos h-1)
                         -R\{N_{p,q}(-z)-N_{p,q}(0)\}.
 \end{split}
\tag{3}
\]

**Sorted-D conclusion.** If
\[
 P=(x)_++(y)_+\le h,\qquad
 N=(-x)_++(-y)_+\le h,
\]
then, on the entire signed domain,
\[
                    D_c(x,y)\ge-.65P+V_{K,1}(N).
\tag{4}
\]
This bound retains the exact sorted support at the origin. It
does not replace that support by the full-circle value.

**Low-total envelope conclusion.** Fix \(0\le\delta\le L\) and
\(0\le u\le\delta\), and choose
\[
 \begin{split}
 k&=.5866+.4956\delta,\qquad l=1,\\
 m&=1.1642-.8874\delta,\\
 c&=m\{\cos u+.293\sin u\}.
 \end{split}
\tag{5}
\]
For the ordinary H, G, B blocks the coefficient pairs are
\[
                  (k,1),\quad(k,1),\quad(1,m).
\tag{6}
\]
Suppose their signed angles, together with the two D angles,
have total \(-\delta\), with positive variation at most
\(h-\delta\) and negative variation at most h. Normalize the
ordinary blocks by their full-circle supports at zero and D
by its actual support \((1+c)c_0\). Then their combined
angular increment is at least
\[
                              V_{k,1}(\delta).
\tag{7}
\]
The concentration domain may have weak variation inequalities;
thus (7) applies in particular to the strict original G1
variation domain. The block lower bounds use the same original
angles and witness weights. Concentration is a minimization of
their lower bound, not a modification of the original centers.

The analytic argument below reduces (4) to the three exact
endpoint certificates in
[HAND_G3_POSITIVE_BT3_SORTED_D_ENDPOINT_CERTIFICATES.md](HAND_G3_POSITIVE_BT3_SORTED_D_ENDPOINT_CERTIFICATES.md).
That file proves its endpoints directly and does not use (4)
or (7). Sections 6--9 then prove (7).

## 2. The support regions and the diagonal comparison

Set
\[
 f=c\sin x+\cos y,\qquad g=c\cos x+\sin y,\qquad
 \tau=\frac1{2(a_0+1/2)}.
\]
Both f and g are strictly positive on the domain of (4).
Indeed the coarse whole-interval estimates
\[
 \sin h<.6443,\quad \cos h>.7648
\]
give
\[
 f\ge\cos h-C\sin h
    >.7648-1.1642(.6443)=\frac{735297}{50000000}>0,
 \qquad g>\cos h-\sin h>0.
\tag{8}
\]
The exact sorted-circle support has these three continuous
branches:
\[
 S(f,g)=
 \begin{cases}
 c_0(f+g),&g/f\ge1,\\
 R\sqrt{f^2+g^2}-(f+g)/2,&\tau\le g/f\le1,\\
 a_0f,&g/f\le\tau.
 \end{cases}
\tag{9}
\]
The expressions agree at each transition. The first branch is
the diagonal endpoint \(a=b=c_0\); the last is the tangent-zero
endpoint \((a,b)=(a_0,0)\). Formula (9) follows by maximizing
the linear force over the arc
\((a+1/2)^2+(b+1/2)^2=Q\), \(a\ge b\ge0\).

On the diagonal branch the contribution of a single positive
angle t of weight w is
\(-wd\{\phi(t)-1\}\); that of a negative angle \(-t\) is
\[
                     w\{r\sin t+d(1-\cos t)\}.
\tag{10}
\]
Here the two weights are c and 1. Consider the expression
obtained from (10) plus \(.65P-V_{K,1}(N)\), even before
restricting to the diagonal branch. Its derivative in each
positive-angle variable is at least
\[
                         .65-Cd>.65-.4C>.18.
\tag{11}
\]
Its derivative in a negative-angle variable is at least
\[
            r\cos t+d\sin t-V_{K,1}'(N)>1.327-1.101>0.
\tag{12}
\]
For the last estimate, \(V_{K,1}\) is concave on \([0,h]\), by
Section 3 of
[HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).
Also
\[
 V_{K,1}'(N)\le V_{K,1}'(0)=\frac{RK}{\sqrt{1+K^2}}<1.101,
\tag{13}
\]
where positive squaring leaves the reserve
\[
 1.101^2(1+K^2)-QK^2
                       =\frac{9634390329}{6250000000000}>0.
\]
The function \(r\cos t+d\sin t\) is concave. Its values at
0 and h are respectively greater than 1.3992 and
\[
 1.3992(.7648)+.3992(.6442)
                          =\frac{1659091}{1250000}>1.327.
\tag{14}
\]
Both (11) and (12) therefore hold throughout the domain.
Their common expression vanishes at zero, so
\[
                    D_c(x,y)+.65P-V_{K,1}(N)\ge0
\tag{15}
\]
at every point in the diagonal support region. In fact it is
strict there whenever at least one angle is nonzero. Integrating
the expression (10) does not require a path to stay on the
diagonal branch: (10), as an explicit function, satisfies the
derivative inequalities on the entire relevant orthant.

## 3. Full-circle concavity and the two endpoint values of c

Put
\[
 \psi(t)=\cos t+\max(0,\sin t)-1,\qquad
 N_c(s)=\sqrt{1+c^2+2c\sin s}.
\]
Replacing S in (2) by full-circle support gives
\[
 F_c(x,y)=c\psi(x)+\psi(y)+(1+c)r-RN_c(x+y).
\tag{16}
\]
Always \(D_c\ge F_c\), with equality on the interior branch
of (9), including its endpoints.

The two-angle concavity estimates of Section 3 of
[HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md),
applied with \(p=1,q=c\), imply
\[
              -RN_c''(s)<.945c\qquad(-h\le s\le h).
\tag{17}
\]
The coefficient ratio is admissible since \(1/c\ge1/C>1/2\).
In particular, for fixed \(0\le n\le h\),
\[
 \frac{d^2}{dt^2}
   \{F_c(t,-n)+.65t-V_{K,1}(n)\}
       =-c\phi(t)-RN_c''(t-n)<-.055c<0.
\tag{18}
\]
Here \(0\le t\le h\), \(\phi(t)\ge1\), and
\(t-n\in[-h,h]\).

The independent endpoint note proves
\[
                   D_c(h,-n)+.65h-V_{K,1}(n)>0
\tag{19}
\]
for all \(n\in[0,h]\) at both \(c=1\) and \(c=C\).
For fixed x,y, (2) is concave in c: its width and baseline
terms are affine in c, while S is a convex function of its
two force coefficients, themselves affine in c. Therefore
the left side of (19) is concave in c, and (19) holds for every
\(1\le c\le C\). This extends the endpoint conclusion for the
actual sorted support. It does not require a full-circle
endpoint bound where the tangent-zero branch is active.

One other boundary value will be used repeatedly:
\[
                         D_c(0,-n)\ge V_{K,1}(n).
\tag{20}
\]
This is exactly the one-angle sorted-D inequality (32) of the
same concentration note, with \(k=K\). Its hypotheses
\(1/2\le K\le17/20\) and \(K\le c\le2\) hold. At this
boundary the tangent-zero branch is inactive: f=cos n and
g=c-sin n give
\[
                g/f>.355>\tau,
\tag{21}
\]
because \(a_0+1/2>1.9\), so \(\tau<1/3.8<.264\).
Thus (20) is also an endpoint estimate for F whenever the
support there is interior.

## 4. The mixed-sign quadrants

First take \(x=-n\le0\), \(y=t\ge0\). Then
\[
 f-g=\cos t-\sin t-c(\cos n+\sin n)
                      =\phi'(t)-c\phi(n)\le0.
\tag{22}
\]
The support is diagonal, and (15) proves (4).

It remains to take \(x=t\ge0\), \(y=-n\le0\), with
\(t,n\in[0,h]\). In this quadrant
\[
 \frac{d}{dt}\frac gf
              =-\frac{c\{c+\sin(t-n)\}}{f^2}<0.
\tag{23}
\]
As t increases, the support can pass only from diagonal to
interior to tangent-zero, each at most once. The diagonal
part is already safe by (15). On the interior part the residual
\(D_c(t,-n)+.65t-V_{K,1}(n)\) is strictly concave by (18).
Its left endpoint is either a diagonal transition, where (15)
holds, or t=0, where (20)--(21) hold.

On the tangent-zero part, direct differentiation gives
\[
 \frac d{dt}\{D_c(t,-n)+.65t-V_{K,1}(n)\}
       =.65-c\{(a_0-1/2)\cos t+\tfrac12\sin t\}<0.
\tag{24}
\]
Indeed \(a_0-1/2>.914\), and the concave function in braces
is greater than .914 at both endpoints: at h use
\[
             .914(.7648)+\tfrac12(.6442)
                       =\frac{1276409}{1250000}>.914.
\]
Consequently a tangent-zero interval has its minimum at t=h.
Its left transition value is no smaller than that endpoint,
which is strictly positive by (19). If no tangent-zero interval
occurs, the right endpoint of the interior interval is t=h and
the same bound applies. Concavity then proves the residual is
nonnegative throughout the interior interval as well. This
proves (4) in both mixed-sign quadrants, including their axes.

## 5. The equal-sign quadrants and all weak ties

For two positive angles fix their total \(p=x+y\le h\) and
increase x from 0 to p, so \(y=p-x\). The force satisfies
\[
                         f'=g,\qquad g'=-f.
\tag{25}
\]
Thus g/f decreases strictly, and the support again runs in the
order diagonal, interior, tangent-zero. The norm in (16)
is constant along this path. Its remaining second derivative
is
\[
                            -c\phi(x)-\phi(y)<0.
\tag{26}
\]
On the tangent-zero branch the derivative of D, and hence of
the residual with fixed p, is
\[
 -c\{(a_0-1/2)\cos x+\tfrac12\sin x\}
   -\{(a_0-1/2)\sin y+\tfrac12\cos y\}<0.
\tag{27}
\]
The diagonal part is safe by (15); the right endpoint (p,0)
is safe by Section 4 with n=0. Equations (26)--(27), together
with continuity at both support transitions, therefore prove
(4) for this quadrant.

For two negative angles write \(x=-t\), \(y=-(n-t)\), with
fixed \(0\le n\le h\). Here
\[
                         f'=-g,\qquad g'=f,
\tag{28}
\]
so g/f increases strictly. There is no tangent-zero interval:
at t=0, (21) already places the ratio above that branch, and
it increases thereafter. On the interior interval the fixed
norm in (16) leaves second derivative
\[
                          -c\cos t-\cos(n-t)<0.
\tag{29}
\]
The left endpoint t=0 is safe by (20), and the other endpoint
is diagonal and safe by (15), unless it is t=n; that point is
also diagonal because its f-g equals \(1-c\phi(n)\le0\).
This proves (4) in the final quadrant.

All reductions used closed domains and the continuous branch
values in (9). The cases x=0, y=0, c=1, f=g and g=\(\tau f\)
are consequently included without a strict-owner assumption.
This completes the proof of (4).

## 6. The low-family range and concentration

For the family (5),
\[
             .5866\le k\le K,
       \qquad 1.0163\le m\le c\le C.
\tag{30}
\]
The first two ranges follow directly from \(0\le\delta\le1/6\).
The function \(\cos u+.293\sin u\) increases on this interval,
since
\[
 -\sin u+.293\cos u
 \ge-\frac16+.293\frac{71}{72}=\frac{8803}{72000}>0.
\]
Thus \(c\ge m\).
For the upper bound, use \(\cos u\le1\), \(\sin u\le u\le\delta\):
\[
 c\le(C-.8874\delta)(1+.293\delta)\le C,
\tag{31}
\]
because the coefficient of \(\delta\) is
\(C(.293)-.8874=-2731447/5000000<0\), and the quadratic
coefficient is negative. In particular every ordinary pair
in (6) has ratio at least 1/2, so all full-interval concavity
and concentration lemmas apply.

For \(1/2\le k\le K\), \(V_{k,1}(t)\) increases with k on
the whole interval \(0\le t\le h\). Differentiate its radical
formula. If \(k-\sin t\le0\), the sign is immediate. Otherwise
positive squaring reduces the comparison to
\[
               \sin t\{2k-(1+k^2)\sin t\}\ge0,
\]
which holds since \(2k/(1+k^2)\ge4/5>\sin h\).
Consequently (4) supplies the simpler enlarged D block
\[
                         -.65P_D+V_{k,1}(N_D).
\tag{32}
\]

The ordinary two-angle blocks normalize exactly as in Section 5
of the concentration note. For each unordered coefficient pair
\(p\le q\), an angle of either sign can first be placed in the
coordinate giving the smaller lower bound, leaving the block
\[
 p\{\phi(P_i)-1\}+q(\cos N_i-1)
             -R\{N_{p,q}(P_i-N_i)-N_{p,q}(0)\}.
\tag{33}
\]
Its positive and negative variables are separately concave on
\([0,h]\). The D block (32) has the same separate concavity.
The domain is
\[
 P_i,N_i\ge0,\qquad
 P:=\sum_iP_i\le h-\delta,\qquad
 \sum_iN_i=\delta+P.
\tag{34}
\]
Concentrating the negative simplex, then the positive simplex,
and finally the scalar \(P\in[0,h-\delta]\) gives exactly the
following kinds of endpoint values:

* a single negative value \(V_i(\delta)\);
* an ordinary same-block value \(M_i(\delta)\);
* a separated value \(U_i(h-\delta)+V_j(h)\), allowing the D
  positive alternative \(-.65(h-\delta)\) and its H-type
  negative alternative \(V_{k,1}(h)\).

The same-block D endpoint is included in the third kind. The
indices H and G have the identical pair \((k,1)\), and B has
\((1,m)\). Allowing equal indices in the separated minimum
can only enlarge its minimizing domain. The proof of this
concentration is the same elementary separate-concavity proof
as equations (41)--(46) of the cited concentration note; the
only changed D coefficient is the linear slope -.65.

## 7. Same-block endpoints

For B, \(1/m\ge1/C>2/3\). The universal same-block inequality
from Section 4 of
[HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
therefore gives
\[
                         M_{1,m}(\delta)\ge V_{1,m}(\delta).
\tag{35}
\]
For H and G, where k can be below 2/3, the required exact
correction is
\[
 E(\delta):=M_{k,1}(\delta)-V_{k,1}(\delta)
      =k\{\phi(h-\delta)-1\}+\cos h-\cos\delta.
\tag{36}
\]
Put \(b=h-\delta\), \(a=.4956\), and \(k=.5866+a\delta\).
Direct differentiation gives
\[
 \begin{split}
 E'&=a(\phi(b)-1)-k(\cos b-\sin b)+\sin\delta,\\
 E'''&=-\sin\delta-3a\phi(b)+k(\cos b-\sin b)<0.
 \end{split}
\tag{37}
\]
The last sign follows already from \(\phi(b)\ge1\),
\(\cos b-\sin b\le1\), and \(k\le K<3a\).
Thus \(E'\) is concave, so its minimum is at an endpoint.
Alternating Taylor bounds at h and \(h-L=8/15\) give
\[
 \begin{gathered}
 \phi(h)-1>.409,\quad \cos h-\sin h<.1207,\\
 \phi(8/15)-1>.369,\quad \cos(8/15)-\sin(8/15)<.353,\\
 \sin L>.1658.
 \end{gathered}
\tag{38}
\]
Consequently
\[
 \begin{split}
 E'(0)&>.4956(.409)-.5866(.1207)
                         =\frac{6594889}{50000000}>.11,\\
 E'(L)&>.4956(.369)-.6692(.353)+.1658
                         =\frac{140561}{1250000}>.11,\\
 E(0)&>.5866(.409)+.7648-1
                         =\frac{23597}{5000000}>0.
 \end{split}
\tag{39}
\]
Hence \(M_{k,1}(\delta)>V_{k,1}(\delta)\) on the entire
low interval. This uses the continuous low family, not a
finite list of values of \(\delta\).

## 8. Whole-interval secants for the negative endpoints

We claim that every ordinary pair in (6) satisfies
\[
                 V_i(h)>V_{k,1}(\delta)+.75(h-\delta).
\tag{40}
\]
For the H pair, put \(J(k)=V_{k,1}(h)\),
\(S=\sin h\), \(C_h=\cos h\). Then
\[
 J''(k)=R\left\{\frac1{(1+k^2)^{3/2}}
       -\frac{C_h^2}{(1+k^2-2kS)^{3/2}}\right\}<0
                    \quad(.5866\le k\le K).
\tag{41}
\]
For an explicit sign check, the quadratic
\(1+k^2-2k(.6442)\) is convex in k and is less than
\(.768^2\) at both endpoints. Its two positive square
reserves are \(37497/25000000\) and \(6551/1562500\).
Also
\[
                    .7648^2-.768^3=\frac{257684}{1953125}>0.
\]
Thus the second term in braces in (41) exceeds 1 while the
first is below 1.

At the right endpoint,
\[
 \sqrt{1+K^2}<1.204,\qquad
 \sqrt{1+K^2-2KS}>.764,\qquad 0<K-S<.025.
\]
Therefore
\[
 J'(K)>1.978\left\{\frac{.6692}{1.204}-\frac{.025}{.764}\right\}
                         =1+\frac{66229}{1910000}>1.
\tag{42}
\]
At \(k_0=.5866\), positive squaring and the alternating
sine polynomial through degree seven give
\[
 \sqrt{1+k_0^2}>1.159353,\qquad
 \sqrt{1+k_0^2-2k_0S}<.767010.
\]
Using \(R>1.9787\),
\[
 J(k_0)>.7648-1+1.9787(1.159353-.767010)
                         =.541+\frac{1290941}{10000000000}>.541.
\tag{43}
\]
By (41)--(43),
\[
                         J(k)>.541+.4956\delta.
\tag{44}
\]
Concavity of V and (13) imply
\(V_{k,1}(\delta)\le1.101\delta\). Subtracting, and using
\(.75h=.525\), gives
\[
 \begin{split}
 J(k)-V_{k,1}(\delta)-.75(h-\delta)
       &>.541-.6054\delta-.525+.75\delta\\
       &=.016+.1446\delta>0.
 \end{split}
\tag{45}
\]
This proves (40) for H and G.

For B, concavity gives
\[
 V_{1,m}'(t)\ge V_{1,m}'(h)
   =m\left\{-\sin h+
       \frac{R\cos h}{\sqrt{1+m^2-2m\sin h}}\right\}>1.
\tag{46}
\]
Indeed the denominator is less than .926 throughout
\(m\in[1.0163,C]\): convexity of its squared upper bound
reduces this to the endpoints, with positive square reserves
\(13401123/100000000\) and \(51741/25000000\). The final
rational derivative comparison is
\[
 1.0163\left\{-.645+\frac{1.978(.7648)}{.926}\right\}-1
                         =\frac{110678043}{23150000000}>0.
\tag{47}
\]
Finally, coordinatewise monotonicity of V on \([0,L]\), proved
in Section 5 of the scalar-envelope note, gives
\[
                         V_{1,m}(\delta)\ge V_{k,1}(\delta).
\tag{48}
\]
For example, increase the first coefficient from k to 1 with
the second fixed at 1, then increase the second from 1 to m;
both paths stay within its allowed coefficient ratios. Integrating
(46) from \(\delta\) to h and using (48) proves (40) for B.

## 9. Elimination of every saturation endpoint

The universal positive-envelope bound, Section 2 of the scalar
envelope note, is
\[
                         U_{p,q}(t)\ge-.545qt.
\tag{49}
\]
Here every ordinary q is at most C, and
\[
                    .65-.545C=\frac{15511}{1000000}>0.
\tag{50}
\]
Thus each ordinary positive alternative, as well as the D
linear alternative, is at least \(-.65(h-\delta)\). Combining
with (40), every separated or D same-block endpoint is strictly
greater than
\[
                   V_{k,1}(\delta)+.10(h-\delta).
\tag{51}
\]
The ordinary same-block endpoints are no smaller than their
pure-negative counterparts by (35)--(39). Their pure-negative
minimum is exactly \(V_{k,1}(\delta)\), by (48), with H and G
providing that scalar candidate. All endpoints of the enlarged
concentration domain are therefore at least (7). This proves
the low-total envelope conclusion.

For clarity, neither (4) nor (7) asserts that the original
configuration has concentrated angle errors. They bound its
actual two-angle D support and all of the original selected
projection witnesses on their complete signed domains. The
strict inequalities used to discard saturation endpoints leave
all weak original owner ties available.

## 10. The resulting low-total split is strictly concave

This additional observation records the analytic interface to
the two low-total scalar endpoint checks in
[HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
For fixed \(\delta\), use k,m from (5),
\(c(u)=m(\cos u+.293\sin u)\), and
\[
 \sigma=R\sqrt{1+.293^2}-\frac{1+.293}{2}<1.416.
\]
On \(0\le t\le L\), the exact sorted middle support charge is
\[
                j(t)=\frac{\cos t-1}{2}
                              +(\tfrac12-a_0)\sin t.
\tag{52}
\]
The actual D baseline contributes
\[
                  c-S(1,c)=(1-c_0)c-c_0,
\tag{53}
\]
whose second derivative in u is \(-(1-c_0)c<0\). All other
u-dependent terms, apart from \(j(\delta-u)\), are
\(mW(u)-m\sigma\sin u\). Since \(a_0-1/2<.915\),
\[
 \begin{split}
 j''(\delta-u)&\le-\tfrac12\cos(\delta-u)
                                      +.915\sin(\delta-u),\\
 (mW-m\sigma\sin)''(u)
                 &\le m\{-\tfrac12\cos u+.916\sin u\}.
 \end{split}
\tag{54}
\]
Use \(m\ge1.0163\), \(m\le C\),
\(\cos u,\cos(\delta-u)\ge71/72\), and
\(\sin u+\sin(\delta-u)\le\delta\le1/6\). The sum in (54)
is bounded above by
\[
                 -\frac12(1+1.0163)\frac{71}{72}
                                 +\frac{.916C}{6}<-.8.
\tag{55}
\]
Discarding the additional negative second derivative from
(53) preserves this strict bound. Thus the remaining low-total
scalar is strictly concave in \(u\in[0,\delta]\); its minimum
is at \(u=0\) or \(u=\delta\). At \(\delta=0\) these are the
same endpoint. This is an analytic endpoint reduction on the
full interval, independent of the subsequent positive scalar
certificates.
