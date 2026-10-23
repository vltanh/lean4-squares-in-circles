# The negative outer-to-outer bridge in the all-high cycle

## 1. Statement and the actual cycle cap

Use the original G0--G2 radial-boundary cycle, at
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad c_0=\sqrt{Q/2}-1/2,
 \quad \kappa=\frac{103}{100},\quad \rho=\frac{11}{10}.
\]
All terminating decimals in this note are exact rationals. An outer
state has
\[
 a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2,
                 \qquad 0\le b\le c_0.
\]
Retain the original L, M or H marker, with cuts at a=4b and a=7b/3:
\[
 \begin{split}
 F_L&=.403875(a-a_0)+1.089065b,\\
 F_M&=-2.143075+1.489593a+1.580219b,\\
 F_H&=\pi/4-.569472(a-c_0)+.390886(b-c_0).
 \end{split}                                                   \tag{1}
\]
Write b1 and b2 for the two transverse cuts, and extend the H
formula to the whole outer arc as \(F_H^*\). The potential is exactly
the one used in
`HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md` and
`HAND_G3_THREE_ZERO_AUGMENTED_PRIMARY_CHARGE.md`:
\[
             \Pi(a,b)=\kappa a+\rho(F_H^*(a,b)-F(a,b)).           \tag{2}
\]
In particular the original marker is used once at each shared vertex;
neither a marker nor a radial state is substituted in this proof.

Consider a quarter edge with two negative outer states, source
\((a,-b)\) and target \((A,-B)\). Its actual high-owner alternatives are
\[
 \begin{split}
 P_2&=a\cos d+b\sin d+B\ge W(d),\\
 P_3&=a+A\sin d+B\cos d\ge W(d),\qquad
 W(d)=\frac{1+\cos d+|\sin d|}{2},\quad |d|\le.7.
 \end{split}                                                   \tag{3}
\]
Then, in the actual cycle,
\[
 \boxed{\quad \frac\pi2+d+\Pi(a,b)-\Pi(A,B)>.957.\quad}         \tag{4}
\]

Here is the only information from the rest of the cycle that is used.
Put
\[
 h(z)=\frac{\sin z+\cos z-1}{2},\quad \beta=\frac9{50},\quad
 C_* =\frac{710}{113}-6\frac{8833}{10000}.
\]
For a selected outer chart j, set
\(
 \tau_L=0,\ \tau_M=.0093,\ \tau_H=.0265.
\)
The original marker charge
\[
                  O=\frac\pi2+d-F(a,b)+F(A,B)
\]
obeys
\[
 O+\beta h(|d|)<C_* -\mathcal B_{st},\qquad
 \mathcal B_{st}=\max\bigl\{|\tau_s-\tau_t|,
                  .0186\,\mathbf1_{s=t=M}\bigr\}.              \tag{5}
\]
This is a direct consequence of the established global G1 theorem.
For completeness, subtract .8833 from its C/L/M/H pair constants
\[
 \begin{pmatrix}
 .92&.91&.9005&.8833\\
 .91&.91&.9005&.8833\\
 .9005&.9005&.8912&.8926\\
 .8833&.8833&.8926&.9099
 \end{pmatrix}.                                                \tag{6}
\]
Also set \(\tau_C=0\). Each residual is at least
\(|\tau_i+\tau_j-.0265|\). Alternating the six quantities along
the complementary six-edge path gives a residual sum at least
\(|\tau_s-\tau_t|\). If both ends are M, a path that leaves M
has two transitions of residual at least .0093; the constant M
path has residual \(6(.0079)>.0186\). This proves the extra M/M
term. On the common real frame interval, concavity and monotonicity
of h imply that the width cost of the complementary path is at
least h(|d|). Summing its six actual G1 inequalities, using their
unchanged shared markers and \(2\pi<710/113\), gives (5).

Thus (4) is a statement about an original edge with its actual
global cap. No geometric deformation, physical-gap restriction or
unproved cap for a substituted state is used. The proof below uses
only the three intrinsic marker arcs, fixed positive multipliers,
and whole-interval scalar inequalities.

## 2. Elementary bounds and the two error signs

The circle equations, the cut equations, and the hand bounds
\(3.14159<\pi<355/113\) give
\[
 \begin{array}{c}
 .8992140<c_0<.8992141,\qquad
 1.4145756<a_0<1.4145757,\qquad R<1.978788,\\
 .3246868<b_1<.3246869,\qquad
 .5139668<b_2<.5139669.                            \tag{7}
 \end{array}
\]
For example, substitute the endpoints in
\((4b+1/2)^2+(b+1/2)^2=Q\) and
\((7b/3+1/2)^2+(b+1/2)^2=Q\). Every root in (7) is
enclosed by one strict rational square comparison.

All three original F functions increase on their own arcs. Their
endpoint bounds include
\[
 F_L(b_1)<.307,\quad F_M(b_2)<.456,\quad
 F_M(b_1)>.304,\quad F_H(b_2)>.463,
                   \quad 0\le F\le\pi/4.                     \tag{8}
\]
On L, the potential derivative has the especially simple form
\[
 \Pi_L'(b)=.0406817\frac{b+1/2}{a+1/2}-.7679969,
                         \qquad -.768<\Pi_L'(b)<0.             \tag{9}
\]

If d>=0, (5) forces source H and target L. Indeed a non-H source
would give \(O+\beta h\ge\pi/2-.456>C_*\), while a non-L target
would give \(O+\beta h>\pi/4+.304>C_*\).

For either projection in (3), with d>=0,
\[
             a+B-1\ge-.915\sin d-\tfrac12(1-\cos d).           \tag{10}
\]
For P3, use \(A-1/2<.915\); for P2 the stronger lower
bound \(-.4\sin d\) follows immediately. Let
\(B_0=\max(0,1-a)\). It lies in L. If B<B0, (9)--(10) show
\[
 \begin{split}
 \frac\pi2+d+\kappa a-\Pi_L(B)
 &\ge\frac\pi2+\kappa a-\Pi_L(B_0)
                 +\{1-.768(1.09)\}d,\\
                  1-.768(1.09)&>0.                           \tag{11}
 \end{split}
\]
Here \(1-\cos d\le d^2/2\le.35d\). If B>=B0, the
same comparison holds with gain d. Section 4 proves the aligned
quantity in (11) is greater than .9609. This proves (4) for d>=0,
including both actual owners.

For d=-z<0 and a negative outer target, original owner 3 implies
original owner 2. Indeed, with \(q=\tan(z/2)<.366\),
\[
 P_3-P_2=\sin z\{qa+b-A-qB\}\le0.                            \tag{12}
\]
Sorted source containment gives \(qa+b\le c_0(1+q)\).
Concavity on the target outer arc reduces
\(A+qB\ge c_0(1+q)\) to its two endpoints; the B=0 endpoint
uses \(a_0>1.414>.9(1+.366)\). This is also the actual-owner
comparison proved in Section 5 of the high-quarter charge note.
It remains to treat the actual P2 constraint with z in [0,.7].

## 3. A fixed dual expression for negative error

For \(\mu\ge0\), put \(K_\mu=\Pi-\mu F\). Giving the
actual constraints (3) and (5) multipliers \(\lambda>0\) and
\(\mu\), respectively, gives the following lower bound for the
charge in (4):
\[
 \begin{split}
 U={}&(1+\mu)(\pi/2-z)-\mu(C_*-\mathcal B_{st})
          +\lambda W(z)+\mu\beta h(z)\\
 &+\{K_\mu(a,b)-\lambda a\cos z+\lambda b\sin z\}
          +\{-K_\mu(A,B)-\lambda B\}.                         \tag{13}
 \end{split}
\]
Each added multiple is nonpositive on the original feasible edge.
The two braces can therefore be bounded on their independent
whole outer arcs.

The source-H bounds below use \(\mu=0\), except when (5) is
used to exclude a long error. Source L/M uses the two fixed choices
\[
 \begin{array}{c|cc}
 \text{target chart}&\mu&\lambda\\\hline
 L&17/10&59/25\\
 M\text{ or }H&5&93/20.
 \end{array}                                                   \tag{14}
\]
These are choices by the original marker chart, not a partition
of an angle or of a state arc.

## 4. Source H and target L, with every negative error

Use \(\mu=0\), \(\lambda=.755\). On L the target brace in
(13) is concave as a function of B, so its minimum is at B=0 or
B=b1. Direct substitution of (7) gives
\[
                         -\Pi_L(A,B)-.755B>-1.6120.             \tag{15}
\]
The source brace is
\((\kappa-\lambda\cos z)a+\lambda b\sin z\). Its a
coefficient is positive, so it too is concave in b. Its minimum
on H is at b=b2 or b=c0.

For one of these fixed source endpoints, the angular expression is
\[
 D_b(z)=\pi/2-z+\kappa a-1.6120
       +\lambda\{1/2+(1/2-a)\cos z+(1/2+b)\sin z\}.           \tag{16}
\]
At b=b2, its derivative is negative throughout [0,.7], because
\[
 \lambda\sqrt{(a-1/2)^2+(b+1/2)^2}<1.
\]
At b=c0, its derivative is positive: the concave function
\((c_0-1/2)\sin z+(c_0+1/2)\cos z\) has both endpoint
values greater than 1/lambda. The lower sine and cosine polynomials
of degrees 7 and 6 at .7 verify the second endpoint strictly.
Consequently only two values are needed:
\[
                         D_{c_0}(0)>.9609,
                         \qquad D_{b_2}(.7)>.9609.              \tag{17}
\]
The substitutions use (7), an upper degree-8 cosine polynomial
where its coefficient is negative, and the lower degree-7 sine
polynomial. This proves (4) in this entire chart case.

At z=0 the same dual applies to every source-H/target-L state
satisfying a+B>=1. Thus (17) proves the aligned lower bound used
in (11), without any assumption on the original positive-error
projection after that scalar comparison.

## 5. Source H and target M/H when z<=1/2

Use \(\mu=0\), \(\lambda=.69\). Concavity on M, and full
circle support on H, give the common target bound
\[
                          -\Pi(A,B)-.69B>-1.5992.               \tag{18}
\]
For H, the full circle expression is
\((\kappa+\lambda)/2-\sqrt{Q(\kappa^2+\lambda^2)}\);
the square bound \(\sqrt{Q(\kappa^2+\lambda^2)}<2.4533\)
already suffices. The M minimum is at one of its two endpoints.

The source again reduces to its two H endpoints. With -1.5992
in place of -1.6120 in (16), the b2 expression decreases, and
\[
                              D_{b_2}(1/2)>.9638.               \tag{19}
\]
For the diagonal endpoint, Taylor bounds on [0,1/2] give
\[
 \begin{split}
 D_{c_0}(z)&\ge D_{c_0}(0)-.03455z+.0543z^2,\\
 D_{c_0}(0)-\frac{.03455^2}{4(.0543)}&>.9618.                  \tag{20}
 \end{split}
\]
To see the quadratic coefficient directly, use
\(\sin z\ge z-z^3/6\),
\(1-\cos z\ge z^2/2-z^4/24\), and obtain
\[
 .69\left\{\frac{47}{96}(c_0-1/2)-\frac{c_0+1/2}{12}\right\}
                            >.0543.
\]
Thus (4) holds on this whole short interval. The next section
excludes its complementary long interval by the original cap.

## 6. The cap excludes long H-source errors into M or H

Write \(p=.569472\), \(q=.390886\), and suppose
\(1/2\le z\le.7\). For a source b, actual P2 requires
\[
 B\ge B_z(b):=\tfrac12-(a(b)-1/2)\cos z+(b+1/2)\sin z.        \tag{21}
\]
Put \(X=a+1/2\), \(t=b+1/2\), and r=t/X. On H,
\(r>.5967\), and
\[
          \partial_b B_z=r\cos z+\sin z>1.                     \tag{22}
\]
For (22), the function of z is concave, and the lower Taylor
bounds at 1/2 and .7 are both greater than 1. It also increases
with r.

There is a unique \(z_*\) for which \(B_{z_*}(b_2)=b_2\), and
\[
                              .6<z_*<.62.                     \tag{23}
\]
The derivative of \(B_z(b_2)\) in z is positive. Substituting
the bounds (7) and the sine/cosine Taylor bounds at .6 and .62
proves (23). Whenever \(B_z(b)=b_2\) and z>=1/2, also b<.65:
\[
 B_{1/2}(.65)>b_2,
 \qquad a(.65)+1/2<1.611.                                    \tag{24}
\]
Monotonicity in b and z proves the claim. All endpoint curves
below are therefore on their stated original outer arcs.

### 6.1 The H target

For a fixed source, F_H of the target increases with B, so the
smallest possible augmented old charge uses
\(B=\max(b_2,B_z(b))\). On the active part B=B_z(b), its
source derivative is
\[
       (p r_B+q)(r\cos z+\sin z)-p r-q,
             \qquad r_B=\frac{B+1/2}{A+1/2}.                   \tag{25}
\]
It is strictly positive. Indeed replace rB by .5967; the resulting
expression is affine in r in [.5967,1] and concave in z in
[1/2,.7]. Its four corner values are positive by the lower sine
and cosine Taylor polynomials. On the floor part B=b2, the old
charge decreases with source b. Therefore its minimum, at every z,
is on one of just two intrinsic contact boundaries:
\[
                 b=b_2\quad\hbox{or}\quad B=b_2.               \tag{26}
\]

The augmented old charge decreases along both boundaries as z
increases. On the first, z>=z*>.6, and
\[
 B<.619,\quad F_H'(B)<.782,\quad
 \partial_zB_z(b_2)<1.232,\quad \beta h'(z)<.024.
\]
Its derivative is thus less than
\(-1+.782(1.232)+.024<0\).

On the second boundary, define
\[
 C=1+\cos z-(b_2+1/2),\quad S=\sqrt{Q-C^2}.
\]
The source satisfies
\(X\cos z-t\sin z=C\),
\(X\sin z+t\cos z=S\). Implicit differentiation of (21) gives
\[
 -F_H'(b)\frac{db}{dz}
              =(pt+qX)\left(1-\frac{\sin z}{S}\right).        \tag{27}
\]
By (24), b<=.65. The function pt+qX increases on this subarc,
so \(pt+qX<1.285\). Also
\[
 C>.75,\quad S<1.832,\quad \sin z>.479,\quad
                    \beta h'(z)<.036.
\]
Thus the old-charge derivative is less than
\[
              -1+1.285(1-.479/1.832)+.036<0.                  \tag{28}
\]
The two boundaries join continuously at z*. Their minimum on the
whole long interval is consequently at z=.7, b=b2.

At that endpoint, (21) and the circle equation give
\(B>.61838\), \(A<1.13244\). The H-marker constants cancel,
and direct rational substitution gives
\[
 \begin{split}
 O+\beta h
 &=\pi/2-.7+p(a(b_2)-A)+q(B-b_2)+\beta h(.7)\\
 &>.9864>C_* .                                                \tag{29}
 \end{split}
\]
This contradicts (5), excluding the H target throughout the long
interval.

### 6.2 The M target

Now B<=b2. Equations (21)--(23) imply z<=z*, and every feasible
source lies between b2 and the unique point with B_z(b)=b2. In
particular b<.65. Also \(B_z(b_2)>.372>b_1\), so no lower
target-floor segment occurs. The smallest old charge uses B=B_z(b).

It is concave in the source parameter b. In fact, with
\(U=A+1/2\), its second derivative is
\[
 \frac Q{X^3}\{F_M'(B)\cos z-p\}
       -\frac{1.489593Q}{U^3}(\partial_bB_z)^2.
\]
Here X>1.6, U<1.8, \(F_M'(B)\le1.580219\), and (22) applies.
The upper bound is strictly negative because
\[
       \frac{1.489593}{1.8^3}
          -\frac{1.580219-.569472}{1.6^3}>0.                   \tag{30}
\]
Thus only the two contact boundaries (26) are needed again.

On B=b2 the derivative is the one already bounded in (28); only
the constant target marker changes. On b=b2 the old charge is
concave in z: \(\partial_zB_z>.8\),
\(\partial_{zz}B_z=1/2-B_z<.13\), and
\[
 \frac{1.489593Q}{1.8^3}(.8)^2-1.580219(.13)>0                 \tag{31}
\]
make its second derivative strictly negative. The width term has negative second
derivative as well.

The remaining endpoint values are z=1/2 and z=z*. At the first,
use B>.372, \(a(.372)>1.275\), and the upper bound for F_H(b2)
from (7). At the second, use (23),
\(F_H(b_2)-F_M(b_2)<.009\), and \(h(z_*)>h(1/2)\).
These give respectively
\[
 \begin{split}
 O+\beta h\big|_{z=1/2,b=b_2}&>C_*-.0172,\\
 O+\beta h\big|_{z=z_*,b=b_2}
 &>\pi_L/2-.62-.009+\beta h(1/2)>C_*-.0172,                  \tag{32}
 \end{split}
\]
where \(\pi_L=3.14159\). The latter comparison alone has a
reserve greater than .007. Since the H/M bonus in (5) is .0172,
both possibilities contradict the original cap. This completes
the long-error exclusion for source H.

## 7. Source L/M: exact support bounds for two fixed duals

The remaining combinations of source L/M and target L/M/H are
handled by the four scalar bounds associated with (14). This section records the support
bounds; Section 8 proves their continuous angle scalars.

Use shifted coordinates x=a+1/2, t=b+1/2. Write
\[
 \begin{gathered}
 h_a=-.569472,\quad h_b=.390886,\quad
 h_0=\pi/4+.178586(c_0+1/2),\\
 (f_{aL},f_{bL},f_{0L})
   =(.403875,1.089065,-.403875(a_0+1/2)-1.089065/2),\\
 (f_{aM},f_{bM},f_{0M})
   =(1.489593,1.580219,-2.143075-(1.489593+1.580219)/2).
 \end{gathered}
\]
For j=L or M, define the exact rational coefficients, apart from
the displayed constant Cj,
\[
 \begin{split}
 A_j&=-\kappa-\rho h_a+(\rho+\mu)f_{aj},\\
 B_j&=-\rho h_b+(\rho+\mu)f_{bj},\\
 C_j&=-\kappa/2+\rho h_0-(\rho+\mu)f_{0j}.
 \end{split}                                                   \tag{33}
\]
Then \(K_\mu=-A_jx-B_jt+C_j\). The source and target
support calculations below are on the full original arcs.

### 7.1 The L target: mu=1.7, lambda=2.36

The target brace is concave on L and its two endpoint values give
\[
                    -K_\mu(A,B)-\lambda B>-1.6116.              \tag{34}
\]
For an L source,
\[
                 K_\mu(a(b_1),b_1)>.8452.                    \tag{35}
\]
Its source brace differs from its value at b1 by at most a loss
of .0016. Here is a bound over the entire L arc. In t coordinates,
the variable part is
\[
 f(t)=-(A_L+\lambda\cos z)\sqrt{Q-t^2}
                         +(-B_L+\lambda\sin z)t.
\]
Throughout [0,.7],
\[
 A_L+\lambda\cos z>2.53,\quad
 \frac Q{(Q-t^2)^{3/2}}>.55,
                       \quad f'(b_1+1/2)<.065.                \tag{36}
\]
For the last assertion, the derivative at b1 equals
\(-B_L+r_1A_L+\lambda(\sin z+r_1\cos z)\), where
\(r_1=(b_1+1/2)/(4b_1+1/2)<.459\). It increases in z on
this interval, and the upper sine/cosine polynomials at .7 give
the stated bound. Strong convexity gives
\[
 f(t)\ge f(b_1+1/2)
             -\frac{.065^2}{2(2.53)(.55)}
                        >f(b_1+1/2)-.0016.                   \tag{37}
\]
If the endpoint derivative is nonpositive there is no loss;
otherwise (37) is the single quadratic completion on t<=b1+1/2.

For an M source, use its full shifted-circle support instead:
\[
 \begin{split}
 C_M&>10.9221,\\
 K_\mu(a,b)-\lambda a\cos z+\lambda b\sin z
 &\ge C_M+\frac\lambda2(\cos z-\sin z)-R N(z),\\
 N(z)^2&=A_M^2+B_M^2+\lambda^2
                       +2\lambda(A_M\cos z-B_M\sin z).       \tag{38}
 \end{split}
\]
The actual M/L bonus is .0093.

### 7.2 The M/H target: mu=5, lambda=4.65

Both target charts have the common bound
\[
                    -K_\mu(A,B)-\lambda B>-1.357.              \tag{39}
\]
On M it follows by concavity and the two endpoints. On H,
full-circle support gives
\[
 \frac\kappa2+\mu h_0+\frac\lambda2
  -\sqrt{Q\{(\kappa-\mu h_a)^2+(\lambda-\mu h_b)^2\}}
                         >-1.357.
\]
The radical is less than 9.3445 by a rational square comparison.

For an L source its source brace decreases across the entire L
arc. Its endpoint derivative is negative, as is verified at the
largest angle .7 by the same increasing expression used in (36).
Consequently the endpoint is the exact minimum, and
\[
                    K_\mu(a(b_1),b_1)>-.1673.                 \tag{40}
\]
For an M source use (38), now with \(C_M>23.0594\). The
minimum permitted bonuses are .0093 for source L and .0172 for
source M. These allow either M or H as target; M/M has the
slightly stronger actual bonus .0186.

All bounds (34)--(40) follow by direct substitution in (33) and
(7), or by one displayed full-circle support. For example the
two target endpoint values on L are bounded below by
\[
 -C_{L,U}+A_L X_{\rm low}+(B_L-\lambda)t_{\rm low}
                                           +\lambda/2,
\]
with the appropriate b=0 or b=b1 endpoints. The coefficients
used there are positive. Thus the finite constant bounds concern
actual intrinsic endpoints, not sampled states.

## 8. Four whole-interval scalar checks

Let Sn and Cn be the ordinary alternating sine and cosine Taylor
polynomials ending at their indicated degree. Set
\[
 \eta=.957,\quad \pi_L=3.14159,\quad
 a_{1,U}=4(.3246869),\quad b_{1,L}=.3246868,
                           \quad\overline R=1.978788.
\]
The signs of every Taylor substitution below are fixed, on the
whole interval 0<=z<=.7.

For an endpoint source bound K, target bound g, and bonus B,
define the degree-eight polynomial
\[
 \begin{split}
 E(z)={}&(1+\mu)\pi_L/2-\mu(C_*-B)+K+g+\lambda/2-\mu\beta/2
            -(1+\mu)z\\
 &+\{\lambda(1/2-a_{1,U})+\mu\beta/2\}C_8(z)\\
 &+\{\lambda(1/2+b_{1,L})+\mu\beta/2\}S_7(z).                \tag{41}
 \end{split}
\]
The cosine coefficient is negative and the sine coefficient
positive in both uses.

### 8.1 L source, L target

Use
\[
 (\mu,\lambda,K,g,B)=(1.7,2.36,.8452,-1.6116,0),
 \qquad P_L=E-\eta-.0016.
\]
By (13), (34)--(37), positivity of PL proves the desired bound.
Expand \(P_L(.55+w)=\sum_{j=0}^8 a_jw^j\), with
\(-.55\le w\le.15\). Direct expansion of (41) gives
\[
 a_0>.00703,\quad |a_1|<.00502,\quad
 a_2+\sum_{j=3}^8\min_{-.55\le w\le.15}(a_jw^{j-2})>.1137.
                                                                    \tag{42}
\]
Each minimum in this coefficient sum is merely the minimum of
an indicated signed monomial, hence is evaluated at an interval
endpoint or at zero. It follows on the entire interval that
\[
 P_L>.00703-.00502|w|+.1137w^2
       \ge.00703-\frac{.00502^2}{4(.1137)}>.00697>0.             \tag{43}
\]

### 8.2 M source, L target

For the parameters in (38), take the positive polynomial
\[
                   p(z)=7.315-1.29z-.72z^2.
\]
Define
\[
 \begin{split}
 N_+^2&=A_M^2+B_M^2+\lambda^2
                         +2\lambda(A_MC_8-B_MS_7),\\
 D(z)&=(1+\mu)\pi_L/2-\mu(C_*-B)+C+g+\lambda/2-\mu\beta/2
          -\eta-(1+\mu)z\\
     &\hspace{12mm}+(\lambda+\mu\beta/2)C_{10}(z)
                              +(\mu\beta/2)S_7(z),\\
                         P_M(z)&=2p(z)D(z)
                                   -\overline R\{p(z)^2+N_+^2(z)\},
 \end{split}                                                   \tag{44}
\]
using
\[
       (\mu,\lambda,C,g,B)=(1.7,2.36,10.9221,-1.6116,.0093).
\]
Since \(N^2\le N_+^2\), the elementary inequality
\(N\le(p^2+N^2)/(2p)\) shows that PM>0 suffices. All
denominators are positive, and \(R<\overline R\).

This is one polynomial of degree twelve. Writing
\(P_M(z)=\sum_{j=0}^{12}p_jz^j\), its exact coefficient sums are
\[
 p_0>.073,\qquad p_1>.036,\qquad
 p_2+\sum_{j=3}^{12}\min(0,p_j)(.7)^{j-2}>.095.                \tag{45}
\]
Thus \(P_M>.073+.036z+.095z^2>0\) throughout [0,.7].

### 8.3 L source, M/H target

Use (41) with
\[
       (\mu,\lambda,K,g,B)=(5,4.65,-.1673,-1.357,.0093).
\]
The underlying trigonometric expression decreases: its derivative
is \(-6-A\sin z+B'\cos z\), where A and B' are the
displayed cosine and sine coefficients, and
\(A^2+(B')^2<36\). It is therefore enough to substitute z=.7
with the Taylor directions used in (41). The result is
\[
                              E(.7)-\eta>.0118>0.              \tag{46}
\]
This proves the full-interval bound, not just the endpoint value
of an otherwise unchecked polynomial.

### 8.4 M source, M/H target

Use (44) with
\[
 \begin{gathered}
 (\mu,\lambda,C,g,B)=(5,4.65,23.0594,-1.357,.0172),\\
                         p(z)=16.205-2.643z-1.462z^2>0.
 \end{gathered}
\]
Again PM has degree twelve. Expand at \(h=.35\):
\(P_M(h+w)=\sum a_jw^j\), \(|w|\le h\). Direct expansion
of the fixed formula gives
\[
 a_1+\sum_{j=2}^{12}j h^{j-1}
  \begin{cases}
    |a_j|,&j-1\text{ odd},\\
    \max(0,a_j),&j-1\text{ even}
  \end{cases}
                         <-6.4,\qquad P_M(.7)>1.16.            \tag{47}
\]
The left side bounds the derivative on the entire interval. Hence
PM decreases and stays strictly positive.

Equations (42), (45), (46), and (47) are arithmetic statements
about four explicitly printed polynomials or trigonometric
expressions. They use one full interval each, with no subdivision
or numerical feasibility premise. The coefficients are obtained
by ordinary multiplication of the displayed rational Taylor
polynomials; the signed-monomial bounds and the quadratic
completion prove their whole-interval conclusions.

## 9. Completion

For nonnegative error, the original cap gives H/L, and (11), (17)
prove the claim. For negative error, (12) reduces either original
owner to the actual P2 inequality. Source H is covered by Sections
4--6. Source L or M is covered by the two fixed choices (14) and
their full-interval support and scalar proofs in Sections 7--8.
The bounds are all strict and retain either allowed original
marker at a cut. Therefore every original negative outer-to-outer
high-quarter bridge in the cycle satisfies (4).

This proves precisely the remaining bridge component for the
common potential (2). Summing it with the three quarter and three
zero components is a separate, immediate cyclic assembly; no
other owner or sign class is claimed here.
