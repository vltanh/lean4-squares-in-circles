# Positive GA1 with a sole nonnegative DE3, or with both E edges secondary

## 1. Actual domain and finite entry statement

Put
\[
 Q_1=1957767069/500000000,\quad R=\sqrt{Q_1},\quad h=7/10,
 \qquad a_0=\sqrt{Q_1-1/4}-1/2.
\tag{1}
\]
All decimals below are exact rationals. Work with sorted contained
states at a common actual ceiling q at most Q1. H,A have nonnegative
signed tangents, B,D nonpositive signed tangents, and E nonpositive
signed tangent. Write its magnitude as b_E. G,T may have either sign.
The actual errors have zero sum and positive and negative variations
at most h. Retain the actual weak witnesses
\[
 HG2,\quad GA1,\quad AB0\text{ or }AB2,\quad BT2,\quad TD0,
 \qquad d_{GA}=x\ge0.
\tag{2}
\]
There are two allowed E regimes:

1. DE3 has error e at least zero, and EH0 has arbitrary error.
2. DE2 and EH0 both have arbitrary errors. In this regime put e=0
   as an absent-primary parameter; neither actual E error is changed.

**Theorem.** Neither necessary system exists. The contradiction is
strict at Q1, includes x=0 and e=0, and allows every sign of the
remaining errors and both AB owners. No core/outer equality is
needed. In particular the theorem applies to original outer E.

The sign of E is an input in the sole-DE regime: the proof uses
\(a_E-\eta b_E\le a_0\) with \(b_E\ge0\). It does not assert
this strict exclusion after an arbitrary sign-changing E transport.
The two-secondary regime cancels E altogether and permits either
E sign. The argument changes no actual state or witness.

We use the continuous circle-envelope facts and the three coefficient
families in [the positive-EH endpoint theorem](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md).
The changed ordinary block is kept explicitly below: EH0 belongs to
H, so H can have two ordinary errors. This is why its negative
coefficient is sometimes max(1,n), rather than n.

## 2. The positive stress and the exact axis support

Set t=x+e in the sole-DE regime, and t=x in the secondary regime.
Thus 0<=t<=h. On the low interval 0<=t<=.2 use
\[
 k=.86265+.55t+.3t^2,\quad c=k+.3t,\quad
 l=.50521+.823t+.7t^2,\quad g=.32.
\tag{3}
\]
On .2<=t<=.35 put z=t-.2 and use
\[
 k=.983+.10z-.3z^2,\quad c=1.045+.65z-1.5z^2,
 \quad l=.698+.9z-z^2,\quad g=.31.
\tag{4}
\]
On .35<=t<=h use
\[
 k=1.017-.02t,\quad c=1.13,\quad l=.70+.36t,
 \quad g=.27+.08t.
\tag{5}
\]
Always put
\[
 n=k(\cos x+g\sin x),\qquad
 \sigma_g=R\sqrt{1+g^2}-(1+g)/2.
\tag{6}
\]
In (3)--(4) put r=cos(e)+.7sin(e). In (5) put r=1.
The seven multipliers in cyclic order are
\[
                         (n,k,l,c,c,1,r).
\tag{7}
\]
All are positive. The G force is k sin(x) times
\(a_G+g(-y_G)\), bounded above by k sigma_g sin(x) for
either G sign. The signed T tangent cancels exactly.

In the sole-DE regime the exact E force is
\[
 a_E\sin e+b_E(\cos e-r)
 \le a_0\sin e.
\tag{8}
\]
For (3)--(4), its left side is sin(e)(a_E-.7b_E).
For (5), the additional term is -b_E(1-cos(e)). Both are
bounded as stated because b_E>=0, a_E<=a0 and e>=0.
In the two-secondary regime the E tangent cancels, with r=1.

The four anchor pairs when ordinary errors are zero are
\[
                    H:(r,n),\quad A:(k,l),\quad
                    B:(l,c),\quad D:(1,c).
\tag{9}
\]
The actual HG2 and EH0 rotations belong to H; AB belongs to
A or B according to its retained owner; BT2 belongs to B;
TD0 belongs to D. The secondary DE2 rotation, when present,
also belongs to D. All these actual errors are retained.
For two angles at one anchor their exact force norm is
\(\sqrt{a^2+b^2+2ab\sin(u+v)}\), with the appropriate
positive base coefficients from (9).

## 3. Split the two nonnegative primary errors before taking supports

Fix t, the ordinary errors, and the actual sorted anchor coordinates.
Only x and e=t-x vary in this scalar comparison. The ordinary
signed sum remains -t; this is not a motion of any square.
After (8) and the G support, the two varying residual multipliers
have actual residuals
\[
 M_{HG}=W(u)-a_H\sin u-b_H\cos u>-.065,
\]
\[
 M_{EH}=W(v)-a_H\cos v-b_H\sin v>-.415,
 \qquad W(s)=(1+\cos s+|\sin s|)/2.
\tag{10}
\]
These are precisely the uniform transverse and radial residual
bounds (19)--(20) of the positive-EH note; their proofs require
only sorting and the actual circle. Also sigma_g-.5<.935 and
a0-.5<.915.

On (3)--(4), the second derivative along the split is therefore
bounded above by
\[
 k\{-.435\cos x+.956\sin x\}
                -.085\cos e+1.2055\sin e.
\tag{11}
\]
Here the larger last coefficient is .915+.415(.7); the unchanged
G coefficient is bounded using g<=.32. At x=0 its value is less than
\[
             -.435(.862)-.085(.9393)+1.2055(.343)<-.041.
\]
At x=t it is less than -.15. For fixed t the expression is a
linear combination of sin(x) and cos(x). Division by positive
cos(x) makes it affine in tan(x), so the two negative endpoint
values imply negativity on the entire interval. Its second
derivative is its negative; hence it is convex, and its maximum
is at an endpoint. Thus (11) is everywhere less than -.04.

On (5) there is no varying E multiplier. The same calculation
instead gives
\[
 k\{-.435\cos x+.961\sin x\}
                    -.5\cos e+.915\sin e.
\tag{12}
\]
This is the identical high-family split bound (25) in the
positive-EH note, whose endpoint proof gives a bound below -.20.

Consequently it suffices to prove strict positivity at
\[
                              (x,e)=(0,t),(t,0).
\tag{13}
\]
This split was made before the independent H,A,B,D circle supports,
so it does not assume that a support-maximizing state is an actual
packing. With no E primary only the G endpoint of (13) is needed.

## 4. The ordinary-angle envelope, including both H arguments

For a sorted positive pair a<=b define
\[
 U_{a,b}(s)=a(\cos s+\sin s-1)
 -R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\},
\]
\[
 V_{a,b}^{\nu}(s)=\nu(\cos s-1)
 -R\{\sqrt{a^2+b^2-2ab\sin s}-\sqrt{a^2+b^2}\}.
\tag{14}
\]
The actual available negative coefficients are
\[
 \nu_H=\max(r,n),\quad \nu_A=l,\quad
 \nu_B=c,\quad \nu_D=c
\tag{15}
\]
for sole DE. With both E edges secondary replace nu_D by max(1,c).
At the middle and high G endpoints c>1, so this makes no change.
On the low interval the common bound below handles either value.

The separate-concavity and two-simplex concentration proof used
in Section 4 of the positive-EH note applies to (9), (15).
Its remaining variations satisfy P<=h-t, N<=h and N-P=t.
It leaves pure negative terms at t, same-block terms, or a
positive term at h-t separated from a negative term at h.
The H block is now allowed both signs. Its smaller/larger ratio
is above .77 on the low interval and above 2/3 elsewhere, so the
same-block comparison applies to H as well as B,D. The A block
continues to use its actual coefficient l.

### 4.1 Low t: the canonical B charge still dominates

Write V_B=V_{l,c}^c. All A/B coefficient bounds in (34)--(39)
of the positive-EH note are unchanged. They prove
\[
             V_A(t)\ge V_B(t),\quad V_B(t)<1.15t,
\tag{16}
\]
and the same-block B comparison. For H and D, the two
coordinates are at least those of (.86265,1), their ratio
exceeds .77>sin(h), and their negative coefficient is at most
1.12. The norm gain therefore gives
\[
 V_H(t),V_D(t)\ge1.292\sin t-1.12(1-\cos t)>1.17t.
\tag{17}
\]
For the last inequality use sin(t)>=t(1-.2^2/6) and
1-cos(t)<=t^2/2. The coefficient of t is then greater than
1.1713. The inequality
R(.86265)/sqrt(1+.86265^2)>1.292 follows by positive squaring.

At h the same monotone norm-gain comparison gives
\[
 V_H(h),V_D(h)>.775>V_B(h),\qquad V_A(h)\ge V_B(h).
\tag{18}
\]
For an explicit check of the first bound use
\[
 R>1.9787,\quad \sqrt{1+.86265^2}>1.32066,
\]
\[
 \sqrt{1+.86265^2-2(.86265)\sin h}<.79543,
 \qquad \cos h>.7648.
\]
Thus the left side exceeds
1.9787(1.32066-.79543)-1.12(.2352)>.775.
The B upper bound .72 and A comparison are unchanged from
Section 4.2 of the positive-EH note. Norm-gain monotonicity
holds along the comparison rectangle because every intermediate
ratio exceeds .77>sin(h); no negative-coordinate support is used.

For every pair in (9), its larger coefficient is at most
1+.7t. Indeed r<=1+.7t, c and k obey this immediately from
(3), and n<=k(1+.32t)<=1+.7t on [0,.2]. The established
uniform bound U_{a,b}(P)>=-.545bP therefore implies
\[
 U_i(h-t)\ge-.545(1+.7t)(.7-t)\ge-.3815.
\tag{19}
\]
The last quadratic decreases on [0,.2]. The exact certificate
(55)--(56) of the positive-EH note still supplies
\[
                            V_B(h)-V_B(t)>.43.
\tag{20}
\]
Equations (18)--(20) dispose of every separated alternative
with reserve .0485. H and D same-block terms dominate their
pure terms since their ratios exceed sin(h); the B statement
is already included in (16). The complete low ordinary envelope
is therefore bounded below by V_B(t), with both H angles and
with both D angles when DE is secondary.

### 4.2 Middle and high t

Every coefficient ratio is at least 2/3. Thus the same-block
comparison (29) of the positive-EH note removes those terms.
The derivative bound (30) there gives
\[
                         (V_{a,b}^{\nu})'(w)>.674b
            \quad(0<=w<=h,\ \nu<=b).
\tag{21}
\]
In the middle family every larger coefficient lies in [.983,1.18].
Together with U>=-.545bP, the comparison
\[
                       .674(.983)-.545(1.18)>0
\tag{22}
\]
removes every separated alternative. In the high family the
larger coefficients lie in [1,1.13], and the corresponding
comparison .674-.545(1.13)>0 does the same. These ranges follow
from (4)--(6), r<=cos(.35)+.7sin(.35)<1.18 on the middle
interval, and r=1 on the high interval.

Only the four actual pure negative charges in (15) remain.
This includes every original ordinary sign allocation.

## 5. Endpoint scalars and the reused certificates

On the low and middle intervals put r(t)=cos(t)+.7sin(t) and
\[
\begin{split}
 B_E(t)={}&3k+2l+3c+1+\tfrac12\cos t
       +(\tfrac12-a_0)\sin t+\tfrac32r(t)\\
 &-R\{\sqrt{r(t)^2+k^2}+\sqrt{k^2+l^2}
                    +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{23}
\]
This is the exact four-anchor stress at x=0 after (8).
The negative pairs there are
\[
 (r,k;r),\quad(k,l;l),\quad(l,c;c),\quad(1,c;c),
\tag{24}
\]
where the last entry is nu. In (24), r>k on the middle
interval; on the low interval only V_B is needed.
The new scalar requirements are B_E+V_B>0 on [0,.2],
and B_E+V_i>0 for i=H,A,B,D on [.2,.35].

At the G endpoint r=1. Its baseline is exactly B_G in (43)
of the positive-EH note. Low positivity with V_B and all
four middle positivities are therefore already certified.
On the high interval all old G certificates still apply except
possibly H: its actual coefficient is max(1,n), which is at
most 1.06. We supply the stronger new certificate
\[
 B_G+V_{1,n}^{1.06}>0\qquad(.35<=t<=h).
\tag{25}
\]
Since cos(t)-1 is nonpositive, (25) implies the required
inequality for max(1,n).

For the high E endpoint use the old equal-multiplier baseline
with the new charge
\[
             j_{DE}(t)=\tfrac12(\cos t-1)
                                 +(\tfrac12-a_0)\sin t.
\tag{26}
\]
It is at least sin(t)-2R sin(t/2): the full-circle support
in direction (sin(t),1-cos(t)) is at least its support at
the actual axis point (a0,0). Hence each high E scalar is
bounded below by the corresponding already certified high E
scalar (44)--(46) of the positive-EH note. Its four actual
negative coefficients agree: k,l,c,c.

## 6. Six exact whole-interval polynomial certificates

Here are complete rational specifications for the five new
scalars (23)--(24) and the one scalar (25). Put
\[
 R_+=1.978770866>R,\quad a_+=1.414558471>a_0,
\]
\[
 S(t)=\sum_{j=0}^7\frac{(-1)^jt^{2j+1}}{(2j+1)!},
 \qquad C(t)=\sum_{j=0}^8\frac{(-1)^jt^{2j}}{(2j)!}.
\tag{27}
\]
The two radical inequalities follow by positive squaring.
The uniform errors on [0,h] are below 7e-18 and 3e-19.

Use z=t-a and D=.2,.15,.35 for a=0,.2,.35 respectively.
For a new E scalar substitute its coefficient family, set
r=C+.7S, and start with
\[
 A=3k+2l+3c+1+C/2+(1/2-a_+)S+3r/2,
\]
\[
 (v_H,v_A,v_B,v_D)=(r^2+k^2,k^2+l^2,l^2+c^2,1+c^2),
\]
\[
 (b_H,b_A,b_B,b_D)=(rk,kl,lc,c),\quad
 (\nu_H,\nu_A,\nu_B,\nu_D)=(r,l,c,c).
\tag{28}
\]
For its negative index i, add nu_i(C-1) to A and replace
v_i by v_i-2b_iS. Each resulting squared norm has weight 1.
Use only i=B in the low family and all four indices in the
middle family.

For (25) use the high family, n=k(C+gS), and
\[
 A=3+2l+3c+k\{1+2C+(1+2g)S\}+1.06(C-1).
\]
The squared norms and weights are
\[
 (1+n^2-2nS,1),\ (k^2+l^2,1),\ (l^2+c^2,1),
 \ (1+c^2,1),\ (1+g^2,kS).
\tag{29}
\]
The last pair accounts for the G tilt support.

For each squared-norm polynomial v let v0=v(0)>0 and define
\[
 \rho_0=1,\quad\rho_{j+1}=(\rho_j+v_0/\rho_j)/2\ (j=0,1,2),
\]
\[
 w=([v]_{<=3}-v_0)/v_0,\qquad
 m_v=[\rho_3(1+w/2-w^2/8+w^3/16)]_{<=3}.
\tag{30}
\]
The brackets truncate in z. For the resulting list (v_j,w_j)
form the explicit rational polynomial
\[
 P=2A\prod_jm_{v_j}
       -R_+\sum_j w_j(v_j+m_{v_j}^2)\prod_{r\ne j}m_{v_r}.
\tag{31}
\]
The mass inequality
\[
             \sqrt v\le(v+m^2)/(2m)\qquad(m>0)
\tag{32}
\]
turns positivity of P into the required scalar inequality.
Every mass is positive on its whole interval.

For the low polynomial, write P(z)=sum a_j z^j, of degree 41.
Its Bernstein coefficients on [0,.2] are exactly
\[
             B_i=\sum_{j=0}^i a_j(.2)^j
                    \frac{\binom{i}{j}}{\binom{41}{j}}
                    \quad(0<=i<=41).
\tag{33}
\]
All 42 coefficients exceed .00259. This is one polynomial
identity over the entire interval: the Bernstein basis functions
are nonnegative and sum to 1. No state or angle subdivision occurs.

For the other five polynomials use the coefficient-norm identity
(53)--(54) of the positive-EH note. The exact rational bounds are:

| Polynomial | Degree | Lower bound for P | Lower bound for every mass |
| --- | ---: | ---: | ---: |
| Low E, B | 41 | .00259 | .99230 |
| Middle E, H | 44 | .40412 | 1.20551 |
| Middle E, A | 41 | .03846 | 1.04314 |
| Middle E, B | 41 | .01966 | 1.12660 |
| Middle E, D | 41 | .37421 | 1.20551 |
| High G, H with coefficient 1.06 | 43 | .03719 | .83162 |

These bounds follow by rational additions, multiplications and
comparisons in (27)--(33). The numerator partial bounds used in
the positive-EH note remain valid: fewer than six masses, masses
less than 3, absolute outside part less than 30, squared norms
less than 6, and input derivatives less than 30. Even the uniform
upper bound 1e7 for each partial makes the total Taylor error less
than 1e-8. It is below every displayed numerator reserve.
This proves all six new scalars without a sampled premise.

## 7. Consequence and remaining paired-E input

Sections 4--6 prove both intrinsic endpoints (13) strictly positive
for every retained ordinary sign allocation. The scalar concavity
of Section 3 then proves the original positive stress strictly
positive. Actual weak feasibility and the positive weights (7)
make the same stress nonpositive, a contradiction.

Together with the positive-EH endpoint theorem, this closes every
single-primary or two-secondary E alternative with HG2, positive
GA1, BT2 and arbitrary TD0, after any justified same-state
replacement of a nonpositive E primary by its secondary owner.
For original outer E those replacements are supplied by the
[outer-E witness comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md),
with its same-radius version when q is below Q.

A pair of positive E primaries is a separate finite join. The
[sign-preserving E-pair reduction](HAND_G5_COUPLED_POSITIVE_E_PAIR_SAME_RADIUS_ENDPOINTS.md)
can leave an actual E=0 endpoint with both primaries still positive.
The present theorem does not remove that endpoint merely because
it includes b_E=0 in its sole-primary statement. Nor does it assert
BT3 entry or a primary TD2 case. No unconditional equality claim
or Lean verification is made.
