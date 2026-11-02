# An endpoint-owned oblique separator can replace the vertical comparison

November 1, 2026 America/Chicago / November 2 UTC. Complete hand
derivation of the explicitly stated owner branch. No numerical search,
mathematical program, Lean, Lake, or CI. This result removes the actual
vertical shoulder-to-main premise in one physical owner class; it does
not cover every physical separator owner or close unrestricted A.2.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 \mu=\frac{k}{b}=\frac{23}{24},\quad T=\frac{211}{4},
 \quad\kappa=r-\frac{11}{8}.
\]
For a centered physical unit square S let H_S(v) be its support
halfwidth and h_S=H_S(e_x)=H_S(e_y).

## 1. Exact geometric hypotheses and transfer statement

Suppose an actual horizontal four-chain M0<_xM1<_xM2<_xM3 and two
physical outsiders A,B are interior-disjoint in a centered disk of
radius R_0<=r. Write M=M0. Assume A lies in the left side column,
\[
                         x_A\le-29/60.                 \tag{1}
\]
Suppose there is a genuine unit separating normal from M toward A,
\[
 n=(c,s),\quad s\ge|c|,\quad c^2+s^2=1,
 \quad n\cdot(c_A-c_M)\ge H_M(n)+H_A(n),              \tag{2}
\]
and this normal is parallel to a physical side axis of M. The letter
c here is a horizontal component, not a center or a floor height.
Thus (2) is an upward, nearly vertical, **endpoint-owned** separator.
No actual vertical projection comparison of M and A is assumed.

Suppose A toward B has a genuine right-and-upward separator,
\[
 (1,z)\cdot(c_B-c_A)\ge H_A((1,z))+H_B((1,z)),
 \qquad z\ge0.                                       \tag{3}
\]
The allowed domains are
\[
 \boxed{c\le0:\ \text{all }z\ge0;\qquad
         c>0:\ 0\le z\le7/5.}                        \tag{4}
\]
In the left-side coordinates, c<0 means the separator from the outer
main points horizontally outward; c>0 means it points inward.

Define the same central and shoulder reserves as in the established
upward-transfer proof:
\[
 E_B(z)=H_B((1,z))+(1+z)h_B-(1+z)\ge0,
\]
\[
 D_A=(1+\mu)h_A+H_A((-1,\mu))-(1+\mu)\ge0,
\]
\[
 \Psi_A(z)=H_A((1,z))-h_A+z(h_A-\kappa)+D_A.
\]
Then, under (1)--(4),
\[
\begin{aligned}
 &a(-x_M-h_M)+b(1-x_B-h_B)\\
 &\qquad\le T-bE_B(z)-b\Psi_A(z)
                         -bz(r-h_B-y_B).              \tag{5}
\end{aligned}
\]
This is exactly the retained upward-transfer bound needed for the
shared-central-orientation proof. It is strict if R_0<r or c is nonzero.
Since Psi_A(z)>0 for z>0, its coarse bound by T is also strict for
every positive z. Horizontal reflection supplies the right-side version.

## 2. Endpoint tilt and the retained orientation reserve in a physical cap

The proved actual-four estimates give
\[
 -91/60<x_M<-89/60,\quad h_M<8/15,
 \quad |y_M|+\frac{37}{50}(h_M-1/2)\le\frac18.          \tag{6}
\]
Let epsilon=|c|. Because M owns n and s>=epsilon,
\[
 h_M=(s+\epsilon)/2,\qquad j_M=(s-\epsilon)/2.
\]
Equation (6) implies
\[
 \epsilon<1/14,\qquad s>27/28,\qquad
       \frac{1-s}{\epsilon}=\frac{\epsilon}{1+s}<\frac2{55}
                  \quad(\epsilon>0).                 \tag{7}
\]
Indeed epsilon+sqrt(1-epsilon^2) is increasing on [0,1/sqrt(2)].
Its value at 1/14 exceeds 16/15, since
sqrt(195)>209/15, with squared reserve 195*225-209^2=194.
Also s>sqrt(195)/14>27/28. These give the last ratio in (7).

We will prove the physical weighted cap retains A's complete vertical
orientation reserve, even when M,A are not vertically projection-separated:
\[
 a(-x_M-h_M)+b(-x_A-h_A)\le T-bD_A-\Gamma(c),           \tag{8}
\]
where
\[
 \Gamma(c)=
 \begin{cases}
 (42619/1760)c,&c\ge0,\\
 (7199/1760)|c|,&c<0.
 \end{cases}                                         \tag{9}
\]
For c nonzero the estimate is strict; for R_0<r the disk-support
step is strict as well.

Apply containment supports in directions -a e_x-k n and -b e_x+k n,
and use the actual physical separator (2). The left side of (8) is at
most
\[
 H(c)-P_M(c)-P_A(c),
\]
\[
 H(c)=r\left(\sqrt{a^2+k^2+2ak c}
                       +\sqrt{b^2+k^2-2bk c}\right),
\]
\[
 P_M=a h_M+H_M(ae_x+kn)+kH_M(n),
\]
\[
 P_A=b h_A+H_A(be_x-kn)+kH_A(n).                       \tag{10}
\]
Direct differentiation shows H is concave. Its values at zero are
\[
 H(0)=T+(a+b+2k),\qquad H'(0)=k/2,
\]
so H(c)<=H(0)+(k/2)c.

Since M owns n, the three support terms in P_M can be evaluated in
M's side frame. By epsilon<1/14<k/a,
\[
 P_M(c)=
 \begin{cases}
 k+a(c+s),&c\ge0,\\
 k+as,&c<0.
 \end{cases}                                         \tag{11}
\]

To retain A's actual orientation, take a vertex v maximizing
(e_x-mu e_y).v and a vertex w maximizing e_y.w. Both belong to
the same centered square A. They may be chosen so that
\[
                   -1\le (w-v)_x\le0,\qquad
                    0\le(w-v)_y\le\sqrt2<3/2.         \tag{12}
\]
Here is the complete two-chirality check. Let alpha>=beta>=0 be
A's absolute side-axis components, h=(alpha+beta)/2 and
j=(alpha-beta)/2. For one chirality take v=(h,-j), w=(j,h),
giving difference (-beta,alpha). For the other take w=(-j,h).
Its maximizing v is (h,j) when beta>=mu alpha, giving (-alpha,beta),
and is (j,-h) when beta<=mu alpha, giving (-alpha+beta,alpha+beta).
At a tie either choice works. These are all cases and prove (12).

Use these fixed vertices as support witnesses at n. With
Delta=w-v,
\[
 P_A(c)\ge P_A(0)+k\{c\Delta_x+(s-1)\Delta_y\},
 \qquad P_A(0)=b+k+bD_A.                              \tag{13}
\]
Combining (10)--(13), for c>=0 the cap reserve beyond bD_A is at least
\[
 (a-3k/2)c-(a+3k/2)(1-s)
 >\left(\frac{851}{32}-\frac2{55}\frac{2093}{32}\right)c
 =\frac{42619}{1760}c
\]
when c>0. For c<0 it is at least
\[
 (k/2)|c|-(a+3k/2)(1-s)
 >\left(\frac{207}{32}-\frac2{55}\frac{2093}{32}\right)|c|
 =\frac{7199}{1760}|c|.
\]
The c=0 case follows directly. This proves (8)--(9) without replacing
the physical M,A pair by a vertical comparison.

## 3. The endpoint budget also controls the shoulder's whole floor

The actual-four outsider-strip theorem and (1),(6) give
\[
              2/5<d:=x_A-x_M<31/30.                   \tag{14}
\]
From (6),
\[
             y_M+h_M\ge3/8+\frac{87}{50}(h_M-1/2).    \tag{15}
\]
The coefficient is 1+37/50: an endpoint tilt reduces the allowed
negative center height as well as increasing its halfwidth.
For epsilon>0, (7) gives
\[
 h_M-1/2=\frac{\epsilon}{2}
               \left(1-\frac{\epsilon}{1+s}\right)
                    >\frac{53}{110}\epsilon.          \tag{16}
\]

A topmost vertex of A has offset (plus or minus j_A,h_A), where
0<=j_A<=1/2. Thus H_A(n)>=s h_A-epsilon j_A. Since M owns n,
H_M(n)=1/2, and (2) yields
\[
 y_A-h_A\ge y_M+h_M
     -\frac{\epsilon}{s}(j_M+j_A+\operatorname{sgn}(c)d).
                                                               \tag{17}
\]
This uses the identity 1/(2s)-h_M=-(epsilon/s)j_M.

When c<0, equations (14)--(17), j_M+j_A<=1, and 1/s<28/27 give
\[
 y_A-h_A>
 \frac38+\left(\frac{4611}{5500}-\frac{28}{45}\right)\epsilon
 =\frac38+\frac{10699}{49500}\epsilon>\frac38.
                                                               \tag{18}
\]
When c>0, they instead give
\[
 y_A-h_A>
 \frac38-\left(\frac{854}{405}-\frac{4611}{5500}\right)c
                       >\frac38-\frac{32}{25}c.       \tag{19}
\]
For the final comparison, the positive difference is
\[
 \frac{32}{25}-\left(\frac{854}{405}-\frac{4611}{5500}\right)
                         =\frac{4331}{445500}>0.
\]
At c=0, (2) is an actual vertical comparison and (15) gives the
same floor 3/8 directly. Define
\[
                 \delta(c)=\frac{32}{25}\max(c,0).
\]
We have proved, in every case,
\[
                         y_A-h_A\ge3/8-\delta(c).      \tag{20}
\]

## 4. The physical cap reserve pays for the lost whole floor

Put ell=r-h_B-y_B>=0, using containment of B. Then (20) gives
\[
 y_B-y_A\le1+\kappa-h_A-h_B+\delta(c)-\ell.
\]
Let d'=x_B-x_A. Substitute this bound in (3), add h_B, and retain
the central support excess. The resulting inequality is
\[
 d'+h_B\ge1+H_A((1,z))+z(h_A-\kappa)
                             +E_B(z)-z\delta(c)+z\ell.
\]
Equivalently,
\[
 1-d'-h_B+h_A\le D_A-\Psi_A(z)-E_B(z)+z\delta(c)-z\ell.
                                                               \tag{21}
\]
Add b times (21) to (8). The result is
\[
 a(-x_M-h_M)+b(1-x_B-h_B)
 \le T-bE_B-b\Psi_A-bz\ell-\Gamma(c)+bz\delta(c).
                                                               \tag{22}
\]
If c<=0 then delta=0, so its last two terms are nonpositive for
every z. If c>0 and z<=7/5, the exact comparison is
\[
 \Gamma(c)-bz\delta(c)
 \ge\left(\frac{42619}{1760}-\frac{3024}{125}\right)c
                       =\frac{1027}{44000}c>0.        \tag{23}
\]
Thus (22) proves precisely (5) on the domains (4).

## 5. How this removes an endpoint premise in a paired terminal

The retained right side in (5) is identical to the one used for an
ordinary matched upward transfer. Therefore the all-upward shared-central
argument applies if, on each side independently, one has either:

1. the previously required actual vertical comparison; or
2. the physical endpoint-owned hypotheses (1)--(4), reflected on the
   right side.

The common central square still uses one orientation, and the two
shoulder reserves pay its full joint-orientation loss. The four-chain
span then contradicts every radius R_0<r. At radius r a nonvertical
endpoint normal in (2), or a positive shoulder-to-central slope in (3),
forces strictness. Thus equality in this owner branch can only route
back to vertical matched endpoint separators and an actual horizontal
three-chain.

The same retained inequality can replace the upward side of the
mixed-sign terminal wherever that terminal's central-floor, central-band,
and upward-slope conditions are established. It does not replace a
downward-transfer premise. The next section treats arbitrarily steep
upward slopes without any ownership condition on the A,B separator.

## 6. Retaining both support branches removes every upward-slope restriction

Retain (1)--(3), with **no ownership condition on the A,B separator**.
The restriction z<=7/5 in the inward case can be removed from the
paired terminal. For z>7/5 the retained transfer uses an adjusted
shoulder reserve, whose two needed lower bounds are proved below.

Use the sharper floor loss from (17), keeping A's orientation. Let
alpha>=beta>=0 be A's absolute side-axis components, h_A=(alpha+beta)/2,
j_A=(alpha-beta)/2. Define delta_A=0 for c<=0, and for c>0 put
\[
 \delta_A=\max\left\{0,
       \frac c s(j_M+j_A+d)-\frac{87}{50}(h_M-1/2)\right\}.
                                                               \tag{24}
\]
Then y_A-h_A>=3/8-delta_A. Equations (16)--(19) give
\[
 \delta_A\le\frac{32}{25}\max(c,0)<\frac{16}{175},
\]
and, for c>0,
\[
 \delta_A< c\left(\frac{644}{405}-\frac{4611}{5500}
                                     +\frac{28}{27}j_A\right).
                                                               \tag{25}
\]
The latter uses j_M<=1/2, d<31/30, and 1/s<28/27. The maximum
with zero in (24) causes no issue because the displayed coefficient
is positive. For c<=0 the needed nonnegative upper bounds hold directly.

Repeating (21)--(22) with delta_A gives the transfer
\[
\begin{aligned}
 &a(-x_M-h_M)+b(1-x_B-h_B)\\
 &\qquad\le T-bE_B(z)-b\widetilde\Psi_A(z)
                              -bz(r-h_B-y_B),
\end{aligned}
\]
\[
           \widetilde\Psi_A(z)=\Psi_A(z)+\Gamma(c)/b-z\delta_A.
                                                               \tag{26}
\]
We prove, for every z>0,
\[
 \boxed{\widetilde\Psi_A(z)>\frac1{10}\min(z,1),
        \qquad\widetilde\Psi_A(z)>(21/10-r)z.}         \tag{27}
\]
At z=0 the same reserve is nonnegative. These are exactly the
two bounds used by the all-upward and mixed-sign paired proofs.

### 6.1. The previously covered slopes and a useful payment identity

Put z_0=7/5 and lambda=21/10-r>0. For 0<=z<=z_0, (23) gives
Gamma/b>=z delta_A, hence tilde-Psi>=Psi. The strengthened 81/100
reserve and its finite-range estimate in
`SHARED_CENTRAL_ORIENTATION_AND_ALL_MIXED_SHOULDER_SIGNS_HAND_PROOF.md`
give both inequalities in (27), strictly for z>0. We will also use
\[
                         \Gamma/b\ge z_0\delta_A.     \tag{28}
\]

### 6.2. Both chirality-independent support branches

For every z>=1, both physical chiralities obey
\[
              H_A((1,z))\ge\max(h_A+j_Az,-j_A+h_Az).
                                                               \tag{29}
\]
For one chirality this is the exact support formula. For the other,
the support is at least j_A+h_Az, which exceeds both displayed
terms when z>=1. The two terms in (29) cross at z=alpha/beta,
with the evident interpretation if beta=0.

Combining (26),(29),
\[
 \widetilde\Psi_A(z)\ge D_A+\Gamma/b+
  \max\{z(\alpha-\kappa-\delta_A),
               -\alpha+z(\alpha+\beta-\kappa-\delta_A)\}.
                                                               \tag{30}
\]
This maximum is essential: retaining only its first term would lose
the steep-slope gain for an A with orientation near a diagonal.

### 6.3. Larger alpha: the first branch suffices

Suppose alpha/beta>=7/5, including beta=0. Then
\[
               \alpha\ge7/\sqrt{74}>13/16,
\]
where the strict comparison has squared reserve 49*256-169*74=38.
We claim
\[
                         \alpha-29/40-\delta_A>0.     \tag{31}
\]
If alpha<=5/6, then beta>=sqrt(11)/6>1/2 and j_A<1/6.
The coefficient in (25) is less than
\[
                      \frac{238}{135}-\frac{4611}{5500}<1;
\]
the last comparison is 566500<622485. Hence delta_A<1/14,
whereas alpha-29/40>13/16-29/40=7/80>1/14.
If alpha>=5/6, use instead
\[
 \alpha-29/40-\delta_A>
                     \frac{13}{120}-\frac{16}{175}
                      =\frac{71}{4200}>0.
\]
This proves (31), also when c<=0 and delta_A=0.

Because kappa+lambda=29/40, (31) makes the first slope in (30)
strictly larger than lambda. It already proves the second inequality
in (27) for all z>=z_0. For the first, this slope is positive, so
(28) gives
\[
\begin{aligned}
 \widetilde\Psi_A(z)
 &\ge D_A+\Gamma/b+z_0(\alpha-\kappa-\delta_A)\\
 &\ge z_0(\alpha-\kappa)
 >\frac75\left(\frac{13}{16}-\frac{45}{64}\right)
 =\frac{49}{320}>\frac1{10}.
\end{aligned}
\]

### 6.4. Smaller alpha: the second branch supplies the missing slope

Suppose alpha/beta<=7/5. For every z>=z_0, the second term in
(30) is at least its first, since their difference is -alpha+z beta.
Its slope is strictly larger than lambda:
\[
 \alpha+\beta-\kappa-\delta_A-\lambda
 \ge1-29/40-\delta_A>
              \frac{11}{40}-\frac{16}{175}
               =\frac{257}{1400}>0.                  \tag{32}
\]
At z=z_0, use (28) and the fact that this second term is at least
the first to lower-bound (30) by D_A+z_0(alpha-kappa). Since
alpha>=1/sqrt(2)>kappa, this is at least D_A+alpha-kappa.
The proved 81/100 shoulder estimate, evaluated at z=1, gives
\[
                         D_A+\alpha\ge81/100.
\]
Here H_A((1,1))=alpha for either chirality, so this is the exact
z=1 instance of that reserve. The anchor bound is consequently
81/100-kappa, which exceeds 1/10. It also exceeds lambda z_0:
\[
 (81/100-\kappa)-(7/5)(21/10-r)
                         =\frac25r-\frac{151}{200}
                         >\frac9{200}>0,
\]
using r>2. By (32), both strict inequalities persist for all z>=z_0.
This completes (27) in the second orientation range, and hence globally.

## 7. Full all-slope owner-branch conclusion and the remaining owner gap

The all-upward paired terminal now permits, on either side, any
upward nearvertical separator owned by that outer main, with **every
upward slope** from shoulder to central square and no ownership
assumption on that second separator. Its transfer is (26), and the
first bound (27) pays the universal shared-central-orientation loss.
The four-chain span then excludes every R_0<r.

For a mixed-sign terminal, the second bound (27) pays the full
shared-height deficit. When this endpoint-owned transfer is used,
no central-band argument is needed merely to bound the upward slope.
The central-floor and opposite downward-transfer premises remain
explicitly necessary.

At radius r, nonvertical endpoint normals give strictness already
in (8), and positive shoulder-to-central slopes give strict reserve
in the paired argument. Equality in this owner class therefore routes
back to vertical matched endpoint separators and an actual horizontal
three-chain.

The still-uncovered endpoint-pair domains include a separator owned
only by the shoulder, a nearly horizontal separator owned by the
endpoint, and a downward transfer whose endpoint pair is oblique.
No transfer into those domains or into the global weak-chain caller
is asserted by this theorem.
