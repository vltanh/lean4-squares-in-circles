# One central orientation: all signs and slopes for matched shoulders

November 1, 2026 (America/Chicago; November 2 UTC). Reconstructed hand
proof and a strengthened mixed-sign domain. No mathematical program,
orientation sampling, Lean, Lake, or CI is used. This is a conditional
seven-square terminal, not an unrestricted nine-square extraction.

The two transfer lemmas used below are fully written in
`DOWNWARD_THREE_SQUARE_CAP_FLOOR_ONE_TENTH_HAND_PROOF.md` and
`UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md`. The present proof retains
their discarded orientation and height reserves. No unpublished routing
or inner-main-height claim is used.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 \mu=\frac{k}{b}=\frac{23}{24},\quad T=\frac{211}{4}.
\]
For a physical unit square S, let H_S(v) be its support halfwidth in
vector direction v, and write h_S=H_S(e_x)=H_S(e_y).

## 1. Precisely what is proved

Let four physical units form an actual horizontal projection chain
\[
                 M_0<_xM_1<_xM_2<_xM_3.                 \tag{1}
\]
Let L,C,R be three other units. All seven are interior-disjoint and
contained in a common disk centered at zero. Assume the two actual
vertical projection comparisons
\[
 y_L-y_0\ge h_L+h_0,\qquad y_R-y_3\ge h_R+h_3.         \tag{2}
\]
In the statements requiring a central floor, assume
\[
                       y_C-h_C\ge\frac1{10}.          \tag{3}
\]
The conclusions below are that the containing squared radius is at
least Q, and at radius r every stated positive separating slope is
impossible. At zero slopes the actual horizontal chain L<_xC<_xR
is supplied, so the already-proved physical 4+3 terminal applies.

The physical separator from C toward L has normal (-1,eta_L s), and
that from C toward R has normal (1,eta_R t), in unnormalized form,
where s,t>=0 and each eta is +1 or -1. Thus, for example,
\[
 (-1,\eta_Ls)\cdot(c_L-c_C)
   \ge H_L((-1,\eta_Ls))+H_C((-1,\eta_Ls)).             \tag{4}
\]
The right separator is defined identically. These must be true
physical separating inequalities; no normal ownership is assumed.

| Sign pair | Additional premises sufficient for the terminal |
|---|---|
| (+,+) | Central whole floor at least 7/60; no slope bound. Alternatively, floor (3) and s+t<=min(sqrt(1+s^2),sqrt(1+t^2)) suffice |
| (-,-) | No slope bound and no central-floor premise needed |
| (+,-) or (-,+) | Central floor (3), central strip \(\lvert x_C\rvert<29/60\); no slope bound |

In every row (2) is an actual-projection hypothesis. Replacing (2) by
arbitrary physical disjointness is not justified by this proof.

The unrestricted (+,+) slope row uses the independently reconstructed
`DOWNWARD_TRANSFER_WITH_CENTRAL_CENTER_COST_HAND_PROOF.md`. That theorem
proves the stronger single transfer
\[
             a(-x_M-h_M)+b(1/2-x_C)\le T
\]
under a central whole floor 7/60, strictly at subcritical radius or a
positive downward-transfer slope. Adding its left and right reflected
forms and using the actual-four span immediately proves the (+,+) row.
Sections 2--4 below retain the older floor-1/10, bounded-slope alternative.

Consequently, if (2) holds, the central unit is in |x_C|<29/60 and has
whole floor at least 7/60, **every choice of the two signed shoulder
separators and every finite slope are covered**. The actual endpoints
and the one physical central unit are retained throughout.

## 2. The joint orientation inequality

For s,t>=0 put S=s+t. If
\[
             S\le\min\{\sqrt{1+s^2},\sqrt{1+t^2}\},  \tag{5}
\]
then every physical unit square C satisfies
\[
       S h_C+H_C((-1,s))+H_C((1,t))\ge1+S.             \tag{6}
\]
The two supports use the same orientation of C.

Consider the triangle with vertices (0,0),(1,t),(0,S). Its edge
vectors are (1,t),(-1,s),(0,-S). In either coordinate of C's side
frame, half the sum of the absolute edge projections is the range
of the three vertex projections. The left side of (6) is therefore
the sum of the two side lengths of its bounding rectangle in that frame.

Between changes of a projected extreme vertex this positive side sum
has the form A cos(theta)+B sin(theta), whose second derivative is its
negative. It is concave there. A minimum occurs when some triangle
edge is parallel to a frame axis. The three candidates are
\[
       1+S,\qquad L_s+S/L_s,\qquad L_t+S/L_t,
       \quad L_z=\sqrt{1+z^2}.                        \tag{7}
\]
To check the sloping-edge candidates, the third vertex projects inside
the other two longitudinal extremes exactly when st<=1. Condition (5)
implies max(s,t)^2+2st<=1 and hence st<=1. The transverse range is
S/L_z, so (7) follows. Since L_z>=1 and L_z>=S,
\[
        L_z+S/L_z-(1+S)=(L_z-1)(L_z-S)/L_z\ge0.
\]
This proves (6). The zero-slope degeneration is the elementary
inequality 2h_C>=1. In particular S<=1 is sufficient for (5); equal
slopes up to 1/sqrt(3) are also allowed.

## 3. Retained transfer terms and the four-chain span

It suffices to consider a containing radius R_0<=r. The established
actual-four endpoint budget gives |y_0|,|y_3|<=1/8. By (2), each
shoulder is wholly above y=3/8.

Write Y=y_C and h=h_C, and set
\[
 A_L=a(-x_0-h_0)+b(1-x_C-h),\qquad
 A_R=a(x_3-h_3)+b(1+x_C-h).                            \tag{8}
\]
For a downward transfer from a shoulder toward C with slope z, retain
the central support penalty and the excess of its floor above 1/10
in the downward proof. This gives
\[
 A_i\le T-bE_i(z)-bz(Y-h-1/10),                        \tag{9}
\]
where E_i(z)=H_C(v_i(z))+(1+z)h-(1+z), and v_i(z) is the
corresponding unnormalized separator from that shoulder toward C.
Every such E_i is nonnegative: the contained aligned square of
halfwidth g=1/(4h) gives H_C(v_i)>=g(1+z), while h+g>=1.
The positive scalar reserve from the downward proof has been discarded.
Inequality (9) is strict if R_0<r or if z>0.

For an upward transfer retain the central support excess and the top
slack r-h-Y in the upward proof. Its inequality is
\[
 A_i\le T-\Delta_{M,i}-bE_i(z)-b\Psi_i(z)-bz(r-h-Y),   \tag{10}
\]
where Delta_{M,i}>=0 is the outer main's matched-cap reserve. For
the relevant reflected shoulder A,
\[
 \Psi_A(z)=H_A((1,z))-h_A+z(h_A-\kappa)+D_A,
 \quad \kappa=r-11/8,
\]
\[
 D_A=(1+\mu)h_A+H_A((-1,\mu))-(1+\mu)\ge0.          \tag{11}
\]
The upward proof establishes Psi_A(z)>0 for z>0, and Psi_A(0)=D_A>=0.
The top-slack term in (10) follows by retaining it in
\[
 Y-y_A\le r-h-h_A-3/8-(r-h-Y).
\]
The cap step in (10) is strict when R_0<r.

The actual chain (1) supplies
\[
              D=x_3-x_0-h_0-h_3\ge2.                  \tag{12}
\]
If we prove that the total normalized reserve in (9)--(10) is at
least 2h-1, then their sum gives
\[
 A_L+A_R\le2T-b(2h-1),\quad
 aD+b\le2T=2a+b.                                     \tag{13}
\]
Strict subcritical containment contradicts (12)--(13).

## 4. The two equal-sign cases

For either equal-sign pair the two central excesses have sum
\[
 (2+S)h+H_C((-1,s))+H_C((1,t))-(2+S),
\]
up to a reflection or interchange of s,t. Under (5), equation (6)
bounds this below by 2h-1. All retained height and main/shoulder
reserves are nonnegative. Therefore (13) follows in both cases.

For (+,+), both transfers are downward, and (3) makes the retained
floor slacks nonnegative. For (-,-), both are upward, so (3) is not
needed. At radius r a positive slope makes its individual transfer
strict, hence all separating slopes vanish at equality.

## 5. A quantitative upward-shoulder reserve

The next estimate pays for the orientation loss when the two central
supports point in the same direction, as happens with mixed signs.
Let alpha>=beta>=0 be the absolute side-axis components of a shoulder,
alpha^2+beta^2=1. Put h_A=(alpha+beta)/2, j_A=(alpha-beta)/2.
An outward-quadrant vertex gives
\[
 D_A\ge(1+\mu)(\alpha-1)+\mu\beta=:D_0.              \tag{14}
\]
We first prove the stronger reserve
\[
                  D_A\ge\frac\beta\alpha(81/100-\beta),\tag{15}
\]
strictly if beta>0. At beta=0 both sides are zero. For beta>0,
the difference between D_0 and the right side of (15) is
\[
 \frac\beta\alpha\left(\mu\alpha-\frac{81}{100}+
                 \frac{\beta(1-\mu\alpha)}{1+\alpha}\right).
\]
Put u=beta/(1+alpha), so alpha=(1-u^2)/(1+u^2) and
0<=u<=sqrt(2)-1<5/12. Multiplying the parentheses by 600(1+u^2)
gives exactly
\[
                         P(u)=89+25u-1061u^2+1175u^3.
\]
On [0,1/4], P''=-2122+7050u<0, and the endpoint values are
P(0)=89, P(1/4)=3027/64. On [1/4,5/12], P' is a convex quadratic
whose endpoint values are -4563/16 and -3955/16. Thus P'<0 there,
and P>=P(5/12)=367/1728>0. This proves (15).

Since r<133/64, kappa<45/64<1/sqrt(2). For every z>=0,
\[
 \Psi_A(z)\ge(81/100-\kappa)\min(z,1)
                  >\frac1{10}\min(z,1)\quad(z>0).    \tag{16}
\]
For 0<=z<=1, the two possible square chiralities both give
\[
 H_A((1,z))\ge\max(h_A-j_Az,j_A+h_Az).
\]
The two expressions cross at z_0=beta/alpha. On [0,z_0], (15)
gives Psi_A>=D_A+z(beta-kappa)>=z(81/100-kappa). On [z_0,1],
the lower bound D_A-beta+z(2h_A-kappa) agrees at z_0 and has
slope at least 1-kappa>81/100-kappa. For z>=1 the outward-quadrant
vertex instead gives
\[
                  \Psi_A(z)\ge D_A+z(\alpha-\kappa).
\]
This is increasing and at z=1 is the preceding lower bound. Hence
(16) holds for every orientation and every slope. Its final strict
comparison uses 81/100-45/64=171/1600>1/10.

For the present theorem we need the stronger finite-range estimate
\[
       \boxed{\Psi_A(z)>(21/10-r)z\quad(0<z\le11/2).} \tag{17}
\]
For 0<z<=1 this follows from (16), because
(81/100-kappa)-(21/10-r)=17/200>0. For 1<=z<=11/2, note that
\[
 D_0+\frac{11}{2}(\alpha-29/40)
       =\frac{179\alpha+23\sqrt{1-\alpha^2}-1427/10}{24}>0.
                                                               \tag{18}
\]
The right side is concave on [1/sqrt(2),1], and its two endpoint
values are positive. At alpha=1 it is 121/80. At alpha=1/sqrt(2)
its numerator is 101sqrt(2)-1427/10>0, because
\[
                    2\cdot1010^2-1427^2=3871>0.
\]
Since D_A>=D_0 and D_A>=0, the convex combination with weights
1-2z/11 and 2z/11 gives D_A+z(alpha-29/40)>0 throughout the
claimed finite range. Finally kappa+(21/10-r)=29/40, so the
preceding outward-vertex bound proves (17).

## 6. A universal joint-orientation bound and all upward slopes

For every s,t>=0, with no slope-domain restriction, we have
\[
\begin{aligned}
 &(s+t)h+H_C((-1,s))+H_C((1,t))\\
 &\qquad\ge1+s+t-\frac1{10}\bigl(\min(s,1)+\min(t,1)\bigr).
                                                               \tag{24}
\end{aligned}
\]
Here is a direct proof covering arbitrarily steep slopes and both
chiralities. Write alpha>=beta>=0 for C's absolute side-axis components,
h=(alpha+beta)/2, j=(alpha-beta)/2. If beta=0, the left side is exactly
1+s+t. Otherwise, after possibly interchanging s,t, the two supports are
\[
 H_-(z)=\max(h-jz,j+hz),\qquad
 H_+(z)=\max(h+jz,-j+hz).
\]
Put c=1/10. Subtract 1+s+t from the left side of (24) and add its
proposed loss. It suffices to show
\[
 F_-(s)+F_+(t)\ge1,\quad
 F_\pm(z)=z(h-1)+H_\pm(z)+c\min(z,1).
\]
These are piecewise linear. The kink of H_- is beta/alpha<=1; its
slopes below and above that kink force
\[
 \min_{z\ge0}F_-(z)=h+(\beta/\alpha)(\beta-1+c).
\]
Indeed the first slope is beta-1+c<0, the next is 2h-1+c>0, and
beyond one it is 2h-1>=0. The kink of H_+ is alpha/beta>=1, and
the only possible global minima of F_+ are at zero or this kink:
\[
 \min_{z\ge0}F_+(z)=\min\{h,h+c+(\alpha/\beta)(\alpha-1)\}.
\]
On the interval from one to alpha/beta the slope is alpha-1<=0;
beyond the latter it is 2h-1>=0. This also covers either sign of
the first slope alpha-1+c.

Adding the first candidate h gives at least one, since the excess is
\[
             \frac{(1-\alpha)(1-\beta)+c\beta}{\alpha}\ge0.
\]
For the other candidate, put p=alpha+beta. Multiplication by alpha beta
shows that its excess over one is nonnegative exactly when
\[
                         5(p-1)^2\le\beta p.          \tag{25}
\]
With u=beta/(1+alpha) this becomes, after dividing by the positive
factor 2u/(1+u^2)^2,
\[
                         1-8u+19u^2-10u^3\ge0.
\]
Set v=u-1/4. The left side is
\[
              \frac1{32}-\frac38v+\frac{23}{2}v^2-10v^3.
\]
For -1/4<=v<=0 every nonconstant displayed term is nonnegative.
For 0<=v<=1/6, the expression is at least
1/32-(3/8)v+9v^2>=7/256>0. This covers the full allowed interval
u<=sqrt(2)-1<5/12, proves (25), and completes (24).

In the (-,-) case both transfers are upward. Formula (24) says their
central excesses have sum at least
\[
 (2h-1)-\frac1{10}\bigl(\min(s,1)+\min(t,1)\bigr).
\]
The two shoulder reserves (16) pay the entire loss, strictly if either
slope is positive. All remaining terms in (10) are nonnegative.
Thus (13) holds for **every pair of upward-transfer slopes**, with
no central-floor or central-strip premise. This removes the restriction
(5) from the (-,-) row of the statement table.

## 7. Mixed signs use one central height as well as one orientation

By horizontal reflection it is enough to take the normals from C
toward the shoulders to be (-1,s) and (1,-t), with s,t>=0.
The left transfer is downward, and the right is upward. In both
transfers the central support is H_C((1,-z)), by central symmetry
and reflection. Define
\[
                  E(z)=H_C((1,-z))+(1+z)h-(1+z)\ge0.
\]
Put j=sqrt(1/2-h^2), alpha_C=h+j, beta_C=h-j; alpha_C<=1.
A rightmost vertex has offset (h,+j) or (h,-j), so
\[
            E(z)\ge(2h-1)-z(1-\beta_C).               \tag{19}
\]
Let m=min(s,t). The central floor and disk containment imply
Y-h-1/10>=0 and r-h-Y>=0. Consequently
\[
 s(Y-h-1/10)+t(r-h-Y)\ge m(r-2h-1/10).                \tag{20}
\]
Use (19) on the smaller slope and E>=0 on the other. Adding (20),
and using 2h-beta_C=alpha_C<=1, gives
\[
\begin{aligned}
 E(s)+E(t)&+s(Y-h-1/10)+t(r-h-Y)\\
 &\ge(2h-1)+m(r-11/10-\alpha_C)\\
 &\ge(2h-1)-m(21/10-r).                              \tag{21}
\end{aligned}
\]
If 0<t<=11/2, (17) is strictly greater than the possible deficit
in (21), because t>=m and 21/10-r>0. If t=0, then m=0 and
Psi_R(0)>=0. Thus in every case with t<=11/2 the normalized
reserves in (9)--(10) total at least 2h-1. Equation (13) proves
the lower bound. At radius r, t>0 makes the combined reserve
strict; if t=0 and s>0, the downward transfer is strict. Hence
both slopes vanish at equality.

This part in fact proves a conditional mixed-sign terminal whenever
the upward-transfer slope is at most 11/2, with no upper bound on
the downward-transfer slope.

## 8. The central strip removes the mixed-slope restriction

Assume |x_C|<29/60. The proved actual-four outsider-strip theorem
gives |x_R|<13/12 and hence, in the reflected right-transfer frame,
\[
                     d=x_R-x_C<\frac{47}{30}.          \tag{22}
\]
By (2) and the endpoint budget, y_R>=h_R+3/8. Circle containment
gives Y<=r-h. Therefore
\[
                    Y-y_R\le r-3/8-h-h_R\le\kappa.
\]
Each physical square contains a disk of radius 1/2, so a true
separating normal (1,t) in this reflected frame requires
\[
                   \sqrt{1+t^2}\le d+t(Y-y_R)
                                   <47/30+\kappa t.  \tag{23}
\]
If t>=11/2, then kappa<45/64 and
\[
             47/30<209/128=(19/64)(11/2)\le(19/64)t
\]
make the right side of (23) less than t, a contradiction. Thus
t<11/2 automatically. Section 7 applies to every mixed-sign
separating choice, without an angle or normal-owner restriction.

Horizontal reflection proves the opposite mixed-sign assignment.
Together with Sections 4 and 6 this proves all rows in the statement table.

## 9. Exact scope of the remaining gap

The mixed-sign result no longer needs the previously proposed
stronger central band |x_C|<17/60 or any unproved route to that band.
It covers the whole existing central occupancy band |x_C|<29/60.
No claim that a packing supplies (2) or (3) is made here. The
oblique shoulder-to-outer-main pairs in place of (2), and the global
weak-chain caller remain open. The new floor-7/60 downward-center theorem
does cover the same-sign downward slopes outside (5); at the weaker
floor1/10 those extra downward slopes are not asserted covered.
No canonical root exclusion count or global gate is changed by
this conditional theorem alone.
