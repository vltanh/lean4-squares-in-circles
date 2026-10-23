# Intermediate frame order before either intermediate sign is fixed

## 1. Statement and original scope

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad R_1=\sqrt{Q-1},
 \quad \lambda=\frac1{R_1},\quad S_0=2R_1-3,
 \quad h_0=\frac7{10},\quad p=\frac{50}{49}.
\tag{1}
\]
Retain the G0--G2 necessary system, its actual sorted circles,
true central exclusion, and real frame interval of length at
most \(h_0\). H,A have nonnegative signed tangents, B,D,E
have nonpositive signed tangents. The signed G and T tangents
\(y_G,y_T\) are arbitrary. Retain
\[
 HG,AB,TD\in\{0,2\},\qquad GA=0,\quad BT=2,
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
For a necessary system apart from an original candidate, retain
also the original zero-owner sign implications
\[
                  HG2\Longrightarrow y_G<0,
        \qquad TD0\Longrightarrow y_T>0.
\tag{3}
\]
They are already global theorems for original G0--G2 candidates.

**Theorem.** Every such system satisfies
\[
                              \theta_G>\theta_T.
\tag{4}
\]
No G/T sign, AB alignment, outer-error sign, or original frame
order is an input. This strengthens
[the normal-sign intermediate-order theorem](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md).
It retains the hard GA0/BT2 owners. It does not yet align AB
or remove the intermediate-sign hypotheses from the later
arbitrary-frame sharp theorem.

The new ingredient is an estimate for the original middle path
which uses only one fixed positive weighted sum. If
\(r=\theta_T-\theta_G\ge0\), then
\[
                         -y_G+y_T\le S_0+\frac34r.
\tag{5}
\]
The signed quantity in (5) is intentional: neither tangent has
been replaced by its positive part or magnitude.

## 2. A fixed stress on the actual middle constraints

First take the actual AB0 witness. Normalize \(\theta_G=0\),
and set
\[
 x=\theta_A-\theta_G,\quad s=\theta_T-\theta_A,
 \quad d=\theta_B-\theta_A,\quad w=\theta_B-\theta_T.
\tag{6}
\]
Then
\[
 x+s=r\ge0,\qquad d-w=s,
 \qquad |x|,|s|,|d|,|w|\le h_0.
\tag{7}
\]
Write \(g=-y_G\), \(t=y_T\). With the actual positive A
and negative B magnitudes, the three constraints are exactly
\[
\begin{aligned}
 a_A\cos x+b_A\sin x-g&\ge W(x),\\
 b_A+a_B\sin d+b_B\cos d&\ge W(d),\\
 a_B\cos w-b_B\sin w-t&\ge W(w),
\end{aligned}
\qquad W(z)=\frac{1+\cos z+|\sin z|}{2}.
\tag{8}
\]
Add them with weights \(1,\lambda,1\). The collected A/B
forces have norms
\[
 N(x)=\sqrt{1+\lambda^2+2\lambda\sin x},\qquad N(s).
\tag{9}
\]
Apply Cauchy once to each actual shifted corner. The exact
necessary upper bound is
\[
\begin{aligned}
 g+t\le{}&R\{N(x)+N(s)\}-1-\cos x-\cos w\\
 &-(\sin x)_+-(-\sin w)_+
                -\lambda\{1+\cos d+(\sin d)_+\}.
\end{aligned}
\tag{10}
\]
No G or T coordinate circle, sign, or core assumption is used
in this middle-path calculation. Their actual signed tangents
occur only through \(g+t\).

The square-root tangent and \(R\lambda/\sqrt{1+\lambda^2}=1\)
give
\[
 R\{N(x)+N(s)\}\le2R\sqrt{1+\lambda^2}+\sin x+\sin s.
\tag{11}
\]
The zero-angle constant in (10) is exactly \(S_0\).
Put \(C(z)=1-\cos z\), and define
\[
 K_s(d)=\cos(d-s)+(-\sin(d-s))_+
                    +\lambda\{\cos d+(\sin d)_+\}.
\tag{12}
\]
Equations (10)--(11) therefore imply
\[
 g+t-S_0\le C(x)+\min(\sin x,0)+\sin s
                                      +1+\lambda-K_s(d).
\tag{13}
\]

We will use only the following rational whole-interval bounds:
\[
 \frac7{12}<\lambda<\frac35,\qquad
 \cos(h_0/2)>\frac{15}{16},\qquad
 \sin(h_0/2)<\frac{343}{1000},\qquad
 \sin h_0<\frac{13}{20},\quad \cos h_0>\sin h_0.
\tag{14}
\]
The lambda square reserves are \(2839/360000\) and
\(3101/62500\). The half-angle bounds follow from the
degree-two lower cosine and degree-five upper sine. The
last two inequalities follow from the degree-six lower
cosine and degree-five upper sine at \(7/10\).
In particular
\[
                 \tan(h_0/2)<\frac7{19}
                    <\frac{\lambda}{1+\lambda}.
\tag{15}
\]
Indeed \(7(15/16)-19(343/1000)=91/2000>0\).

## 3. The sector with A at or below T

Assume \(s\ge0\). We first prove, for every admissible d,
\[
                         K_s(d)\ge1+\lambda(\cos s+\sin s).
\tag{16}
\]
If \(0\le d\le s\), the expression in (12) is
\[
 \cos(s-d)+\sin(s-d)+\lambda(\cos d+\sin d).
\]
Its second derivative is its negative, so it is concave.
Its minimum is at one of the two endpoints; the smaller
endpoint is d=s because \(\lambda<1\) and
\(\cos s+\sin s\ge1\).

If \(d=-v\le0\), then \(s+v\le h_0\) and
\[
 K_s(-v)-K_s(0)
 =2\sin(v/2)\{\cos(s+v/2)-\sin(s+v/2)-\lambda\sin(v/2)\}\ge0.
\tag{17}
\]
To see the bracket sign, put \(u=v/2\), replace
\(s+u\) by its upper bound \(h_0-u\), and expand. The
result is
\[
 (\cos h_0-\sin h_0)\cos u
            +(\sin h_0+\cos h_0-\lambda)\sin u>0.
\]
Both coefficients are positive by (14).

If \(d=s+v\ge s\), then \(s+v\le h_0\) and
\[
 K_s(s+v)-K_s(s)
 =2\sin(v/2)\{\lambda[\cos(s+v/2)-\sin(s+v/2)]-\sin(v/2)\}\ge0.
\tag{18}
\]
For the bracket, again replace \(s+u\) by \(h_0-u\).
The resulting function is
\[
 \lambda(\cos h_0-\sin h_0)\cos u
       +\{\lambda(\sin h_0+\cos h_0)-1\}\sin u.
\]
Its first coefficient is positive and its second negative:
\(\lambda<3/5\) and \(\sin h_0+\cos h_0<3/2\).
It decreases for \(0\le u\le h_0/2\). At the right endpoint
it exceeds
\[
 \frac7{12}\left(\frac{15}{16}-\frac{343}{1000}\right)
                       -\frac{343}{1000}=\frac{91}{24000}>0.
\tag{19}
\]
This proves (16) in all three geometric sectors.

Substituting (16) into (13) yields
\[
 g+t-S_0\le C(x)+\min(\sin x,0)
                          +(1-\lambda)\sin s+\lambda C(s).
\tag{20}
\]
If \(x\ge0\), then \(x+s=r\) and
\(C(z)\le z^2/2\le(7/20)z\) for nonnegative z. Thus
\[
 (20)\le\frac7{20}x+
              \left(1-\frac{13}{20}\lambda\right)s
       \le\frac{149}{240}(x+s)<\frac34r
\tag{21}
\]
when r>0; the weak bound holds at r=0.

If \(x=-v<0\), then \(s=v+r\). At r=0, the right side
of (20) is
\[
                       (1+\lambda)C(v)-\lambda\sin v\le0
\]
by (15). Its derivative as r increases is
\[
             (1-\lambda)\cos(v+r)+\lambda\sin(v+r)<\frac34.
\tag{22}
\]
Indeed its square is at most
\((1-\lambda)^2+\lambda^2\le13/25<9/16\), using
\(1/2<\lambda<3/5\). The reserve is \(17/400\).
Integrating (22) proves (5) also when x<0.

## 4. The sector with A above T

Now let \(s=-v<0\). Then \(x=v+r>0\). We claim
\[
                     K_{-v}(d)\ge2+\lambda-\cos v-\sin v.
\tag{23}
\]
If \(-v\le d\le0\), then
\(K_{-v}(d)=\cos(d+v)+\lambda\cos d\). Concavity shows
its minimum is at an endpoint; the smaller is
\(\cos v+\lambda\). This is greater than the right side
of (23), since
\[
                         \sin v-2(1-\cos v)>0
\tag{24}
\]
by \(2\tan(v/2)<14/19<1\).

If \(d=-v-u\le-v\), then \(u+v\le h_0\), and
\[
\begin{aligned}
 K_{-v}(-v-u)-K_{-v}(-v)
 =2\sin(u/2)\{\cos(u/2)-\sin(u/2)-\lambda\sin(v+u/2)\}\ge0.
\end{aligned}
\tag{25}
\]
The bracket exceeds
\[
                \frac{15}{16}-\frac{343}{1000}
                     -\frac35\frac{13}{20}=\frac{409}{2000}>0.
\]
Thus this sector also reduces to the preceding endpoints.

If \(d\ge0\), then \(0\le d\le h_0-v\) and
\[
 K_{-v}(d)=\cos(v+d)+\lambda(\cos d+\sin d).
\tag{26}
\]
This positive function is concave in d. Its endpoint at
d=0 has already been handled. At \(d=h_0-v\), subtract
the right side of (23) to obtain
\[
 D(v)=\cos h_0+\lambda\{\cos(h_0-v)+\sin(h_0-v)\}
                    -2-\lambda+\cos v+\sin v.
\tag{27}
\]
The function D is concave on \([0,h_0]\), so its minimum
is at an endpoint. Both endpoints are positive. Explicitly,
the degree-six lower cosine \(C_6\) and degree-seven lower
sine \(S_7\) give
\[
\begin{aligned}
 D(0)&>(19/12)C_6(h_0)+(7/12)S_7(h_0)-19/12
                  =\frac{298782547}{86400000000}>0,\\
 D(h_0)&\ge2C_6(h_0)+S_7(h_0)-2
                  =\frac{417357857}{2400000000}>0.
\end{aligned}
\tag{28}
\]
Here \(D(0)\) increases with lambda because
\(\cos h_0+\sin h_0>1\), so \(\lambda>7/12\) is
legitimate in its displayed lower bound. This proves (23).

Insert (23) into (13). Since x>0 and \(s=-v\),
\[
                    g+t-S_0\le C(v+r)-C(v)
                         \le\frac{13}{20}r<\frac34r
\tag{29}
\]
for r>0, with the weak conclusion at zero. The derivative
of C is sine, bounded by (14) throughout this interval.
This proves (5) for every AB0 geometry.

For AB2, apply local reflected reversal: exchange A with B
and G with T, reverse the frame direction, and negate the
signed tangents. The new AB owner is zero; the two hard
owners retain their displayed roles, r is unchanged, and
the new signed sum is again \(-y_G+y_T\). Thus (5) holds
for either actual AB witness, including all weak ties.

## 5. The unclipped outer charges retain the signed sum

Put
\[
 h=\theta_G-\theta_H,\quad k=\theta_D-\theta_T,
                 \quad \alpha=\theta_H-\theta_D.
\tag{30}
\]
Section 2 of
[the global primary-GA outer-target theorem](HAND_G3_GLOBAL_PRIMARY_GA_TARGET_IS_OUTER.md)
proves, with either sign of the actual G tangent,
\[
                         b_H-y_G\ge1-ph.
\tag{31}
\]
For \(y_G\le0\) it is the all-sign zero-edge charge
with its nonnegative remainder discarded. For \(y_G>0\),
(3) leaves HG0, which forces h>0. Its actual G-circle
support gives the same signed charge; the whole-interval
concavity comparison is proved in that cited section.

Reflected reversal of TD gives the matching inequality
\[
                         y_T+b_D\ge1-pk.
\tag{32}
\]
The role of (3) is explicit: a wrong T sign leaves TD2,
which becomes HG0 after reversal. The signed transverse
quantity at the reflected intermediate is \(-y_T\).

Suppose now \(r=\theta_T-\theta_G\ge0\). Add
(31)--(32), use (5), and note \(h+k=-\alpha-r\).
Since \(p-3/4=53/196>0\), this gives
\[
             2\le b_H+b_D+S_0-p\alpha-(p-3/4)r
                   \le b_H+b_D+S_0-p\alpha.
\tag{33}
\]
The all-mixed endpoint theorem in Sections 2--5 of
[the existing global-order note](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md)
uses only H,D,E, their actual circles, true core, normal
signs, frame span, and actual DE/EH inequalities. It proves
\[
                         b_H+b_D+S_0-p\alpha<2
\tag{34}
\]
for all four mixed-owner pairs in (2). It has no G/T sign
input. Equations (33)--(34) contradict each other and prove
(4).

The proof retains every original state and witness. Its
only geometric cases are the relative orders of A, B and T
in one fixed three-edge inequality. Each entire continuous
sector is handled by concavity or a monotone derivative.
No moved state, angle mesh, state enumeration, numerical
acceptance premise, Lean compilation, or CI result is used.
