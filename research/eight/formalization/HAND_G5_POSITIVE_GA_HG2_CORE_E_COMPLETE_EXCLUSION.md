# Positive GA1 with HG2 excludes the complete core-E entry domain

## 1. Actual domain and theorem

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad
 R=\sqrt Q,\quad h=7/10,\quad K=13/12.
\tag{1}
\]
Fix one actual common ceiling \(q_L\le q\le Q\). Work in
the boundary-neighbor domain of the
[boundary bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md),
with its actual outer boundary taken at q. Every state is
sorted, is contained at q, and is on either that outer circle
or the true core. H,A are positive sorted outer states,
B,D are negative sorted outer states, and E has nonpositive
tangent and is on its true core. G and T may have either
signed tangent and either radial kind. In particular
\[
 (a_i+1/2)^2+(|y_i|+1/2)^2\le q\le Q,
 \qquad a_i\ge|y_i|,
\]
\[
                 0\le b_E=-y_E\le a_E\le7/12.
\tag{2}
\]
The actual captured errors are frame differences. Their sum
is zero; both their positive and negative variations are
less than h. All estimates below hold on the closed
enlargement with variations at most h.

Retain actual HG2 and GA1, with GA error
\(x=d_{GA}\ge0\). Retain either actual AB0 or actual AB2,
with arbitrary signed error, and either actual owner on
each E edge:
\[
                         DE2\text{ or }DE3,
                   \qquad EH0\text{ or }EH1.
\]
No sign is imposed on either E error or on their sum.
The following four T regimes are all excluded:
\[
\begin{array}{c|c|l}
BT&TD&\text{additional condition}\\ \hline
2&0&\text{both errors arbitrary}\\
2&2&\text{both errors arbitrary}\\
3&0&d_{BT}\ge0,\ d_{TD}\text{ arbitrary}\\
3&0&d_{BT}<0,\ d_{TD}=0.
\end{array}
\tag{3}
\]

**Theorem.** No necessary boundary-neighbor cycle satisfying
these hypotheses exists. The contradiction is strict at the
upper ceiling Q and includes all weak witness ties. The last
row really uses TD alignment; no local conversion of an
arbitrary sole BT3/TD0 triple is asserted.

The proof retains each actual AB, HG and remaining TD
rotation. Its only geometric preprocessing concerns a
negative core-E primary total and changes E alone at the
original q. All other steps are inequalities on the actual
states and angles. The coefficient and scalar companions are

- [the full signed angular envelope](HAND_G5_POSITIVE_GA_CORE_E_ANGULAR_ENVELOPE.md);
- [seven exact scalar certificates](HAND_G5_POSITIVE_GA_CORE_E_SCALAR_CERTIFICATES.md).

## 2. The actual weighted force at G and T

Write \(g=-y_G\), which is signed. With \(v=d_{HG}\),
the two retained projections are
\[
 a_H\sin v+b_H\cos v+g\ge W(v),\qquad
 a_A+a_G\sin x-g\cos x\ge W(x),
\quad W(t)=\frac{1+\cos t+|\sin t|}{2}.
\tag{4}
\]
Choose GA weight k and HG weight
\[
       k=.863,\qquad n=k(\cos x+\eta\sin x).
\tag{5}
\]
The G force is then exactly
\[
                 k\sin x(a_G+\eta g)
                 \le k\sigma_\eta\sin x,
 \qquad \sigma_\eta=R\sqrt{1+\eta^2}-(1+\eta)/2.
\tag{6}
\]
For either sign of g, (6) follows by replacing g with
\(|g|\) and applying the actual shifted-circle containment.

Give AB weight l and both E edges weight 1. For an outer
state with its normal nonnegative magnitudes (a,b), use
\[
 fa+gb\le\overline S(f,g)
       :=R\sqrt{f^2+g^2}-(f+g)/2.
\tag{7}
\]
This is a full-circle support inequality, valid for any
real force coefficients. Equality on the outer circle is
not required for its use.

For actual BT2 and TD0, equal weights c cancel the signed
T tangent. If TD2 has a nonnegative error z, give it weight
k and give BT2 weight \(m=k(\cos z+\eta\sin z)\). The T
force becomes
\(k\sin z(a_T-\eta y_T)\le k\sigma_\eta\sin z\).
If instead BT3 has nonnegative error z and TD0 is retained,
give BT3 weight k and TD0 weight m. Its T force is
\(k\sin z(a_T+\eta y_T)\le k\sigma_\eta\sin z\).
These inequalities also allow both T signs.

For the nonnegative T cases put \(d=x+z\), interpreting
z=0 when BT2 and TD0 are retained. Use family P:
\[
 l=.5052+.49d-.108d^2,\quad c=k,\quad
 \eta=.25+.1645d,\quad\lambda=1.03.
\tag{8}
\]
For a genuine negative T primary, put d=x and use family N:
\[
 l=.5054+.55d-.2d^2,\quad c=.863+.35d-.15d^2,
 \quad\eta=.38,\quad\lambda=.8888+.2d.
\tag{9}
\]
The positive variation gives \(d\le h\). Both families
satisfy \(l<.8<k\), and every tilted coefficient is at
least k. For (8), \(\eta\ge\tan(d/2)\) and therefore
\(\cos t+\eta\sin t\ge1\) for \(0\le t\le d\).
Indeed \(.25+.1645d-\tan(d/2)\) is concave in d and
positive at both 0 and h; the far endpoint is the exact
Taylor check recorded in the coefficient audit.
For (9), use \(.38>\tan(h/2)\). These are inequalities
on the whole intervals; the endpoint Taylor bounds and
all coefficient ranges are in the companions.

## 3. The exact base scalars and ordinary angular blocks

Put
\[
 C_\eta(t)=1+2\cos t+
                \{1+2\eta-R\sqrt{1+\eta^2}\}\sin t.
\tag{10}
\]
For BT2/TD0 the zero-rotation four-outer baseline is
\[
 \begin{split}
 B_N={}&3+2l+3c+kC_\eta(x)\\
 &-R\{\sqrt{1+n^2}+\sqrt{k^2+l^2}
                    +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
 \end{split}
\tag{11}
\]
Here the notation \(B_N\) is used with (9) when a negative
T primary is present; the same force identity is valid
with (8), c=k, and z=0.

For positive TD2 the corresponding baseline is
\[
 \begin{split}
 B_{PT}(x,z)={}&3+2l+kC_\eta(x)+kC_\eta(z)\\
 &-R\{\sqrt{1+n^2}+\sqrt{k^2+l^2}
                  +\sqrt{l^2+m^2}+\sqrt{1+k^2}\}.
 \end{split}
\tag{12}
\]
Its four ordinary pairs are
\[
                       H:(1,n),\ A:(k,l),\ B:(l,m),\ D:(1,k).
\tag{13}
\]
For positive BT3, move the second tilt from B to D:
the last two pairs are \((l,k),(1,m)\). The demand in
(12) is unchanged, and its support sum only decreases.
Indeed, for m≥k and l<1,
\[
 \sqrt{l^2+m^2}-\sqrt{l^2+k^2}
 \ge\sqrt{1+m^2}-\sqrt{1+k^2}.
\tag{14}
\]
Differentiate both sides with respect to m to verify (14).
Thus the positive-BT baseline is at least (12).

An actual ordinary rotation is assigned to its true outer
endpoint: HG2 to H, AB0 to B or AB2 to A, BT2 to B,
TD0 to D, DE2 to D and EH0 to H. A two-angle outer force
has norm
\(\sqrt{p^2+q^2+2pq\sin(u+v)}\). Its threshold and the
half-coordinate shifts give the trigonometric contribution
\(\psi(t)=\cos t+\max(\sin t,0)-1\).
Consequently the ordinary increment is bounded by the
actual signed blocks in the angular companion, with no
change of any actual frame.

For reference write its canonical negative block as
\[
 V_{l,k}(w)=k(\cos w-1)
      -R\{\sqrt{l^2+k^2-2lk\sin w}-\sqrt{l^2+k^2}\}.
\tag{15}
\]
The companion proves a uniform comparison for the varying
B coefficient, full concentration of both actual signs,
all same-block and separated saturation comparisons, and
the far endpoint estimate
\[
                         V_{\rm block}(h)>l-.0696.
\tag{16}
\]
These bounds are uniform in the split x+z=d. They also
cover the actual one-angle supports produced by the
negative secants used next.

## 4. A negative TD2 is secondary or flat with error below .3

Suppose BT2 is retained and TD2 has error \(-t<0\).
BT2 and sorted containment of B give
\[
 y_T\le a_B\cos d_{BT}+b_B\sin d_{BT}-W(d_{BT})
             \le\sqrt{a_B^2+b_B^2}-1\le a_0-1<.415,
\tag{17}
\]
where \(a_0=\sqrt{Q-1/4}-1/2<1.415\).
The actual TD2 inequality is
\[
                         b_D+y_T\cos t-a_T\sin t\ge W(t).
\tag{18}
\]
It forces \(y_T>0\) and \(b_D+y_T>1\), hence \(b_D>y_T\).

If T is outer at its actual q while D is contained there,
then \(a_T>a_D\) and
\[
 \frac{a_T-a_D}{b_D-y_T}
       \ge\frac{b_D+y_T+1}{a_T+a_D+1}
                     >\frac2{3.83}>\frac12>\tan(t/2).
\tag{19}
\]
The difference of the actual projections is
\[
             TD0-TD2=(a_T-a_D)\sin t-(b_D-y_T)(1-\cos t)>0.
\tag{20}
\]
Thus TD0 is already an actual weak witness at those same
states and frames, and this case returns to the first row
of (3).

Otherwise T is true core. Equation (17) places it on the
flat side \(a_T=7/12\). Since \(b_D<.9\), the margin in
(18) is less than
\[
                         .4-.085\cos t-K\sin t.
\tag{21}
\]
This decreases on [0,h] and is negative at t=.3, by
the rational Taylor check in the scalar companion. Hence
\(t<.3\).

Give TD2 weight \(c\sec t\) and BT2 weight c. The signed
T tangent cancels exactly. Relative to (11), the gain is
\[
       cF_{1/c}(t),\qquad
 F_a(s)=\sec s+K\tan s-R\sqrt{\sec^2s+a^2}
                                      -1+R\sqrt{1+a^2}.
\tag{22}
\]
The remaining D pair is \((1,c\sec t)\), containing only
its actual DE rotation if that is secondary. The angular
companion proves
\[
              cF_{1/c}(t)\ge\lambda t,
                  \qquad c\sec t<1.084.
\tag{23}
\]
Thus (9) applies with this one negative T magnitude t.

## 5. A genuine negative BT3 at aligned TD is shorter than .09

Now assume the last row of (3). If BT2 is also feasible,
reselect it and use the first row. Otherwise write
\(d_{BT}=-t<0\). The aligned TD0 witness gives
\[
                       y_T+b_D\ge1,
                     \qquad y_T>.1.
\tag{24}
\]
Apply the positive-Y contact-vector argument in Section 3
of [the negative-primary entry comparison](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md),
with its \((a,b,A,Y)=(a_B,b_B,a_T,y_T)\).
Its two projections are precisely the actual BT3 and BT2
at error −t. The argument uses sorting, Y>0 and the common
q containment; no high-GA assumption is involved in this
positive-Y part. It proves that T is flat and
\[
 a_T=7/12,\quad 0<y_T<.156,
\]
\[
 Q>1+K^2+(y_T+1/2)^2
           +2\{(y_T+1/2)\cos t+K\sin t\}.
\tag{25}
\]
For completeness, the strict contact-vector norm in that
argument is at most q; if T were also outer at q its own
shifted norm would already be q, contradicting the extra
positive terms. The numerical cuts then use q≤Q.

By (24), \(y_T+1/2>.6\). The right side of (25) is
strictly increasing in t on [0,h] and increasing in this
shifted tangent. At t=.09 its value with tangent .6
already exceeds Q, by
\[
               1+K^2+.6^2+1.2C_6(.09)+2KS_7(.09)>Q.
\tag{26}
\]
Therefore \(t<.09\).

Use (9), give BT3 weight \(c\sec t\), and TD0 weight c.
The exact cancellation now gives gain \(cF_{l/c}(t)\).
Since \(l/c\ge1/2\), the uniform short-secant estimate is
\[
 F_{l/c}(t)>1.048t,
 \qquad 1.048c-\lambda=.015624+.1668d-.1572d^2>0.
\tag{27}
\]
Thus the gain is at least \(\lambda t\). The only changed
ordinary pair is B, now \((l,c\sec t)\), with only AB
remaining. Section 3 of the angular companion proves its
canonical negative comparison using the net angle d−s;
the factor \(\sec t\) is not discarded. Its far endpoint
still obeys (16), since \(c\sec(.09)<1.04\).

## 6. Nonpositive E primaries at the actual q

First suppose the signed sum of the retained E-primary
errors is negative. A retained secondary E edge does not
contribute to this sum; its actual angle remains ordinary.
The following entry and reduction are local to D,E,H.

A genuine negative EH1, with EH0 unavailable, is flat
core and has \(b_E<.156\), by the same positive-Y norm
argument used above. An actual EH0 at any signed angle
gives
\[
 b_E\le\sqrt{a_H^2+b_H^2}-1\le a_0-1<.415<1/2,
\tag{28}
\]
so E is flat in that case too. If both E primaries are
negative, either EH0 can be reselected, or E is flat and
both negative primaries may be retained directly.

If the two E primaries have opposite signs and negative
sum, use the E-only transport in Sections 3--5 of
[the mixed negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
It retains the fixed D/H anchors, changes no G/A/B/T data,
preserves both actual neighboring inequalities, and
decreases both variations. It ends with one negative
primary and an actual secondary, on flat core. If an
available secondary is selected earlier, simply reclassify
the remaining E-primary sum.

That local construction is valid at the original q in (1).
Its exact implicit core formulas do not involve the outer
radius. The only outer lower-radius step is its tangent-zero
endpoint: the squared comparison there is at most 541/144,
whereas
\[
                           q\ge q_L>541/144.
\tag{29}
\]
The actual outer-q H circle therefore supplies the same
strict EH0 witness. All upper coordinate estimates use
q≤Q, and the flat endpoint remains contained at q. The
boundary bridge verifies the actual E-only path and its
endpoint; no enlarged Q anchor is substituted for a q
anchor.

We are left with one or two negative flat E primaries,
with magnitudes \(s_j\). Give each such primary the weight
\(\sec s_j\) and a secondary E edge weight 1. The signed
E tangent cancels. Relative to the full-circle baseline,
their radial gains are \(F_n(s_j)\) on H or \(F_c(s_j)\)
on D, with c replaced by the second positive tilt when
appropriate. All those unmodified coefficients are at
least k. The angular companion proves
\[
                    F_a(s)>1.03s\quad(a\ge k, 0<s\le h).
\tag{30}
\]
Each removed E primary therefore gains at least
\(\lambda s_j\), in either family.

If a negative TD2 and a negative DE3 both scale D, their
gains can be added. The full norm has mixed derivative
\[
         \partial_u\partial_v\sqrt{u^2+v^2}
                         =-uv/(u^2+v^2)^{3/2}<0;
\tag{31}
\]
the simultaneous norm increase is at most the sum of the
two separate increases. No D rotation remains in this
case. Otherwise the remaining actual H or D rotation is
covered by the sorted one-angle estimate in Section 6 of
the angular companion.

Let s be the total magnitude of these negative E primaries
and the possible negative T primary. The variation bound
gives s≤h. After all positive G/T and negative E/T primaries
are removed, the ordinary angles satisfy
\[
 N-P=d-s,\qquad P\le h-d,\qquad N\le h-s.
\tag{32}
\]
Equations (7) and (35) of the angular companion show that
their increments plus all negative gains are at least
\[
                     \min\{V_{l,k}(d),\lambda d\}.
\tag{33}
\]
This also applies when no E primary is retained or the
retained primary errors are zero, provided there is no
positive E charge to add. In particular, no transport
through an E=0 state is excluded by a high-GA premise.

## 7. The complete nonnegative core-E charge

It remains to treat a nonnegative signed E-primary total
e. For the core state write \(a=a_E,b=b_E\). Its exact
primary pair deficit, at errors u,v with u+v=e, is
\[
 L=W(u)+W(v)-2-a(\sin u+\sin v)-b(\cos u-\cos v).
\tag{34}
\]
It satisfies the whole-domain lower bound
\[
                L\ge J(e):=-\sin e/12-K(1-\cos e).
\tag{35}
\]
Here is a direct proof including opposite individual signs.
Put C=cos(e/2), S=sin(e/2), and \(\Delta=(u-v)/2\).
If both errors are nonnegative, (34) is
\[
                 \{C+(1-2a)S\}\cos\Delta
                          +2bS\sin\Delta-1.
\tag{36}
\]
Its second derivative is negative on
\(|\Delta|\le e/2\): the expression before the −1
exceeds .68 using \(a,b\le7/12\), \(e\le h\).
Its smaller endpoint is \(\Delta=-e/2\), with value
\[
                    (1/2-a)\sin e-(1/2+b)(1-\cos e)
                                                        \ge J(e).
\tag{37}
\]
If the errors have opposite signs, the worse orientation
has the negative error on DE, and (34) is at least
\[
                (C-2aS)\cos\delta+(C-2bS)\sin\delta-1,
                \qquad e/2\le\delta\le h-e/2.
\tag{38}
\]
Both coefficients are positive and the second is at least
the first, since b≤a. This expression is concave. Its far
endpoint minus its near endpoint is
\[
 2\sin((h-e)/2)
 \{(C-2bS)\cos(h/2)-(C-2aS)\sin(h/2)\}\ge0.
\tag{39}
\]
The near endpoint is (37), proving (35).

For a sole EH1 with a secondary DE2, its exact E deficit
is already (37). For a sole DE3 and secondary EH0 it is
\((1/2-a)\sin e-(1/2-b)(1-\cos e)\), which is no
smaller. The actual secondary angle stays in its ordinary
H or D block. If both edges are secondary take e=0 and
zero E charge. Thus (35) treats every nonnegative
E-primary total without any E-frame alignment.

## 8. Concentrating a nonnegative E total leaves four charges

Fix the actual positive G/T total d and, in family N,
the negative T magnitude t; put t=0 in family P. After
removing the E primary errors their signed sum e and
(35) leave the ordinary constraints
\[
 N-P=d+e-t,\qquad P\le h-d-e,\qquad N\le h-t,
                         \qquad 0\le e\le h-d.
\tag{40}
\]
If the two original E errors have opposite signs, (40)
is an enlargement: their extra positive and negative
magnitudes have both been dropped. This only weakens
the necessary bound.

For each fixed set of weights, the ordinary concentration
proof leaves a pure sign, one saturated same block, or
one saturated positive block and one negative block.
With e varying, every such alternative plus J(e) is
concave on its sign interval. For a saturated block this
is separate concavity with \(P=h-d-e\), \(N=h-t\);
for separated blocks it is concavity of U; for a pure
block it is concavity of U or V. Also
\(J''(e)=\sin e/12-K\cos e<0\).
The enlarged modified one-angle block is linear in P
and concave in N, so the same argument applies.

Thus only e=0, e=h−d, and a possible pure-sign junction
e=t−d need be checked. Saturated alternatives are concave
across that junction and have no extra endpoint there.

At e=0, (33), with s=t, leaves the charges
\(V_{l,k}(d)\) or \(\lambda d\). At e=h−d only negative
ordinary angles remain, totaling h−t. Concavity from
zero and (16) give
\[
 V_{\rm block}(h-t)\ge(1-t/h)V_{\rm block}(h)
                         >(1-t/h)(l-.0696).
\tag{41}
\]
Adding the negative T gain \(\lambda t\) leaves at least
\(\min\{l-.0696,\lambda h\}\). If t=0 only the first
of these is needed. Finally, if t≥d, then
\[
 J(t-d)+\lambda t\ge\lambda d,
\tag{42}
\]
because \(J'(u)>-.783\) on [0,h], while \(\lambda\ge.8888\).

Combining both signs of the E-primary total, the entire
core-E problem has therefore reduced to these charges:
\[
\begin{array}{c|l}
P&V_{l,k}(d),\quad1.03d,\quad J(h-d)+l-.0696\\
N&V_{l,k}(d),\quad\lambda d,\quad J(h-d)+l-.0696,
                                  \quad J(h-d)+\lambda h.
\end{array}
\tag{43}
\]
They are independent of the positive split x+z=d. Notice
that the varying-B comparison was needed only at e=0;
no unjustified replacement of r(d) by r(d+e) was made.

## 9. Both positive intermediate errors reduce to one scalar endpoint

In family P fix d, hence l and η. For
\[
        g_r(t)=kC_\eta(t)-R\sqrt{r^2+k^2f(t)^2},
        \qquad f(t)=\cos t+\eta\sin t,
\]
discard the nonpositive squared-derivative term to obtain
\[
 \begin{split}
 g_1''(t)&\le k\{-.55\cos t+.907\sin t\},\\
 g_l''(t)&\le k\{-.25\cos t+1.017\sin t\}.
 \end{split}
\tag{44}
\]
The exact coefficient checks use \(kf(t)<.92\),
\[
 \frac{Rkf}{\sqrt{1+k^2f^2}}<1.45,
 \qquad \frac{Rkf}{\sqrt{l^2+k^2f^2}}<1.75,
\]
and \(.25\le\eta\le.36515\). The two sine coefficients
\(R\sqrt{1+\eta^2}-1-.55\eta\) and
\(R\sqrt{1+\eta^2}-1-.25\eta\) are convex functions of η.
Their upper bounds .907 and 1.017 hold at both endpoints
by positive squaring, as recorded in the scalar companion.

For x+z=d, the second derivative of (12) with respect to x
is bounded above by
\[
 k\{A(d)\cos x+B(d)\sin x\},
\]
\[
 A(d)=-.55-.25\cos d+1.017\sin d<-.085,
 \qquad B(d)=.907-.25\sin d-1.017\cos d<-.03.
\tag{45}
\]
A increases and B is convex, so the single far endpoint
for A and the two endpoints for B prove these inequalities
on [0,h]. The Taylor checks are exact. Thus (12) is
strictly concave in the entire positive split.

The charges in (43) do not change with that split, so only
\((x,z)=(d,0)\) and \((0,d)\) remain. The first baseline
is at least the second, by the same norm-increment
comparison as (14), with \(m=kf(d)\). The smaller scalar
is exactly \(B_P(d)\) in (3) of the scalar companion.
The positive-BT baseline was already bounded below by
(12), so it has the same endpoint lower bound. The case
BT2/TD0 is the endpoint z=0 and is included as well.

These are scalar concavity and support comparisons. They
do not move G or T, replace their actual witnesses, or
claim that the endpoint split is geometrically feasible.

## 10. Strict contradiction and scope of the result

Adding the actual weak inequalities with the positive
weights above, then applying their shifted-circle
supports, requires a nonpositive value of the base
scalar plus the corresponding charge in (43).
In family P, Section 9 bounds it below by one of
\[
 B_P+V_{l,k}(d),\qquad B_P+1.03d,
                   \qquad B_P+J(h-d)+l-.0696.
\]
In family N it is one of the analogous four expressions
with \(B_N\), including \(B_N+J(h-d)+\lambda h\).
Every one is strictly positive on [0,h] by the seven
whole-interval rational certificates in the scalar
companion. This is the required contradiction.

The proof includes both AB owners with their original
signed error, every choice and sign of the E primaries,
either G/T tangent sign, and all four T regimes in (3).
Every same-state reselection uses an actual weak witness.
The only E transport stays at the original q, preserves
all other anchors and witnesses, and is used solely to
reach another strictly excluded necessary cycle. Hence
none of these core-E entry cases contributes an equality
case to the sharp hard-owner theorem.

This theorem supplies a full core-E positive-normal-entry
branch. Outer E and the remaining mixed-primary endpoint
joins are separate inputs to the global normal-entry
assembly. No numerical optimizer, angle mesh, Lean
compilation, or CI result is a premise of this proof.
