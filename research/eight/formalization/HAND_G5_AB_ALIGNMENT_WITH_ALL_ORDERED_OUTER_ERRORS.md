# AB aligns with every ordered normal-sign outer error

## 1. Scope and conclusion

Put
\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
 \qquad q_L\le q\le Q.
\tag{1}
\]
Retain the original normal signs
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\]
the original sorted circles, and the true core condition:
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q.
\tag{2}
\]
Let the real frames have spread at most `7/10` and satisfy
\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,
 \qquad \theta_D\le\theta_E\le\theta_H.
\tag{3}
\]
Allow either sign of each original outer difference
`theta_G-theta_H` and `theta_D-theta_T`. Retain the original
owners
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&0\text{ or }2&0&0\text{ or }2&2&0\text{ or }2&3&1.
\end{array}
\tag{4}
\]

**AB alignment theorem.** This necessary edge system has a
descendant with A and B at one common frame
`rho in [theta_D,theta_H]`, at the same actual radius q, and
\[
                         b_A'+b_B'=1.
\tag{5}
\]
H, D and E and their coordinates, frames and mixed constraints
are unchanged. Each outer path retains the appropriate positive
or negative owner comparison, or has already been replaced by
its aligned composite. Negative noncanceling comparison frames
are on the correct side of the common A/B frame. All new A/B
coordinates are nonnegative and sorted, and retain any earlier
strict A/B circle losses separately. If the original AB frame
difference is nonzero, one new A/B circle can be made strictly
smaller than q.

This extends the AB step of
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
and Section 7 of
`HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`
to negative noncanceling HG0/TD2 errors. It does not align those
remaining outer errors. The signs, ordering, quarter owners and
mixed owners in (2)--(4) remain explicit hypotheses.

For a radius lower-bound application, a smaller original q can
first be enlarged to q_L without moving its original centers.
Every construction below uses the working q in (1), not the
larger constant Q in a circle formula.

## 2. The preexisting constant caps

The elementary circle bounds from the cited signed three-zero
note are
\[
 b_i<\frac9{10},\quad a_i<\frac{283}{200},\quad
 |(a_i,b_i)|<\frac{283}{200}.
\tag{6}
\]
First align any negative *canceling* outer owner, HG2 or TD0,
by its same-anchor strict transport in Section 3 of that note.
Its corresponding comparison frame becomes H or D.

For every remaining nonnegative outer difference, use the
constant cap already proved in the cited notes: the effective
H/D cap for a canceling owner, or the exact same-G/T-circle cap
for a noncanceling owner. On the H side these have the form
\[
 X_A\cos t-Z_A\sin t\ge D_H+\cos t,
 \quad X_A=a_A+\frac12,\quad Z_A=b_A+\frac12,
\tag{7}
\]
where `t=gamma-theta_A>=0`, gamma is the G comparison frame,
and
\[
                         .434<D_H<.915.
\tag{8}
\]
In these cases `gamma>=theta_H`, so both A and B lie below
gamma. A previously aligned side is included by taking
`gamma=theta_H,D_H=3/2-b_H`. The D-side statement is reflected,
with a T comparison frame tau below D and
`u=theta_B-tau>=0`.

The same-circle cap for a positive HG0/TD2 side has its concrete
G/T realization as given in Section 2 of the positive-owner
note. The canceling cap is a necessary composite. These are
the same uses as in the published nonnegative-error reduction;
no new claim about omitted nonneighbor constraints is needed.

## 3. A negative noncanceling side has a constant cap until its intermediate frame is crossed

Consider HG0 with `theta_G<theta_H`. Its original GA0 and the
true core give `a_G>=7/12` before eliminating G. If
`theta_G<theta_A`, first use Section 4 of
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`
to restore its G comparison frame to A. This retains the actual
H and A coordinates and yields strict pair slack. Its concrete
core G has circle strictly below q_L.

Thus the comparison frame gamma may be assumed to satisfy
\[
 \theta_A\le\gamma\le\theta_H,
 \quad t=\gamma-\theta_A\ge0,
 \quad e=\theta_H-\gamma\ge0.
\tag{9}
\]
Adding HG0 times `sec(e)` to GA0, and using the true core,
gives exactly (7), now with
\[
       D_H(e)=1+(\tfrac12-b_H)\sec e+\frac{13}{12}\tan e.
\tag{10}
\]
For every `0<=e<=7/10`,
\[
\begin{aligned}
 D_H'(e)-1
 &=\frac{K+(1/2-b_H)\sin e-\cos^2e}{\cos^2e}\\
 &\ge\frac{(\sin e-1/5)^2+13/300}{\cos^2e}>0,
 \qquad K=\frac{13}{12}.
\end{aligned}
\tag{11}
\]
In particular `D_H(e)>=D_H(0)=3/2-b_H>3/5`.
Feasibility in (7), `t>=0`, and (6) also give
\[
 D_H(e)\le(a_A-1/2)\cos t-(b_A+1/2)\sin t
          \le a_A-1/2<.915.
\tag{12}
\]
So this cap is in the narrower subinterval
\[
                             .6<D_H(e)<.915
\tag{13}
\]
of (8).

For later construction, the cap has an exact core realization:
\[
 a_G'=\frac7{12},\qquad b_G'=D_H(e)-\frac12.
\tag{14}
\]
HG0 is an equality by (10), and GA0 is precisely (7).
The bound (13) gives `.1<b_G'<.415<a_G'`, and
\[
 (a_G'+1/2)^2+(b_G'+1/2)^2
 <\frac{169}{144}+\left(\frac{183}{200}\right)^2
 =\frac{723901}{360000}<q_L.
\tag{15}
\]
Thus this comparison preserves a valid original-type sorted,
core-avoiding adjacent G state throughout the cap construction.
Reflection supplies the identical statement on the T side.

## 4. A continuous cap remains steep when A passes G

For a fixed parameter D in (8), define at the actual q
\[
\begin{gathered}
 C=D+\cos z,\qquad w=\sqrt{q-C^2},\\
 X=C\cos z+w\sin z,\qquad
 L(z,D)=w\cos z-C\sin z.
\end{gathered}
\tag{16}
\]
The signed three-zero note proves, throughout its feasible cap
range,
\[
 X^2+L^2=q,
 \quad (X-1)\cos z-L\sin z=D,
 \quad -\partial_zL>\frac98\quad\hbox{when }L\ge\frac12.
\tag{17}
\]
Its radicand is positive on `[0,7/10]`, uniformly for (1),(8).
The actual A corner in (7) satisfies `Z_A<=L(t,D_H)`.

Move a prospective A frame rho upward from its original frame
to H. For a negative noncanceling H side define its cap by
\[
 \Lambda_H(\rho)=
 \begin{cases}
 L(\gamma-\rho,D_H(\theta_H-\gamma)),&\rho\le\gamma,\\
 L(0,D_H(\theta_H-\rho)),&\rho\ge\gamma.
 \end{cases}
\tag{18}
\]
The two expressions agree at gamma. In the second line put the
G comparison frame at rho and use (14). Thus crossing the old
G frame does not require a negative hard-quarter tilt.

The first derivative with respect to rho in the first branch is
greater than `9/8` whenever the cap is at least `1/2`, by (17).
In the second branch e decreases, so its parameter stays
between `D_H(0)>.6` and its original value below `.915`.
Since `L(0,D)=sqrt(q-(D+1)^2)`, (11) gives
\[
 \Lambda_H'(\rho)=
 \frac{D_H(e)+1}{\sqrt{q-(D_H(e)+1)^2}}D_H'(e)
 >\frac{320}{233}>\frac98.
\tag{19}
\]
Here `D_H(e)+1>8/5`, and
`sqrt(Q-(8/5)^2)<233/200`, by positive squaring.
Starting from the feasible original cap, it therefore increases
strictly across both branches and remains at least `1/2`.
Integration through the continuous crossing gives
\[
 \Lambda_H(\rho_2)-\Lambda_H(\rho_1)
 >\frac98(\rho_2-\rho_1)
 \quad(\rho_2>\rho_1\ge\theta_A).
\tag{20}
\]
For a nonnegative or already aligned outer side the ordinary
constant cap has the same conclusion, with no crossing. The
reflected continuous cap increases at the same rate when B
moves downward toward D.

## 5. Both AB owner cases now use the same comparison

Put `d=theta_B-theta_A`. For AB axis 0 its exact original
inequality in corner coordinates is
\[
 Z_A+X_B\sin d+Z_B\cos d
       \ge1+\cos d+(\sin d)_+.
\tag{21}
\]
The axis 2 case is its reflected counterpart.

Suppose first `d<0`, so B will move upward to A. Its comparison
T frame tau is no higher than B, by the preceding preprocessing.
This move goes away from T, so it never crosses T. Put
`u=theta_B-tau` and `v=theta_A-tau=u-d>u`. The same circle
calculation as in Section 5 of the signed three-zero note gives
\[
 X_B\sin d+Z_B\cos d
 \le g_v(D_D+\cos u),\qquad
 g_v(C)=\cos v\sqrt{q-C^2}-\sin v\,C.
\tag{22}
\]
For every parameter in (8), that note proves `g_v'(C)<-1` on
this whole domain. Since
`cos u-cos v>=1-cos(v-u)`, integration in C and (21) give
\[
                         Z_A+L(v,D_D)>2.
\tag{23}
\]
Keep A unchanged, put B at A's frame, set `b_B'=1-b_A`, and
choose its primary strictly below but sufficiently close to its
q-circle. Equation (23) makes its hard cap feasible with strict
room and gives a strict B-circle loss.

Suppose next `d>0`, so A will move upward to B. This may cross
G; (18)--(20) cover that crossing. Keeping B unchanged gives
\[
                 \Lambda_H(\theta_B)>Z_A+\frac98d.
\tag{24}
\]
The unchanged actual B circle and `d<=7/10` give
\[
 (X_B-1)\sin d+(Z_B-1)(\cos d-1)
 <.915d+\frac14d^2\le1.09d.
\tag{25}
\]
Combining (21), (24), and (25),
\[
                 \Lambda_H(\theta_B)+Z_B
                   >2+\frac7{200}d.
\tag{26}
\]
Put A at B's frame, set `b_A'=1-b_B`, and choose its primary
strictly below but sufficiently close to its q-circle. This
preserves its hard cap with strict room and gives a strict
A-circle loss. For a crossed negative G use the exact realization
(14) at the new frame; all other outer data used by its cap stay
fixed.

Apply the reflected argument for original AB axis 2. This covers
both signs of d and permits the analogous T crossing. If d is
zero, retain both original middle coordinates for the moment.
In every case the common frame is one of the original A or B
frames, so it remains between D and H, and the resulting AB
transverse sum is at least one.

## 6. Sorting, tangent normalization, and strict losses

Every newly constructed cap point is strictly sorted. Indeed,
at its feasible frontier `L>=1/2`, the second identity in (17)
gives
\[
 X\ge1+D>1.434>\sqrt{q/2},\qquad L<X.
\tag{27}
\]
The required new transverse corner is strictly below L by
(23) or (26). Its circle-frontier primary corner is therefore
strictly above X and strictly above its transverse corner.
The small primary decrease used there preserves sorting and
positivity. The retained middle point was originally sorted.
Every constructed cap also implies `a_i>=1/2+D>.934`, so its
primary alone satisfies the true core condition.

If the resulting common-frame sum is larger than one, keep A
and lower B's tangent to `b_B'=1-b_A`. This number is positive:
the sorted circles give `b_A,b_B<.9`, and their sum at least one
gives each tangent greater than `.1`. The new tangent is no
larger than the old B tangent. It improves B's circle and each
of its retained cap inequalities, because the transverse
coefficient in a nonnegative hard-quarter cap is nonpositive.
Sorting and the primary core condition remain valid. Thus (5)
can always be imposed. In particular there is at most one middle
tangent strictly greater than `1/2`.

When the original AB error is nonzero, the changed middle point
already has a strict circle loss. If an earlier strict loss was
at the retained point, it stays unchanged; if it was at the
changed point, its strict loss is recreated by (23) or (26).
Thus earlier strict losses at A and B are preserved separately,
and tangent normalization cannot erase them.

If AB was originally aligned, it is not necessary to lift either
primary, so any earlier circle losses and any strict outer-pair
slack survive directly. Once AB is aligned, strict pair slack
may be converted into a strict middle-circle loss by a
sufficiently small decrease of that middle primary, with the
retained cap realized as above. This does not change the AB sum,
H, D, E, or either mixed inequality.

The theorem therefore supplies the common-frame input for both
the nonnegative-outer reduction and the negative shared-chain
reductions, including their strictness bookkeeping. It makes no
claim that a mixed large-transverse negative side and a
small-transverse positive side already align, or that the
remaining nonzero-E negative boundary is excluded.
