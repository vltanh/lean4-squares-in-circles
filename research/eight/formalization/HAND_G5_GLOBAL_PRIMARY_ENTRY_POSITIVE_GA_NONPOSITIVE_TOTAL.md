# Positive GA1 with a nonpositive HG0/GA1 total reaches actual GA0

## 1. Same-circle local theorem

Put
\[
 Q=9789/2500,\qquad h=7/10,\qquad
 L=447/800,\qquad K=13/12,\qquad \kappa_0=847/800.
\tag{1}
\]
Retain a sorted true-core H,G,A triple at a common shifted
corner ceiling \(q\le Q\), with H,A nonnegative and G
nonpositive signed tangents. Write \(y_G=-b_G\), \(b_G\ge0\).
Assume actual weak HG0 and GA1 witnesses at errors
\[
 d_{GA}=x>0,\qquad d_{HG}=-(s+x),\qquad s\ge0,
                             \qquad s+x\le h.
\tag{2}
\]
Thus the selected HG0/GA1 signed total is nonpositive.
Their actual projections are
\[
 \begin{split}
 b_H-a_G\sin(s+x)+b_G\cos(s+x)&\ge W(s+x),\\
 a_A+a_G\sin x-b_G\cos x&\ge W(x),\\
 W(r)&=(1+\cos r+|\sin r|)/2.
 \end{split}
\tag{3}
\]
Every true-core primary exceeds L. Circle containment and
sorting give \(a_i<283/200\), \(|y_i|<9/10\).

**Reduction theorem.** Keeping H,A and all other states and
frames fixed, replace only G by
\[
 \theta_G'=\theta_A,\qquad a_G'=7/12,
                         y_G'=-(a_A-1).
\tag{4}
\]
The new G is a strictly sorted normal flat-core state,
strictly inside the same actual q-circle. GA0 is exact and
HG0 has strict slack. The real frame interval does not
expand; the positive and negative error variations each
decrease by x. If the input is an actual boundary-neighbor
cycle, so is the output.

There is no condition on T's sign or radial kind, any other
owner, any other frame, or any E-primary total. There is no
high-GA unavailability assumption. Original weak witness
ties remain in scope.

## 2. The replacement is admissible at the original radius

Adding (3) gives
\[
 \begin{split}
 b_H+a_A\ge{}&W(s+x)+W(x)
       +a_G\{\sin(s+x)-\sin x\}\\
       &+b_G\{\cos x-\cos(s+x)\}\ge2.
 \end{split}
\tag{5}
\]
Hence \(a_A>1.1\), since \(b_H<.9\). In particular
\[
                   .1<a_A-1<.415<7/12.
\tag{6}
\]
The state (4) is strictly sorted and has negative signed
tangent. Its transverse magnitude is below one half, and
its primary is exactly \(1/2+1/12\), so its true-core
distance is exactly \(1/12\).

Comparing its shifted corner with the unchanged A corner,
\[
 \begin{split}
 q-\{K^2+(a_A-1/2)^2\}
 &\ge(a_A+1/2)^2+1/4-K^2-(a_A-1/2)^2\\
 &=2a_A+1/4-K^2>919/720.
 \end{split}
\tag{7}
\]
Thus (4) stays strictly inside the original q-circle. At
GA alignment its projection is
\[
                           a_A+y_G'=1,
\tag{8}
\]
which supplies actual GA0 and GA1 as tied original axes.

## 3. Exact HG slack and the flat-or-outer G case

The new HG error is \(-s\), and its actual slack is
\[
 \mathcal S=b_H-(7/12)\sin s+(a_A-1)\cos s-W(s).
\tag{9}
\]
Multiply the second original inequality in (3) by
\(\cos s>0\) and add the first. The exact identities
\[
 \sin(s+x)-\sin x\cos s=\cos x\sin s,
\qquad
 \cos x\cos s-\cos(s+x)=\sin x\sin s
\]
give
\[
 b_H+a_A\cos s\ge W(s+x)+W(x)\cos s
                         +(a_G\cos x+b_G\sin x)\sin s.
\tag{10}
\]
Substituting the positive-error width formulas into
(9)--(10) yields
\[
 \mathcal S\ge E(x,s):=
 \cos s\{\sin x+\cos x-1\}
       +\sin s\{(a_G+1/2)\cos x+(b_G-1/2)\sin x-K\}.
\tag{11}
\]

First suppose \(a_G\ge7/12\), which includes every outer
G and every flat-core G. Put \(t=\tan(x/2)\). Since
\(b_G\ge0\), the half-angle identities give
\[
 E(x,s)\ge\sin x\cos s
              \{1-t-\tan s(Kt+1/2)\}.
\tag{12}
\]
By (2), \(s\le h-x<\pi/4-x\). Also \(0<t<1/2\).
Therefore
\[
 \tan s<\tan(\pi/4-x)
              =\frac{1-2t-t^2}{1+2t-t^2}.
\tag{13}
\]
The right side is nonnegative since \(x<\pi/4\).
After multiplication by the positive denominator, the
bracket in (12) is bounded below by the polynomial
\[
 \begin{split}
 &(1-t)(1+2t-t^2)-(Kt+1/2)(1-2t-t^2)\\
 &\hspace{8mm}=\frac12+\frac{11}{12}t-\frac13t^2+
                                      \frac{25}{12}t^3\ge\frac12.
 \end{split}
\tag{14}
\]
Here \(t<1/2\) makes the linear term dominate the sole
negative quadratic term. The denominator in (13) is less
than 2. Thus
\[
                          \mathcal S>\tfrac14\sin x\cos s>0.
\tag{15}
\]
This is a strict whole-domain comparison, with no small-angle
assumption and no circle equality at G.

## 4. The curved true-core G case

It remains to treat \(a_G<7/12\). True central exclusion
then forces \(b_G>1/2\): if \(b_G\le1/2\), the nearest
point of its square would have distance less than \(1/12\).
The GA1 inequality gives
\[
             a_A>\frac12+\cos x-\frac1{12}\sin x.
\tag{16}
\]
If \(x\le1/4\), the lower cosine and upper sine bounds
would imply
\[
 a_A>\frac12+1-\frac{(1/4)^2}{2}-\frac{1/4}{12}
                         =139/96>283/200,
\]
a contradiction. Hence
\[
                              x>1/4,\qquad s<9/20.
\tag{17}
\]

In (11), use \(a_G\ge L\) and \(b_G>1/2\):
\[
 E(x,s)\ge\cos s\{\sin x+\cos x-1\}
                            +\sin s(\kappa_0\cos x-K).
\tag{18}
\]
On (17) and \(x\le h<\pi/4\), elementary alternating
Taylor bounds give
\[
 \cos s>.89,\quad \sin s<.45,\quad
 \sin x+\cos x-1>.21,\quad
 \kappa_0\cos x-K>-.275.
\tag{19}
\]
For the third inequality, use the increasing function
\(\sin x+\cos x\) and
\(S_3(1/4)+C_2(1/4)-1>.21\). For the last one, use
\(\cos h>.7648\). Consequently
\[
                   \mathcal S>.89(.21)-.45(.275)
                                  =.06315>3/50>0.
\tag{20}
\]
This completes the remaining true-core branch.

## 5. Boundary order and the unchanged data

Originally the two relevant errors were \((-(s+x),x)\).
After (4), they are \((-s,0)\). Thus both variations
decrease by x, and the new frame is an existing A frame.
All other six states, all other real errors, and all other
actual witnesses remain unchanged.

For an actual boundary-neighbor input, write
\[
 \alpha_H=\arctan(b_H/a_H),\quad
 \alpha_A=\arctan(b_A/a_A),\quad
 \gamma=\arctan((a_A-1)/(7/12)).
\]
The new physical gaps are
\[
          -s+\alpha_H+\gamma,
          \qquad \pi/2-\gamma-\alpha_A.
\tag{21}
\]
The second is strictly positive by strict sorting of G.
The first belongs to \((-h,\pi/2)\). Actual separation,
containment and true-core avoidance give smaller center
angle greater than \(19/25\), by the two-square central
band. A nonpositive first gap would have magnitude less
than \(h<19/25\), which is impossible. Thus both gaps are
positive. Their sum is unchanged, so the full neighbor
cycle still has winding one. The new G is an actual
canonical flat-core state.

This proves boundary-neighbor eligibility directly, without
assuming a continuous deformation through canonical states.
It is precisely the endpoint eligibility allowed by the
[boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).

## 6. Complete GA1/HG0 two-endpoint entry at the Q boundary

The new lemma completes one finite actual pair reduction.
Start with a retained GA1 and HG0 on an actual low-GA
boundary-neighbor cycle at Q, with arbitrary G sign and
arbitrary signs of their two errors. The outer endpoint
conditions on H,A are the original global low-GA conclusions.

* A zero GA error already supplies the actual GA0 tie.
* For \(y_G\ge0\), the
  [wrong-sign pair theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_WRONG_SIGN_PAIR_REDUCTION.md)
  reaches GA alignment or HG alignment for every signed
  total, including the nonpositive-total branch.
* For \(y_G<0\) and a negative GA1 error, select GA0 if it
  is already feasible. Otherwise the genuine-negative
  comparison gives the flat-core entry and the
  [negative-GA1 companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md)
  reaches GA alignment or HG alignment.
* For \(y_G<0\) and a positive GA1 error, a nonpositive
  paired total is handled by Sections 1--5. A positive
  paired total is handled, after reflection and reversal,
  by the existing
  [positive paired-primary](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
  and
  [signed-cancellation](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md)
  theorems, according to the individual signs.

Thus every actual GA1/HG0 pair at the Q boundary has a
G-only actual descendant with either GA0 or HG aligned.
At HG alignment the unchanged \(b_H<.9\) forces
\(y_G<-.1\), so that endpoint has the normal G sign.
No other witness, state or error is changed. The corresponding
complete BT3/TD2 statement follows by reflection, with a
T-only change and normal T at TD alignment.

The new theorem in Sections 1--5 holds at the original q.
The assembly in this section is explicitly stated at Q,
because the cited positive-total transports are stated on
the outer Q boundary. A uniform-q version of those separate
transports must be supplied before using this assembly as
an equality-preserving sharp-radius entry theorem.

This does not remove arbitrary HG2 from a sole positive GA1
branch, or arbitrary TD0 from a sole positive BT3 branch.
The existing local positive-primary obstruction explains why
those two arbitrary companion-owner cases cannot be declared
locally aligned. Nor does an HG-aligned negative-GA endpoint
by itself supply the other zero-edge alignments used in the
later aligned negative-primary theorem. Those global entry
obligations remain explicit.

## 7. Reflected statement and original equality

Under reflection and reversal, take
\((H,G,A)=(D,T,B)\). A normal T with BT3 error \(x>0\),
TD2 error \(-(s+x)\), and nonpositive total has the actual
replacement
\[
              \theta_T'=\theta_B,\qquad a_T'=7/12,
                                    y_T'=a_B-1>0.
\]
It supplies BT2, strict TD2 slack, the same-circle reserve
(7), and the same decrease of both variations. It is
independent of every A/E owner or signed total.

The strict circle loss in this note is at the intermediate
G or T. It is not a loss at one of the five stationary
anchors, and therefore must not alone be cited to rule out
original equality. All original H,A,B,D,E data were fixed;
any equality conclusion must use their unchanged constraints
and the complete hard-owner equality characterization.
