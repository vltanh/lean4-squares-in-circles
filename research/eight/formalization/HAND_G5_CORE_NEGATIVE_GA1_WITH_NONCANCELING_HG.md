# A flat-core negative GA1 angle reaches GA0 or HG alignment

## 1. Local statement and its precise scope

Put
\[
 Q=\frac{9789}{2500},\qquad K=\frac{13}{12}.
\tag{1}
\]
Consider the normal signed triple H,G,A, with tangents
\(b_H,-b_G,b_A\), sorted magnitudes, true central exclusion,
and actual shifted corners bounded by a common \(q\le Q\).
Their real frames lie in one interval of length at most
\(7/10\). Assume
\[
 a_G=\frac7{12},\qquad
 z=\theta_G-\theta_A>0,
\tag{2}
\]
and retain the actual witnesses HG0 and GA1. Thus the GA1
error \(\theta_A-\theta_G=-z\) is negative.

**Local reduction.** Keeping H,A, every other point, and all
their frames fixed, one can replace G by a sorted point on
its true flat core, with shifted corner strictly below q,
so that HG0 and GA1 remain feasible and either
\[
 \theta_G'=\theta_A
 \quad\hbox{or}\quad
 \theta_G'=\theta_H.
\tag{3}
\]
In the first case the actual GA0 witness is also feasible.
The replacement frame stays between the original H,G,A
frames. If HG was not originally aligned, the chosen
replacement has strict HG0 slack.

This is a local neighboring-inequality reduction. It does
not claim to preserve nonneighbor packing inequalities,
G1 markers, or the original radial-boundary status of G.
It applies to a necessary comparison cycle in which the
two retained constraints involving G are HG and GA.
The H and A coordinates, and hence any previously retained
strict H/A circle losses, are unchanged.

For an original boundary representative with normal signs,
Section 4 of
[the low-GA/high-EH exclusion](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md)
gives a useful entry alternative: an actual negative GA1
witness either already has GA0 feasible, or forces G to
be flat core with \(a_G=7/12\), \(b_G<39/250\), and
\(z<9/20\). The present result applies to the latter
alternative whenever HG0 is retained. It places no order
assumption on H relative to A or G.

## 2. The exact primary cap and its intrinsic endpoints

Rotate all three frames so that \(\theta_A=0\), and put
\[
 \Theta=\theta_H,\qquad P=a_A-\frac12.
\tag{4}
\]
For \(x\ge0\), the GA1 inequality at \(\theta_G=x\) is
\[
 a_A-a_G\sin x-b_G\cos x
       \ge\frac{1+\cos x+\sin x}{2}.
\]
With \(a_G=7/12\), this is precisely
\[
 b_G+\frac12\le D(x),\qquad
 D(x)=\frac{P-K\sin x}{\cos x}.
\tag{5}
\]
The initial negative error makes \(a_A>1\). The sorted
circle bounds give
\[
 \frac12<P<\frac{183}{200},\qquad b_H<\frac9{10}.
\tag{6}
\]
For the upper primary bound, the positive-squaring reserve is
\[
 \left(\frac{283}{200}+\frac12\right)^2+\frac14-Q
       =\frac{13}{8000}>0.
\]
For the tangent bound, \(2(7/5)^2-Q=11/2500>0\).

The lower Taylor bounds at \(x=9/20\) give
\[
 \frac12\left(1-\frac{x^2}{2}\right)
 +K\left(x-\frac{x^3}{6}\right)-\frac{183}{200}
       =\frac{347}{64000}>0.
\tag{7}
\]
Since \(\frac12\cos x+K\sin x\) is increasing on
\([0,7/10]\), feasibility of (5) forces \(z<9/20\).
Indeed its derivative exceeds
\(K(3/4)-(1/2)(13/20)=39/80>0\).

There is one intrinsic endpoint \(z_0\in(0,9/20)\) with
\(D(z_0)=1/2\), and
\[
 D(x)\ge\frac12\quad\Longleftrightarrow\quad
                         0\le x\le z_0.
\tag{8}
\]
Here and below only \(0\le x\le7/10\) is at issue.
The uniqueness follows from
\[
 D'(x)=D(x)\tan x-K
       =\frac{P\sin x-K}{\cos^2x}<0.
\tag{9}
\]

At any allowed x, maximize the G tangent to
\[
 a_G(x)=\frac7{12},\qquad b_G(x)=D(x)-\frac12.
\tag{10}
\]
This makes GA1 an equality. It improves HG0 at the same
frame, since its G-tangent coefficient is a positive
cosine. The replacement is sorted and remains on the
true flat core, because
\[
 0\le b_G(x)<\frac{83}{200}<\frac12<\frac7{12}.
\tag{11}
\]
Its shifted corner is strictly below the original common
ceiling. In fact \(a_A>1\) gives \(q>5/2\), whereas
\[
 \left(\frac{13}{12}\right)^2+
       \left(\frac{183}{200}\right)^2
 =\frac{723901}{360000}
 =\frac52-\frac{176099}{360000}<q.
\tag{12}
\]
No enlargement of q is needed.

## 3. G on or above H: a strictly increasing required tangent

Suppose first that \(z\ge\Theta\). Write \(h=x-\Theta\).
For \(x\in[\max\{0,\Theta\},z]\), both \(h\ge0\) and
\(h\le7/10\), and the HG0 inequality for (10) is
\[
 b_H\ge B_+(x),\qquad
 B_+(x)=\frac12+(1-D(x))\cos h+(1-K)\sin h.
\tag{13}
\]
Differentiating with (9) yields the exact identity
\[
 B_+'(x)=(1-D(x)\tan x)\cos h+(D(x)-1)\sin h.
\tag{14}
\]
Throughout the interval,
\[
 \tan x<\frac12,\qquad
 \cos h>\frac34,\qquad \sin h<\frac{13}{20}.
\tag{15}
\]
At \(x=9/20\), the first assertion follows from
\[
 1-\frac{x^2}{2}
   -2\left(x-\frac{x^3}{6}+\frac{x^5}{120}\right)
       =\frac{1844317}{64000000}>0.
\]
The other two follow at \(h=7/10\) from reserves
\(1/200\) and \(69193/12000000\), respectively.
Consequently
\[
 B_+'(x)>
 \left(1-\frac{183}{400}\right)\frac34
       -\frac12\frac{13}{20}
 =\frac{131}{1600}>\frac2{25}.
\tag{16}
\]

Lower x to \(\max\{0,\Theta\}\). The required H
tangent strictly decreases if the move is nonzero, so
HG0 remains feasible with strict slack. If \(\Theta\le0\),
the endpoint is G=A. If \(\Theta>0\), it is G=H.
When G=H was already aligned, maximizing its tangent as
in (10) suffices and no strict-slack claim is needed.

## 4. G below H: strict concavity leaves the same two endpoints

Now suppose \(0<z<\Theta\), so \(0<\Theta\le7/10\).
For
\[
 0\le x\le x_1:=\min\{\Theta,z_0\},\qquad
                         e=\Theta-x,
\tag{17}
\]
HG0 for (10) is
\[
 b_H\ge B_-(x),\qquad
 B_-(x)=\frac12+(1-D(x))\cos e+K\sin e.
\tag{18}
\]
The two exact derivatives are
\[
 \begin{aligned}
 B_-'(x)&=\sin e-D(x)\frac{\sin\Theta}{\cos x},\\
 B_-''(x)&=-\cos e+
       \frac{\sin\Theta}{\cos x}
                       \{K-2D(x)\tan x\}.
 \end{aligned}
\tag{19}
\]
Since \(2D(x)\ge1\), multiplication by the positive
\(\cos x\) gives
\[
 \begin{split}
 \cos x\,B_-''(x)
 \le{}&-\cos\Theta+K\sin\Theta
       +\cos\Theta\sin^2x\\
     &-\sin\Theta\sin x\{\cos x+\sec x\}.
 \end{split}
\tag{20}
\]
Here \(\sin\Theta\ge\sin x\), \(\cos\Theta\le1\),
and \(\cos x+\sec x\ge2\). The last two terms are
therefore at most \(-\sin^2x\). In particular,
\[
 \cos x\,B_-''(x)
 <-\frac34+\frac{13}{12}\frac{13}{20}
 =-\frac{11}{240},
 \qquad B_-''(x)<-\frac{11}{240}.
\tag{21}
\]
Thus \(B_-\) is strictly concave on its full intrinsic
interval; its minimum is at an endpoint.

If the upper endpoint is \(x_1=z_0\le\Theta\), it has
zero G tangent and would require
\[
 b_H\ge\frac12+\frac12\cos(\Theta-z_0)
                       +K\sin(\Theta-z_0)\ge1.
\tag{22}
\]
The last function increases on \([0,7/10]\), by the
derivative bound used after (7). This contradicts
\(b_H<9/10\); the same contradiction applies when
\(z_0=\Theta\).

The original feasible z is strictly inside (17):
\(z<\Theta\) by assumption, and \(z=z_0\) would give
the impossible zero-tangent case (22). Strict concavity
therefore supplies an endpoint with a strictly smaller
required H tangent than at z. If \(\Theta<z_0\), that
endpoint is either 0 or \(\Theta\). If
\(z_0\le\Theta\), the infeasible upper endpoint is
discarded and the endpoint is 0. These are exactly G=A
or G=H, with strict HG0 slack in every case.

## 5. Witness recovery and strictness available to later reductions

At the endpoint G=A, formula (10) gives
\[
                         b_G=a_A-1.
\tag{23}
\]
Both GA0 and GA1 then have projection \(a_A-b_G=1=W(0)\).
The actual hard GA0 witness is therefore available. At
the endpoint G=H, HG is aligned and both its surviving
zero owners have the same projection \(b_H+b_G\).

Every constructed G frame lies in the closed convex hull
of the original three frames. All other frames stay
fixed, so the full original frame spread is preserved.
Only the two G-neighbor witnesses change. Inherited
circle losses in every unchanged point remain strict.

When HG was nonaligned, the strict HG0 slack can also
be converted to a strict A-circle loss provided the
other retained A-neighbor witness is independent of
\(a_A\); this holds for AB0 or for aligned AB. At either
selected endpoint \(b_G>0\): at G=A this follows from
\(a_A>1\); at G=H it follows from
\(b_H+b_G>1\) and \(b_H<9/10\). Lower \(b_G\) by a
sufficiently small positive amount. HG0 remains feasible,
while GA1 acquires positive slack because its G-tangent
coefficient is \(-\cos x<0\). Lower \(a_A\) by a still
smaller positive amount, preserving GA1, sorting and the
true exclusion. The AB witness under the stated condition
is unchanged, and A's shifted corner strictly decreases.
This optional strict-loss restoration is not asserted
for an arbitrary unaligned AB2 witness.

The reflected reversal gives the corresponding statement
for a flat-core T with negative BT3 error and a retained
noncanceling TD2 witness. The proof is the same local
two-contact calculation; it makes no claim that the
required signs or flat-core alternative have already
been established in a global candidate.
