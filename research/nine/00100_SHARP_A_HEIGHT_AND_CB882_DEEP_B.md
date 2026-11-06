# Sharp left-main height and a downward-cone exclusion for `001/00`

**Scope.** Original-nine physical squares; strict squared radius
`q<Q=1105/256`; same prescribed cone 4+3 witness and marked bits
`001/00`. All nine original frames, 36 pair conditions, and all
36 corners remain in the domain. We do not claim a whole-cell closure
here. These are two **new continuous hand implications** inside the
already frozen original-cell domains, not supplementary hypotheses.

Put
\[
 r=\sqrt{1105/256}<133/64,\qquad \rho=91/60,\qquad
 h_S\in[1/2,1/\sqrt2],\quad g_S=\frac1{4h_S}.
\]
Every center lies in \(|c_S|<\rho\), and the original aligned
inset of \(S\) has halfwidth \(g_S\). The first two original
main links \(AB,BC\) are actual horizontal projection comparisons,
the original \(CD\) comparison is center-cone and strictly weak,
and the original short chain \(E,F,G\) is actual.

## 1. An unconditional hand bound: \(|y_A|<1/3\)

The two actual main links and the original \(CD\) inset comparison give
\[
 x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D,\tag{1}
\]
and \(h_C+g_C\ge1,\ h_D+g_D\ge1\). The outer
horizontal projections lie in \([-r,r]\), hence
\[
 2r>2h_A+2h_B+(h_C+g_C)+(h_D+g_D)
 \ge2h_A+2h_B+2.
\]
As \(h_B\ge1/2\), we obtain
\[
 \frac12\le h_A<r-\frac32<\frac{37}{64}.             \tag{2}
\]
Likewise \(x_D+h_D<r\) and (1) yield
\[
 -x_A+g_A>h_A+g_A+3-r
 =4-r+\delta>\frac{123}{64}+\delta,
 \qquad \delta=h_A+g_A-1\ge0.                       \tag{3}
\]

Let \(h=h_A\in[1/2,37/64]\), \(g=1/(4h)\), and
\(A_0=123/64\). Both left-outward corners of the original contained
aligned inset belong to the \(Q\)-disk. Therefore
\[
 (A_0+h+g-1)^2+(|y_A|+g)^2<Q.                     \tag{4}
\]
We claim for every such \(h\)
\[
 L(h):=(A_0+h+g-1)^2+(g+1/3)^2>Q.                \tag{5}
\]
This is a one-interval rational monotonicity check.

Indeed \(\delta'(h)=1-1/(4h^2)\ge0\), so
\[
 A_0+\delta\le A_0+37/64+16/37-1
             =143/74<2.
\]
Also \(4h^2-1\le345/1024<7/20\), whereas
\(g+1/3\ge16/37+1/3=85/111>3/4\).
The sign of the derivative \(L'(h)\) is the sign of
\[
 (4h^2-1)(A_0+\delta)-(g+1/3)
 <(7/20)\cdot2-3/4<0.
\]
Thus \(L\) is strictly decreasing. Its endpoint comparison is
\[
 L(37/64)-Q=\frac{13519}{3154176}>0.
\]
This proves (5). If \(|y_A|\ge1/3\), inequalities (4) and (5)
contradict each other. Hence
\[
 \boxed{|y_A|<1/3.}                                \tag{6}
\]
No main-edge cone equality, tilted-square owner, extra position,
or additional row condition has been assumed.

### C887 consequence

For the frozen `negative-887236b78100baf3` first-satisfied
escape, the selected original AB cone slack satisfies
\[
 (x_B-x_A)+(y_B-y_A)=0.
\]
Since \(AB\) is actual, \(x_B-x_A\ge h_A+h_B\ge1\).
Equation (6) therefore forces
\[
 \boxed{y_B<-2/3\quad\text{throughout the original C887 cell}.} \tag{7}
\]
This is a strict implication even on the AB diagonal face.

## 2. The entire low-B downward cone is impossible

Use the previously hand-proved C-slant theorem on the unchanged
`001/00` original domain with normalized \(y_D-y_C>2/3\):
\[
 \frac{29}{60}<x_C<\frac45,\qquad
 \text{no additional original }X\text{ has }
 x_X\ge0,\ y_X\le y_C.
 \tag{8}
\]
The standard main bounds also give
\[
 -31/60<x_B<-27/64.                                \tag{9}
\]
(The left bound is from the actual AB comparison and the
center disk; the right is from the actual BC comparison and
\(x_C-h_C<r-2<5/64\).)

**Proposition.** No additional original \(H\) can satisfy
\[
 y_B\le-2/3,\qquad y_H-y_B\le-|x_H-x_B|.             \tag{10}
\]
All contacts, arbitrary physical orientations, and the original
incircles are retained.

*Proof.* Write \(k=y_B-y_H\ge |x_H-x_B|=:z\).
Disjoint original radius-half disks require \(k^2+z^2\ge1\).
Since \(k\ge z\), it follows that \(k\ge1/\sqrt2>7/10\), whence
\[
 y_H\le -\frac23-\frac7{10}=-\frac{41}{30}.        \tag{11}
\]
If \(|x_H|\ge2/3\), (11) gives
\[
 |c_H|^2\ge(2/3)^2+(41/30)^2
          =\frac{8324}{3600}>\frac{8281}{3600}=\rho^2,
\]
contradiction. Therefore \(|x_H|<2/3\).

Suppose \(x_H\le0\). Since \(-2/3<x_H\le0\) and (9),
\[
 z=|x_H-x_B|<
 \max\{31/60,\ 2/3-27/64\}=31/60.
\]
The original B/H incircles then give
\[
 k>\sqrt{1-(31/60)^2}
   =\frac{\sqrt{2639}}{60}
   >\frac{51}{60}=\frac{17}{20},
\]
as \(2639>51^2=2601\). Equations (10) and (11)
yield \(y_H<-2/3-17/20=-91/60=-\rho\),
contradicting the center bound. Thus
\[
                            0<x_H<2/3.            \tag{12}
\]

The C-slant theorem (8), applied to this very same original H,
now forces \(y_H>y_C\). But (11), \(|c_C|<\rho\),
(12), and \(29/60<x_C<4/5\) imply
\[
 0<y_H-y_C<\rho-41/30=3/20,\qquad
 |x_H-x_C|<4/5.
\]
Consequently
\[
 |c_H-c_C|^2<(4/5)^2+(3/20)^2
 =265/400<1,
\]
contradicting the two original radius-half disks. This proves the
proposition without choosing H's frame. \(\square\)

### Complete Cb882 subdomain

In the frozen `negative-b882d8ade0cf9ea0` cell, the
literal first-satisfied `alternate_four_escape(B,H)` entry 3
has primary row
\[
 (x_H-x_B)+(y_H-y_B)\le0
\]
and predecessor complement for entry 2
\[
 (x_H-x_B)-(y_H-y_B)\ge0.
\]
Together they give \(y_H-y_B\le-|x_H-x_B|\).
The proposition excludes the **whole** closed subdomain \(y_B\le-2/3\)
of that exact cell, and establishes the strict necessary bound
\[
 \boxed{y_B>-2/3\quad\text{inside Cb882}.}         \tag{13}
\]

The complementary continuous domain \(y_B>-2/3\) **remains OPEN**.
This strengthens the prior \(-4/5\) cutoff without assuming
the conclusion at any other original cell.

## 3. Improved C boundary dependency

The existing strict-interiorization lemma in
[00100_C_BOUNDARY_DOMINANCE.md](00100_C_BOUNDARY_DOMINANCE.md)
allows one to perturb a hypothetical C887 strict-radius packing,
without changing original frames, physical separation, the marked
bits or the strict \(y_D-y_C>2/3\) inequality, so that all
five selected center-cone slacks become strictly positive.
The perturbation may also retain the **strict** bound
\(y_B<-2/3\) proved in (7).

For that nearby packing, first-satisfied alternate-four escape
branches 0 and 1 cannot apply because the original AB cone slacks
are both strictly positive. Branch 3 cannot apply: its exact
primary and predecessor require the downward-cone condition
excluded by (10)--(13) while \(y_B<-2/3\).
The old frozen fixed-original register identifies branches
4,5,6 and all 29 original descendants of branch 7 as
already CLOSED. The only remaining possible branch is
branch 2, namely **the exact original Cd402 cell**.

Therefore we obtain the stronger conditional theorem:

> **If the entire Cd402 original-cell predicate is excluded at
> strict \(q<Q\), then the C887 original-cell predicate is excluded
> as well.**

This shortens the independent seven-cell worklist to five
obligations: A-c744, B7, B462, B16a, and Cd402 or Cb882?
**Precisely:** the still independently necessary targets are
A-c744, B7, B462, B16a, Cd402 and Cb882, i.e. **six**:
the original C887 has no independent proof requirement after
Cd402 is closed. The extra Cb882 domain still needs its own proof.
The list is deliberately explicit to prevent a mistaken
five-cell credit or a claim of Cb882 closure.

The frozen ledger remains **224/231 original cells CLOSED and
seven OPEN**; only the proof dependencies and the Cb882
necessary height restriction have improved. No Lean, CI,
numerical discovery, or archived certificate replay was used
to derive these two hand estimates, and no independent review
of this new chapter is claimed.
