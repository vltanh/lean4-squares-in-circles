# The jump-two row for every core/outer boundary pair

This is a hand proof of the entire \(k=2\) row of the common
quarter-increment table. Together with the cited critical outer/outer
note, it covers every signed core/outer pair and both surviving source
axes. The other two surviving axes are their reflected reverse images.

Use the labels of the common three-row table, not the different labels
of the four-type frame-concentration proposal:

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},\quad
 K=\frac{73}{10},\quad h=\frac{291}{250},
\]

\[
 L_O(a,b)=-\frac9{100}+pa+qb,\qquad
 L_C(a,b)=K(7/12-a)+hb.                                     \tag{1}
\]

Here the positive outer arc is

\[
 (a+1/2)^2+(b+1/2)^2=Q,\qquad0\le b\le a,
\]

and the positive core boundary is its usual side
\(a=7/12,\ 0\le b\le1/2\), followed by

\[
 (a-1/2)^2+(b-1/2)^2=1/144,\qquad1/2\le b\le a.
\]

For signed source and target states, define

\[
 \mathcal C=\phi+\sigma L_s(a,b)-\tau L_t(A,B),
 \qquad \pi-\frac7{10}\le\phi\le\pi+\frac7{10}.             \tag{2}
\]

**Theorem.** If either surviving source axis is a genuine separating
axis, then

\[
 \boxed{\mathcal C>\frac{163}{200}=.815.}                   \tag{3}
\]

For consecutive squares in the seven-state boundary ring, the cap and
common-point lemmas exclude the other four signed axes: in particular
the common-point lemma gives \(0<\delta<3\pi/4\). Consequently
(3), its reflected reverse, and those exclusions prove the whole
jump-two row for the ring. No unmentioned restriction on \(\phi\)
is required.

## 1. Marker ranges and a short angle interval

Write

\[
 a_0=\sqrt{Q-1/4}-1/2,\quad
 c_O=\sqrt{Q/2}-1/2,\quad
 c_C=1/2+\sqrt2/24.
\]

Direct squaring gives

\[
 1.41<a_0<1.415,\qquad c_O<.9,\qquad .55<c_C<.56.           \tag{4}
\]

Along the outer arc, \(a'(b)=-(b+1/2)/(a+1/2)\in[-1,0]\),
so \(L_O\) increases. Its axial minimum is positive, and its
diagonal maximum gives

\[
 0<L_O\le-.09+(p+q)c_O<.882=\frac{441}{500}.                \tag{5}
\]

Also

\[
 a+b\le2c_O<\frac95.                                      \tag{6}
\]

The core label is nonnegative and increases along both its side and
corner, so its maximum is at \((c_C,c_C)\). Since
\(\sqrt2>707/500\), we have \(c_C>6707/12000\), and hence

\[
 0\le L_C\le K(7/12-c_C)+hc_C
 <\frac{1243231}{1500000}<\frac{83}{100}=.83.               \tag{7}
\]

The negative coefficient \(h-K\) justifies using the lower bound
for \(c_C\) here.

All sign patterns except \((\sigma,\tau)=(-,+)\) now satisfy

\[
 \mathcal C\ge\phi-.882
 >3.1415-.7-.882=\frac{3119}{2000}>.815.                    \tag{8}
\]

For the remaining sign pattern, (5)--(7) show that
\(\phi\ge13/5\) implies

\[
 \mathcal C>\frac{13}{5}-2(.882)=\frac{209}{250}>.815.      \tag{9}
\]

Thus the only remaining domain is

\[
 (\sigma,\tau)=(-,+),\qquad
 I=[\pi-7/10,13/5].                                       \tag{10}
\]

On this interval put \(s=\sin\phi\) and \(d=-\cos\phi\).
The elementary bounds \(3.1415<\pi\),
\(1-.7^2/2>3/4\), and \(13/5<5\pi/6\) give

\[
 \frac12\le s<\frac{13}{20},\qquad
 \frac34<d<\frac78,\qquad s<d,
 \qquad W=\frac{1+s+d}{2}.                               \tag{11}
\]

For \(d<7/8\) use \(d\le\sqrt3/2<7/8\). All trigonometric
claims in (11) thus follow from elementary angle monotonicity and
squaring; there is no numerical angle solver.

## 2. Every source-secondary case

With signs \((-,+)\), the source-secondary separation condition is

\[
 -b+As+Bd\ge W.                                          \tag{12}
\]

If the target is core, its center norm is below \(4/5\).
Indeed the side has squared norm at most \(85/144<16/25\),
and the corner has norm at most
\(\sqrt2/2+1/12<4/5\). Cauchy--Schwarz gives
\(As+Bd<4/5<W\), contradicting (12). This excludes both
core/core and outer/core secondary cases.

If the target is outer, \(As+Bd\) increases as \(B\) runs
along its arc, because its derivative is at least \(d-s>0\).
It is therefore at most \(c_O(s+d)\). Equation (12) implies

\[
 b\le(c_O-1/2)(s+d)-1/2
 <\frac25\sqrt2-\frac12<\frac7{100}.                       \tag{13}
\]

The last inequality follows from \(\sqrt2<57/40\).
If the source is core, (13) places it on the vertical side and
\(L_C=hb<.082\). If the source is outer, (4) and (13) give

\[
 L_O<-.09+p(1.415)+q(.07)<.082.
\]

Thus both remaining secondary cases satisfy

\[
 \mathcal C>3.1415-.7-.082-.882
 =\frac{591}{400}>.815.                                  \tag{14}
\]

## 3. Core source and core target on the negative-primary axis

The negative-primary separation condition is now

\[
 a+Ad-Bs\ge W.                                           \tag{15}
\]

When both states are core, \(a,A\le7/12\) and \(B\ge0\),
so its margin is at most

\[
 \frac7{12}(1+d)-\frac{1+s+d}{2}
 =\frac{1+d}{12}-\frac s2
 \le\frac16-\frac14<0.
\]

This case is impossible throughout (10).

## 4. Core source and outer target on the negative-primary axis

Here \(a\le7/12\), and (6) gives \(A<9/5-B\).
Substitution in (15) shows

\[
 B(s+d)<\frac1{12}+\frac{13}{10}d-\frac s2
 <\frac1{12}+\frac{13}{10}\frac78-\frac14
 =\frac{233}{240}.
\]

Since \(s+d>5/4\), this gives

\[
 B<\frac{233}{300}<\frac{39}{50}.                         \tag{16}
\]

Use (6) once more, now in the marker itself:

\[
 L_O(A,B)=-.09+p(A+B)+(q-p)B
 <-.09+p\frac95+(q-p)\frac{39}{50}
 =\frac{96}{125}=.768.                                  \tag{17}
\]

Equations (7) and (17) imply

\[
 \mathcal C>3.1415-.7-.83-.768
 =\frac{1687}{2000}>.815.                                \tag{18}
\]

## 5. Outer source and core target on the negative-primary axis

Subtract the separating margin in (15), with multiplier one, from
\(\mathcal C=\phi-L_O-L_C\). The source term becomes
\(-(p+1)a-qb\). Enlarging its outer arc to the full outer circle
gives the lower bound

\[
 \frac{p+q+1}{2}-R\sqrt{(p+1)^2+q^2}.
\]

The target term is

\[
 -L_C-Ad+Bs
 =-7K/12+(K-d)A+(s-h)B.
\]

On (10), \(K-d>0\) and \(s-h<0\). This affine function
strictly decreases along the core side and corner, since the primary
coordinate is nonincreasing as \(B\) increases. Its minimum is
therefore the diagonal value
\(-L_C(c_C,c_C)-c_Cd+c_Cs\).

Consequently

\[
 \begin{split}
 \mathcal C\ge F(\phi):={}&\phi+\frac{163}{100}
      -L_C(c_C,c_C)-R\sqrt{(p+1)^2+q^2}\\
 &+(1/2-c_C)d+(1/2+c_C)s.                                \tag{19}
 \end{split}
\]

This function is increasing on the whole interval. Indeed (4) and
(11) give

\[
 F'=1-(c_C-1/2)s-(c_C+1/2)d
 >1-\frac3{50}\frac{13}{20}-\frac{53}{50}\frac78
 =\frac{67}{2000}>0.                                    \tag{20}
\]

There is just one endpoint comparison. Squaring proves

\[
 R\sqrt{(p+1)^2+q^2}<\frac{73}{25}.
\]

The alternating Taylor bounds give
\(\sin(.7)>.644\) and \(\cos(.7)<.765\).
Using these bounds, (4), and (7) in (19) yields

\[
 \begin{split}
 F(\pi-.7)
 &>3.1415-.7+1.63-.83-2.92
       -(.06)(.765)+(1.05)(.644)\\
 &=\frac{4759}{5000}=.9518>.815.                          \tag{21}
 \end{split}
\]

This proves the entire outer/core negative-primary case, including the
core corner.

## 6. Outer source and outer target on the negative-primary axis

This is exactly `JUMP_TWO_OUTER_OPPOSITE_HAND_PROOF.md`.
It uses the fixed multiplier \(3/4\), the diagonal source support,
the full-circle target support, and the identity

\[
 N''+N/4=\frac{(p^2+q^2-(3/4)^2)^2}{4N^3}>0.
\]

The scalar lower bound has \(F''<-1/16\) throughout (10), and
the two printed endpoint rows prove

\[
 \mathcal C>\frac{815887}{1000000}>.815.                   \tag{22}
\]

## 7. Complete coverage

The finite cover can be displayed without any hidden angle cells:

| Domain | Core/core | Core/outer | Outer/core | Outer/outer |
|---|---|---|---|---|
| Signs other than \((-,+)\), all jump-two angles | (8) | (8) | (8) | (8) |
| Signs \((-,+)\), \(\phi\ge13/5\) | (9) | (9) | (9) | (9) |
| Signs \((-,+)\), \(\phi\in I\), source secondary | impossible | (14) | impossible | (14) |
| Signs \((-,+)\), \(\phi\in I\), source negative primary | impossible | (18) | (21) | (22) |

At zero tangent, the signed endpoint inequalities also hold. A
deterministically chosen signed representative suffices for telescoping;
alternatively averaging the two endpoint marker values preserves the
strict pair bound, because the cost is affine in each marker.
Reflection followed by reversal preserves the cost and \(\phi\),
and covers both target axes. This completes the whole row. \(\square\)
