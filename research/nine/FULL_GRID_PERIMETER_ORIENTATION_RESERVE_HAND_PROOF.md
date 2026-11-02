# A full-nine perimeter reserve at an actual diagonal first birth

November 2, 2026 UTC. Complete hand inequalities. No mathematical
program, numerical search, Lean, Lake, or CI was used for this note.

The retained three-by-three center-cone array supplies four boundary
spans simultaneously. Their sum gives a physical diagonal-support
inequality involving all eight perimeter squares. An actual entering
diagonal adds an explicit reserve. Two continuous orientation domains
are excluded below; the unrestricted first-birth case is not claimed.

## 1. Physical hypotheses and the retained array

Let nine physical unit squares, with pairwise disjoint open interiors,
be contained in the centered closed disk of squared radius

\[
 Q=1105/256,\qquad r=\sqrt Q.
\]

In the chosen orthonormal frame write the retained array as

\[
\begin{array}{ccc}
 T=S_{13}&U=S_{23}&V=S_{33}\\
 F=S_{12}&C=S_{22}&D=S_{32}\\
 E=S_{11}&H=S_{21}&I=S_{31}.
\end{array}
\tag{1}
\]

Each row, read left to right, is a center-cone x-three-chain, and
each column, read bottom to top, is a center-cone y-three-chain.
Thus a designated x-gap is at least the absolute y-gap, and
conversely for a designated y-gap. All nine physical squares remain
in the hypotheses; in particular H and I are retained even when
the entering four-chain is E,F,C,D.

For each square S put

\[
 h_S=H_S(e_x)=H_S(e_y),\quad
 g_S=\frac1{4h_S},\quad k_S=\sqrt{1/2-h_S^2},\quad
 a_S=h_S+k_S,
\]
\[
 \eta_S=h_S+g_S-1\ge0,\qquad \delta_S=h_S-g_S\ge0.
\tag{2}
\]

Here 1/2<=h_S<=1/sqrt(2). The inset argument gives a coordinate
gap at least g_S+g_T on every center-cone comparison. The symbol
a_S in this note is a square's larger absolute side-axis component;
it is not a coefficient from the two-square weighted cap.

## 2. Four simultaneous boundary spans

The four outer chains in (1) give

\[
\begin{aligned}
 x_I-x_E&\ge g_E+2g_H+g_I,\\
 x_V-x_T&\ge g_T+2g_U+g_V,\\
 y_T-y_E&\ge g_E+2g_F+g_T,\\
 y_V-y_I&\ge g_I+2g_D+g_V.
\end{aligned}
\tag{3}
\]

The sum of the left sides is

\[
 (-x_E-y_E)+(x_I-y_I)+(-x_T+y_T)+(x_V+y_V).
\tag{4}
\]

For any physical unit square S and any signs epsilon,tau in {+1,-1},

\[
                    H_S((\epsilon,\tau))=a_S.
\tag{5}
\]

Indeed, for side components (u,v), the support is
(|u+v|+|u-v|)/2=max(|u|,|v|)=h_S+k_S; changing either
diagonal sign gives the same value. Physical containment therefore
gives

\[
 \epsilon x_S+\tau y_S+a_S\le\sqrt2\,r.
\tag{6}
\]

Apply (6) to the four actual corner squares E,I,T,V with the signs
in (4), and combine with (3). If P denotes the eight perimeter
squares E,F,T,H,U,I,D,V, the result is

\[
 \boxed{
  4\sqrt2\,r\ge
  2\sum_{S\in P}g_S+a_E+a_I+a_T+a_V.}
\tag{7}
\]

This is a physical support inequality, not a statement that the
centers or square corners form a rectangle. No sign assumption on
an individual center coordinate was used.

More generally, whenever an outer consecutive comparison in (3)
is actual in its designated coordinate, its lower bound g_S+g_T
can be increased by delta_S+delta_T. Summing any such specified
improvements strengthens the right side of (7) by their sum. Each
of the eight consecutive outer comparisons appears exactly once
in (3), so there is no double counting.

## 3. A complete orientation domain for every retained cone grid

**Theorem 1.** A retained grid (1) in the closed Q-disk cannot have

\[
                 h_S\le33/64\qquad(S\in P).
\tag{8}
\]

The orientation of the central square C is unrestricted.

To prove it, (8) gives g_S>=16/33. The function
a(h)=h+sqrt(1/2-h^2) is decreasing on [1/2,1/sqrt(2)], since
a'(h)=1-h/sqrt(1/2-h^2)<=0 in the interior. Moreover

\[
 a(33/64)=\frac{33+\sqrt{959}}{64}>\frac{999}{1000}.
\tag{9}
\]

The exact radical comparison in (9) is

\[
 959\cdot15625-3867^2=30686>0,
 \qquad \sqrt{959}>3867/125.
\]

Thus the right side of (7) is strictly greater than

\[
 8\frac{32}{33}+4\frac{999}{1000}
                    =\frac{96967}{8250}.
\tag{10}
\]

But (4sqrt(2)r)^2=1105/8, and the exact comparison is

\[
 8\cdot96967^2-1105\cdot8250^2=11730212>0.
\tag{11}
\]

Equations (7),(10),(11) contradict each other. This proves Theorem 1,
including the closed-radius boundary.

## 4. The actual entering diagonal and its source orientation

Now additionally suppose the first-birth entering comparison has

\[
       x_F-x_E=y_F-y_E=d\ge h_E+h_F.
\tag{12}
\]

It is actual in both coordinates. Only its y-gap occurs in the
outer-chain sum (3), so the directly strengthened perimeter inequality
is exactly

\[
 \boxed{
 4\sqrt2\,r\ge
 2\sum_{S\in P}g_S+a_E+a_I+a_T+a_V+\delta_E+\delta_F.}
\tag{13}
\]

The x-part of (12) supplies a second, separate constraint: the source
square cannot have h_E>=69/100. We prove this explicitly, retaining
the middle square C.

The established unary proxy bound is
|x_S|-g_S<17/16 and |y_S|-g_S<17/16. Applying it at D and T
and using F<C<D and F<T gives

\[
 x_F<17/16-g_F-2g_C,\qquad y_F<17/16-g_F.
\]

Subtract d>=h_E+h_F and use h_F+g_F>=1. With h=h_E,

\[
          x_E<1/16-h-2g_C,\qquad y_E<1/16-h.
\tag{14}
\]

Suppose h>=69/100. Put k=sqrt(1/2-h^2), X=-x_E, Y=-y_E.
Then 2g_C>=1/sqrt(2)>707/1000 and

\[
       k\le\sqrt{239}/100<31/200,
       \qquad Y>h-1/16>k.
\]

An actual corner of E has x-offset -h and y-offset either +k or
-k. Its squared norm is at least

\[
 (X+h)^2+(Y-k)^2
 >\left(\frac{4049}{2000}\right)^2
       +\left(\frac{189}{400}\right)^2
 =\frac{17287426}{4000000}.
\tag{15}
\]

All replacements in (15) decrease positive quantities: the first
coordinate uses 2h+2g_C-1/16>4049/2000, and the second uses
h-1/16-k>189/400. The exact excess over Q is

\[
 \frac{17287426}{4000000}-\frac{1105}{256}
                         =\frac{21801}{4000000}>0.
\]

This contradicts containment. Hence

\[
                         \boxed{h_E<69/100.}
\tag{16}
\]

The argument proves (16) already from the five-square directed fork
E,F,C,D,T. In the next section it is combined with the entire grid,
including both previously omitted bottom-row squares H and I.

## 5. A full-nine exclusion with E,F,C orientations unrestricted

**Theorem 2.** Under (1),(12), at least one of the six squares

\[
                         H,I,T,U,D,V
\]

has h_S>64/125. In particular the entire closed domain

\[
                 h_S\le64/125\quad(S=H,I,T,U,D,V)
\tag{17}
\]

is impossible. No small-tilt premise is made for E, F, or C.

First control the E contribution in (13). Write

\[
 m(h)=\eta(h)+a(h)
     =2h+\frac1{4h}+\sqrt{1/2-h^2}-1.
\]

On (1/2,1/sqrt(2)),

\[
             m''(h)=\frac1{2h^3}-\frac1{2k^3}\le0,
             \qquad k=\sqrt{1/2-h^2}\le h.
\tag{18}
\]

Thus m is concave on [1/2,69/100] and is bounded below by
the smaller of its endpoint values. They satisfy

\[
 m(1/2)=1,\qquad
 m(69/100)=\frac{19}{50}+\frac{25}{69}+\frac{\sqrt{239}}{100}
                          >\frac{112}{125}.
\tag{19}
\]

For the final comparison use 25/69>181/500 and sqrt(239)>77/5;
their cross-products are 12500>12489 and 5975>5929, respectively.
By (16),(18),(19),

\[
                  \eta_E+a_E>112/125.
\tag{20}
\]

The two contributions involving E and F in (13) can now be grouped
without dropping any sign:

\[
 2g_E+a_E+\delta_E=1+\eta_E+a_E>1+112/125,
 \qquad 2g_F+\delta_F=1+\eta_F\ge1.
\tag{21}
\]

Suppose (17). Each of the other six perimeter squares has

\[
                   2g_S\ge125/128.
\tag{22}
\]

For the three remaining corner squares I,T,V, monotonicity of a
also gives

\[
 a_S\ge a(64/125)>
       \frac{64}{125}+\frac{39}{80}=\frac{1999}{2000}.
\tag{23}
\]

Here the exact square check for sqrt(1/2-(64/125)^2)>39/80 is

\[
        7433\cdot6400-1521\cdot31250=39950>0.
\]

Combining (21)--(23), the right side of (13) exceeds

\[
 2+\frac{112}{125}+6\frac{125}{128}+3\frac{1999}{2000}
       =\frac{94031}{8000}>\frac{3761}{320}.
\tag{24}
\]

The last fraction is itself larger than 4sqrt(2)r, since

\[
     3761^2-1105\cdot12800=1121>0.
\tag{25}
\]

This contradicts (13), proving Theorem 2. It is a full-nine
conditional exclusion: E,F,C,D,T supplied (16), and the two other
bottom-row squares H,I occur in the retained boundary spans.

## 6. The exact orientation-deficit form and remaining scope

For later use define the nonnegative orientation deficits

\[
 e(h)=2-2g(h)-a(h),\qquad \ell(h)=1-2g(h).
\tag{26}
\]

Nonnegativity follows from their zero values at h=1/2 and
ell'(h)=1/(2h^2)>0,
e'(h)=1/(2h^2)-1+h/k>0 in the interior. Rewriting (13)
gives the necessary inequality

\[
\begin{split}
 e(h_I)+e(h_T)+e(h_V)+\ell(h_H)+\ell(h_U)+\ell(h_D)
 \ge 11+\eta_E+a_E+\eta_F-4\sqrt2\,r.
\end{split}
\tag{27}
\]

In this actual-entry branch, (20) makes its right side strictly
larger than 11+112/125-4sqrt(2)r. Equation (27) retains the
individual orientations and can be combined with other physical
constraints without an arbitrary common orientation threshold.

The established directed-fork theorem additionally forces
h_C>8/15 and makes both F--C and C--D weak. Those statements
are compatible with the present perimeter conclusions. The source
upper bound (16), the center lower bound, and the perimeter deficit
are distinct constraints; none is substituted for another.

The larger orientation domain outside (8) or (17), weak entering
diagonals, other first-birth positions, and the persistent-height-four
alternative remain to be excluded. No global actual-four extraction,
canonical-root exclusion, or unrestricted A.2 closure is claimed here.
