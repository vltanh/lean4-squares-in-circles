# A fixed interior segment in the original left main square

November 2, 2026. Complete hand proof for the unchanged `001/00` domain.
The rational constants were checked first and the argument was independently
reviewed by the weak-outer hand agent. No Lean, Lake, or CI. This is a
necessary geometric consequence, not a whole-mask closure.

Let the main originals be A,B,C,D and retain both actual links A/B and B/C,
the original C/D cone comparison and physical nonoverlap, and containment
in the closed disk of radius `r=sqrt(1105/256)`. Write the original
coordinate halfwidth and contained aligned-inset halfwidth as

\[
 h_S\in[1/2,1/\sqrt2],\qquad g_S=\frac1{4h_S},\qquad h_S+g_S\ge1.
\]

No transverse sign, endpoint order, short-chain condition, or bound on the
two unselected originals is required for this result.

## 1. The two actual links constrain the original A width

The C/D cone and the two contained aligned squares give
`x_D-x_C>=g_C+g_D`. Containment of the original D gives `x_D+h_D<=r`.
Consequently

\[
 x_C-h_C\le x_D-(h_C+g_C)-g_D
          \le r-1-(h_D+g_D)\le r-2.                 \tag{1}
\]

The two actual original links give

\[
 x_A+h_A+2h_B\le x_C-h_C.
\]

Combining this with (1), `h_B>=1/2`, and the original left containment
`x_A-h_A>=-r` yields

\[
 -x_A\ge3+h_A-r,
 \qquad h_A+h_B\le r-1.
\]

Since `r<133/64`, these imply

\[
 h_A<37/64,\qquad g_A>16/37,\qquad
 -x_A+g_A\ge3-r+h_A+g_A>123/64.                   \tag{2}
\]

In particular A is on the negative horizontal side. Every inequality
retains A's same original width and center.

## 2. Its inset crosses the horizontal axis with uniform clearance

Suppose, for contradiction, that `|y_A|>=g_A-3/40`. The corner of A's
contained aligned inset that is farthest to the left and has the larger
absolute vertical coordinate has squared norm

\[
 (-x_A+g_A)^2+(|y_A|+g_A)^2
 >\left(\frac{123}{64}\right)^2+
   \left(\frac{32}{37}-\frac3{40}\right)^2.
\]

Both quantities squared are positive. Direct rational arithmetic gives

\[
 \left(\frac{123}{64}\right)^2+
 \left(\frac{32}{37}-\frac3{40}\right)^2-Q
 =\frac{151929}{140185600}>0.
\]

That inset corner belongs to the original physical A, so it cannot lie
outside the containing disk. Therefore

\[
                         \boxed{g_A-|y_A|>3/40.}       \tag{3}
\]

This proves that every point of the vertical interval `[-3/40,3/40]`
lies strictly between the horizontal sides of A's aligned inset.

## 3. A fixed segment, with no moving marker

The universal center bound `|c_A|<91/60` and (2) imply

\[
 x_A+g_A>-\frac{91}{60}+\frac{16}{37}
         =-\frac{2407}{2220}>-\frac{11}{10}.
\]

Also `-x_A>=3+h_A-r>91/64`, so

\[
 x_A-g_A<-\frac{91}{64}-\frac{16}{37}<-\frac{11}{10}.
\]

Together with (3), both strict horizontal inequalities prove

\[
 \boxed{\ \{(-11/10,y): |y|\le3/40\}
                \ \subset\operatorname{int}(A).\ }   \tag{4}
\]

The aligned inset is a subset of the unchanged original square. A point
strictly inside that inset has a neighborhood contained in A, so (4)
asserts interior containment in the physical square itself.

An original packing square distinct from A cannot contain an interior
point of this segment in its own interior. Turning this observation into
an order or capacity theorem still requires a complete argument; no such
additional conclusion is assumed here.

The companion `computer_assisted/verify_weak_outer_left_main_inset_barrier.py`
checks the displayed rational comparisons. This result leaves all
whole-mask, positional-root, and global proof counts unchanged.
