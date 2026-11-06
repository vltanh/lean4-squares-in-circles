# A left endpoint bound when E lies below A

On the entire E-below-A alternative of the original Cb882 caller,

\[
                         \boxed{x_E+h_E>-\frac{11}{16}.}       \tag{1}
\]

Here h_P is the common coordinate projection halfwidth of the actual
physical square P, and g_P=1/(4h_P) is its contained aligned-inset
halfwidth. Put Q=1105/256 and rho=91/60. The proof allows corners
on the closed Q-circle, and uses no chosen physical separating axis.

The [E-down routing theorem](CB882_E_DOWN_ROUTING.md) supplies the
whole-parent bounds and the consequences of the downward order:

\[
\begin{gathered}
 |c_P|<\rho,\quad h_A<37/64,\quad g_A>16/37,\quad
 y_A-g_A<-1/4,\\
 d=x_E-x_A>0,\qquad k_0=y_A-y_E\ge g_A+g_E.
\end{gathered}                                                   \tag{2}
\]

## 1. A contrary endpoint position forces E below height -3/4

Suppose x_E+h_E<=-11/16. Write h=h_E. Since h>=1/2,

\[
 x_E\le-19/16,\qquad
 0<d<\rho-19/16=79/240<16/37<g_A.
\]

The rational reserve in the last comparison is
16/37-79/240=917/8880>0. Thus c_E lies horizontally within
A's actual contained aligned square. Since k_0>g_A, its distance
from that inset is exactly k_0-g_A. E contains an open disk of
radius 1/2, disjoint from A's open interior. Hence

\[
 k_0-g_A\ge1/2,\qquad
 y_E=y_A-k_0\le y_A-g_A-1/2<-3/4.                    \tag{3}
\]

Indeed a point of the closed inset at distance less than 1/2 could
be moved slightly into its interior while retaining that strict
distance, contradicting the physical disjointness of A and E.

Set X=-x_E and Y=-y_E. We have

\[
 X\ge11/16+h\ge19/16,\qquad Y>3/4,\qquad X>Y.       \tag{4}
\]

For the last assertion, Y>=X would give
X^2+Y^2>=2(19/16)^2>rho^2, with positive reserve
14977/28800.

## 2. Three exhaustive halfwidth intervals

Put k=sqrt(1/2-h^2). An actual corner in the outward quadrant
has offsets (h,k) or (k,h). Since X>Y and h>=k, its squared
norm is at least the latter expression. Thus containment and (4)
give

\[
 Q\ge(X+k)^2+(Y+h)^2
   >(11/16+h+k)^2+(3/4+h)^2.                       \tag{5}
\]

The function h+sqrt(1/2-h^2) is concave on
[1/2,1/sqrt(2)]. Its minimum on any closed subinterval is
at an endpoint. The following bounds are therefore valid throughout
their indicated intervals:

| Halfwidth interval | Lower bound for h+k | Endpoint comparison |
|---|---|---|
| [1/2,3/5] | h+k>35/36 | At 3/5, k>67/180 because 7/50-(67/180)^2=47/32400>0; at 1/2 the value is 1 |
| [3/5,2/3] | h+k>9/10 | At 2/3, k>7/30 because 1/18-(7/30)^2=1/900>0; the other endpoint is covered by the first row |

In the first interval, (5) gives

\[
 Q>(239/144)^2+(5/4)^2=Q+1/1296.
\]

In the second interval it gives

\[
 Q>(127/80)^2+(27/20)^2=Q+21/800.
\]

Both are contradictions. In the remaining interval
2/3<=h<=1/sqrt(2), the center bound already fails: (4) gives

\[
 |c_E|^2>(65/48)^2+(3/4)^2
          =\rho^2+1843/19200.
\]

The shared endpoints 3/5 and 2/3 are retained. These three cases
exhaust all physical E halfwidths and prove (1). Every quantity
squared above is positive; all displayed comparisons are rational.
The theorem is a necessary endpoint bound on the complete E-down
alternative, not yet an exclusion of that alternative.
