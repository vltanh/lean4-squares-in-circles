# Negative intermediate errors paid by the fixed four-circle stress

## 1. Original owner scope

Retain the original G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
The original sorted outer states H, G, B and D have signed
tangents respectively positive, negative, negative and negative.
A, T and E may have either sign and either radial kind.

Keep original owners BT2, DE2 and EH0, and either HG0 or HG2.
At the two intermediate edges allow:

* GA2 with any error, or GA3 with nonpositive error;
* AB0 with any error, or AB2 with nonpositive error.

At TD allow TD0 with any error, or TD2 with nonpositive error.
There is no such original cycle. Multiple nonpositive
alternative owners in this statement may occur simultaneously.
No frame order is assumed.

The proof is a direct comparison of positive stresses on the
original inequalities. It does not assert that a virtual
zero-error inequality is an original separating witness.

## 2. The charged form of the fixed-stress theorem

Use
\[
 k=\frac{31}{40},\qquad l=\frac{31}{20},\qquad
 L=\frac{21}{20}.
\tag{2}
\]
The force expression \(\mathcal C\) of
[the secondary-owner four-circle theorem](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md)
uses weights
\[
                         (k,l,l,2,2,1,1).
\tag{3}
\]
Its proof gives the following slightly more general form:
\[
             \mathcal C(\mathbf d)+L\sum_i d_i>\frac7{10000}
\tag{4}
\]
whenever the positive and negative variations are each at most h,
even if \(\sum_i d_i\ne0\).

Indeed Sections 3--5 of that proof bound each charged circle
term on its entire two-error hexagon. The charge sum is only
set equal to zero in the final application to an original cycle;
none of the individual circle bounds uses that equality.
The strict zero-error reserve in its final assembly gives (4).
The bound applies to both HG owners.

For each alternative GA3 or AB2 in Section 1, write its
nonpositive error as \(-s\), with \(s\ge0\), and replace that
angular argument by zero in the algebraic secondary-owner
expression. Let \(S\) denote the sum of these one or two
nonnegative numbers. If TD2 has error \(-w\le0\), replace its
argument by zero as well; for TD0 put \(w=0\) and retain its
actual angular argument.

The resulting virtual angular vector has
\[
                 \sum_i d_i^{\mathrm{virt}}=S+w.
\tag{5}
\]
Deleting negative errors can only reduce negative variation
and leaves positive variation unchanged. Thus its variations
still lie in the domain of (4), and
\[
         \mathcal C(\mathbf d^{\mathrm{virt}})
             >\frac7{10000}-L(S+w).
\tag{6}
\]

## 3. A negative AB2 error

Let the original AB2 error be \(-s\), and give that actual
inequality the positive multiplier
\[
                              p=l\sec s.
\tag{7}
\]
Retain every other multiplier for now. Write \(y_A\) for A's
actual signed tangent and write B's tangent as \(-b_B\).
Its original projection and the corresponding virtual
zero-error AB0 projection are
\[
 P_{AB2}=-a_A\sin s+y_A\cos s+b_B,
 \qquad P_{AB0}^{\mathrm{virt}}=y_A+b_B.
\tag{8}
\]
Hence
\[
 pP_{AB2}-lP_{AB0}^{\mathrm{virt}}
       =-l a_A\tan s+(p-l)b_B.
\tag{9}
\]
The \(y_A\) terms cancel exactly, regardless of its sign.
The difference of the two demands is \(pW(s)-l\), where
\[
                         W(s)=\frac{1+\cos s+\sin s}{2}.
\]
Thus the change in demand minus projection is
\[
 l\left\{(a_A+\tfrac12)\tan s
                 +(\tfrac12-b_B)(\sec s-1)\right\}.
\tag{10}
\]

Every canonical boundary state has \(a_A>447/800\), while
\(b_B\le c_0<.9\). The primary bound follows directly from
the outer arc and the true-core boundary: on the curved core
part, sorting gives
\[
 a_A\ge\frac12+\frac1{12\sqrt2}>\frac{447}{800},
 \qquad
 \frac1{288}-\left(\frac{47}{800}\right)^2
                          =\frac{119}{5760000}>0;
\tag{11}
\]
the flat part has \(a_A=7/12\). Consequently (10) is at least
the common lower bound
\[
 lJ(s),\qquad
 J(s)=\frac{847}{800}\tan s-\frac{183}{200}(\sec s-1).
\tag{12}
\]
The coefficient \(183/200=.915\) is deliberately large
enough to cover the next case as well.

## 4. A negative GA3 error

Give an original GA3 error \(-s\) the multiplier \(p=l\sec s\).
The relevant original and virtual projections are
\[
 P_{GA3}=a_G-a_A\sin s-y_A\cos s,
 \qquad P_{GA2}^{\mathrm{virt}}=a_G-y_A.
\tag{13}
\]
Their weighted difference is
\[
 pP_{GA3}-lP_{GA2}^{\mathrm{virt}}
       =(p-l)a_G-l a_A\tan s.
\tag{14}
\]
Again the actual signed tangent cancels. The resulting
demand-minus-projection gain is
\[
 l\left\{(a_A+\tfrac12)\tan s
                 +(\tfrac12-a_G)(\sec s-1)\right\}.
\tag{15}
\]
Since
\[
 a_G\le a_0=\sqrt{Q-\tfrac14}-\tfrac12<1.415,
\tag{16}
\]
equations (11), (15) give the same lower bound \(lJ(s)\)
as (12). The square comparison proving (16) is
\((1.915)^2>Q-1/4\).

If both GA3 and AB2 occur with nonpositive errors, use their
two separate secant multipliers. Equations (9), (14) are
differences from the respective virtual inequalities, so
their gains add exactly. In particular no uncancelled A
tangent is introduced by making both comparisons.

## 5. The negative-intermediate gain exceeds its angle charge

For \(0\le s\le h\),
\[
                   \tan(s/2)<\frac{183}{500}
                  \quad\hbox{when }s>0.
\tag{17}
\]
Monotonicity reduces this to \(s=h\). The explicit alternating
Taylor comparison is
\[
 \frac{183}{500}C_6(7/20)-S_5(7/20)
              =\frac{7007815411}{7680000000000}>0.
\tag{18}
\]
Use \(\sec s-1=\tan s\,\tan(s/2)\) and \(\tan s\ge s\).
The bracket below is positive, and
\[
 \begin{split}
 lJ(s)
 &\ge l\left\{\frac{847}{800}
              -\frac{183}{200}\frac{183}{500}\right\}s\\
 &=\frac{1121983}{1000000}s
  =Ls+\frac{71983}{1000000}s.
 \end{split}
\tag{19}
\]
This comparison is valid at \(s=0\) too. Thus each negative
intermediate owner change pays its complete charge in (6),
with an additional positive reserve whenever its error is
nonzero.

## 6. A nonpositive TD2 error

If the original TD owner is 2 with error \(-w\le0\), retain
its multiplier 2. Its projection differs from the virtual
zero-error TD0 projection by
\[
             -a_T\sin w+y_T(\cos w-1).
\tag{20}
\]
The original sorting inequality \(a_T\ge|y_T|\), together
with \(a_T>1/2\), gives
\[
 2\{-a_T\sin w+y_T(\cos w-1)\}
 \le-2a_T(\sin w+\cos w-1)
 \le-(\sin w+\cos w-1).
\tag{21}
\]
The demand gain is
\(2(W(w)-1)=\sin w+\cos w-1\). The complete stress gain is
therefore at least
\[
                         2(\sin w+\cos w-1).
\tag{22}
\]
This is at least \(Lw\), and is strictly greater for \(w>0\).
Indeed the function in parentheses is concave and vanishes
at zero, while
\[
 \begin{gathered}
 C_6(h)+S_7(h)-1.409
                         =\frac{420061}{7200000000}>0,\\
 \frac{2(.409)}h-L=\frac{83}{700}>0.
 \end{gathered}
\tag{23}
\]
This is the same signed-core-independent comparison used
for nonpositive TD2 error in the complete TD2 theorem.

## 7. Strict contradiction

Apply the modified positive multipliers to the actual
original separating inequalities. Their total demand minus
projection must be nonpositive.

On the other hand, compare them with the virtual preferred
expression at the same original centers. The exact changes
(10), (15), (22), followed by the four original outer-circle
support bounds, make that total greater than
\[
 \begin{split}
 &\frac7{10000}-L(S+w)
          +\frac{1121983}{1000000}S+Lw\\
 &\hspace{20mm}
   =\frac7{10000}+\frac{71983}{1000000}S>0.
 \end{split}
\tag{24}
\]
This contradiction proves the full scope in Section 1.
Every change was a comparison inside the dual expression;
the argument never assumes a new separating axis or a
feasible deformation of the cycle.
