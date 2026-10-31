# A sharp unrestricted three-square cap at squared radius 9/2

This is a hand proof of a terminal theorem. The three squares may have
independent orientations. The theorem does not assert that an arbitrary
ten-square packing contains such a cap.

## Statement

Let Q=9/2, R=sqrt(Q), and let D be the closed disk centered at the origin.
Every closed unit square contained in D and in y>=1/2 has a horizontal
section at height z=5/4 whose intersection with [-3/2,3/2] has length at
least one. The length is strictly greater than one unless the square is
axis-parallel. The section passes through the square's interior.

Consequently three interior-disjoint unit squares in this cap must have
centers (-1,1), (0,t), (1,1), all axis-parallel, where

    1 <= t <= (sqrt(17)-1)/2.

Conversely these configurations pack the cap. In particular any disk centred
at the origin containing three such squares has squared radius at least 9/2. Four
squares cannot lie in this cap.

## Coordinates and the full section

Represent the two side axes, up to quarter turns, as either

    (a,b),(-b,a), or (a,-b),(b,a),
    a>=b>=0, a^2+b^2=1.

The center is (x,y). Put h=(a+b)/2, t=(a-b)/2, w=a+b,
d=w-1 and delta=5/4-y. The cap and top vertex imply

    1/2+h <= y <= R-h.

Since R<17/8, these bounds give |delta|<7/8-h<h. Thus the test line
lies strictly between the bottom and top supporting lines. For b>0
the full section length is

    W = min(1/a, (h-|delta|)/(a*b)).

Both quantities exceed one. Indeed a<1, and

    w-a*b = w-(w^2-1)/2 >= sqrt(2)-1/2 > 7/8.

The last strict inequality follows from sqrt(2)>11/8. Therefore
h-|delta|>w-7/8>a*b.

## Controlling clipping

Write g(Y)=sqrt(Q-Y^2), C=3/2 and Y0=3/2. The concavity of the
right semicircle and its tangent at (C,Y0) give

    g(Y0+d) <= C-d,
    g(Y0-(1-a)) <= C+(1-a).

Whenever the first expression is needed it is the lower height of an
actual square vertex, so its radical is defined. Also

    D0 := C-g(Y0+d)
       = (3*d+d^2)/(C+g(Y0+d)) >= d+d^2/3.

Let l,r be the full section endpoints. It suffices to prove

    l<1/2 and r>-1/2.

Together with W>1 these imply that the clipped section has length>1:
with no clipping use W; with one clipped endpoint use the corresponding
strict endpoint inequality; with both clipped endpoints its length is 3.
Reflection in the y-axis exchanges the two orientation forms and the
left and right endpoint inequalities, so only l needs checking.

### Positive tilt

For axes (a,b),(-b,a),

    l = max(l1,l2),
    l1 = x-(1/2+b*delta)/a,
    l2 = x+(a*delta-1/2)/b.

The top vertex P=(x+t,y+h) satisfies P_y>=1/2+w. Moreover

    1/2+w-R*b = 1/2+a-(R-1)*b > 0.

For example a>=b and R<17/8 bound this from below by 3/8.
Thus the circle support a*g(Y)+b*Y decreases for Y>=1/2+w,
above its maximizing height R*b. Since

    a*l1 = a*P_x+b*P_y-1-(5/4)*b,

the tangent bound gives

    a*l1 <= a*C-a*d+b*(w-3/4)-1.

The algebraic inequality

    b*(w-3/4) < 1-a+(3/4)*a*d <= 1-a+a*d

therefore implies l1<1/2. To prove its strict part, multiply the
difference of right and left sides by 4 and use a^2+b^2=1:

    4*E = b/(1+a) * (3+2*a-a^2-7*a*b) > 0.

Here b>0, 2*a-a^2>=3/4 for a>=1/sqrt(2)>1/2, and a*b<=1/2;
the bracket is at least 1/4.

The other edge is active only if l2>=l1, equivalently delta>=t.
This implies a=h+t<=z-1/2=3/4. The identity

    b*l2=b*P_x-a*P_y+(5/4)*a

and monotonicity of b*g(Y)-a*Y for positive Y give

    C-l2 >= D0+(a/b)*(w-3/4)
          >= (w-1)+(w-1)^2/3+w-3/4 = H(w).

Since a<=3/4, a>=b and a^2+b^2=1,
w>=w0=(3+sqrt(7))/4. The polynomial H is increasing for w>=1,
and

    H(w0)-1 = (11*sqrt(7)-26)/24 > 0,

because 121*7=847>676. Thus an active l2 is also <1/2; an
inactive l2 is bounded by l1. This proves l<1/2 for positive tilt.

### Negative tilt

For axes (a,-b),(b,a),

    l = max(m1,m2),
    m1 = x+(b*delta-1/2)/a,
    m2 = x+(-a*delta-1/2)/b.

Use the rightmost vertex P=(x+h,y+t), whose height is >=1/2+a.
The identity

    a*m1=a*P_x-b*P_y+(5/4)*b-1

and the second tangent bound imply

    a*(m1-1/2) <= b*(3/4-F(a)),
    F(a)=a+b*(1-a)/(1+a).

Set k=b/(1+a), so 0<k<=sqrt(2)-1<5/12. Substitution gives

    F(a)-3/4 = (1-7*k^2+8*k^3)/(4*(1+k^2)) > 0.

For the sign, k^2*(7-8*k) is increasing on [0,5/12], since
its derivative is 2*k*(7-12*k)>=0. Hence the numerator is at
least 1-(5/12)^2*(7-8*(5/12))=157/432>0. Thus m1<1/2.

For m2 use the top vertex P=(x-t,y+h). Circle support yields

    b*m2=b*P_x+a*P_y-(5/4)*a-1 <= R-(5/4)*a-1.

The function (5/4)*a+(1/2)*sqrt(1-a^2) is concave on
[1/sqrt(2),1], and its endpoint minimum is 7/(4*sqrt(2))>9/8.
Since R-1<9/8, this proves m2<1/2. Reflection gives r>-1/2.

## Axis-parallel case and rigidity

For b=0, y>=1 and disk containment says

    (|x|+1/2)^2+(y+1/2)^2 <= 9/2.

It follows that |x|+1/2<=3/2. The section is a unit interval wholly
in [-3/2,3/2]. It is an interior section by the strict height bounds.

For three interior-disjoint squares, the open section intervals are
disjoint: every nonendpoint of each section lies in that square's
interior. Their clipped lengths sum to at most 3. Thus each length
must be exactly 1, forcing all three squares to be axis-parallel.
The three intervals tile [-3/2,3/2], so their x-centers are -1,0,1.
For the two outside squares y>=1 and the disk inequality force y=1.
For the middle square the same inequality gives the stated range of t.
The outward corners (±3/2,3/2) force squared radius 9/2. The converse
is immediate from horizontal separation and the corner inequalities.

## Necessary condition for an unrestricted subcritical ten-packing

If ten independently oriented squares pack a disk of squared radius
q<9/2, then in every orthonormal frame at most two lie wholly in
y>=1/2 and at most two lie wholly in y<=-1/2. At least six squares
therefore meet the open strip -1/2<y<1/2.

The vertical projection intervals of these six squares have length at
least 1 and cannot contain an ordered disjoint chain of three: the
middle interval would lie between strip-interior points of the first
and third, whose distance is strictly less than 1. Thus the interval
order has height at most two. This does not supply common horizontal
separators between the actual squares. No contradiction or global
extraction theorem is claimed from this necessary condition alone.

## Provenance and trust

This adapts the analytic clipped-section argument in
[the n=9 cap manuscript](https://github.com/vltanh/lean4-squares-in-circles/blob/research/nine-tablefree-hand/research/nine/UNRESTRICTED_THREE_SQUARE_CAP.md)
on the `research/nine-tablefree-hand` branch, with new constants and the changed
inequalities proved explicitly above. The source file's Git blob at the
time of reading was `547b5bebcf9a6a0d56b04af333ab75b0208fd129`.
SymPy checked the two displayed endpoint expansions H(w0)-1 and 157/432;
those checks are not premises of the hand proof. A separate line-by-line
review within this work session checked the endpoint formulas, strict
inequalities, clipping argument, and equality cases. Lean formalization
and kernel verification have not been performed.
