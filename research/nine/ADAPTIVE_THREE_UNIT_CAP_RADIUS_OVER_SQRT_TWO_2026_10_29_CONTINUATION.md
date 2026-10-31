# A radius-adapted cap containing three units requires R at least 3/sqrt(2)

Date: October 29, 2026 UTC. Author: house continuation.

**Status: proposed complete hand theorem, awaiting full independent review
and root adoption.** The floor varies with the actual radius. This theorem
covers all actual orientations and needs no contact graph, stress, degree,
circle mask, selected supporting normal or mean. Its natural cap floor is
`(R-sqrt(2))/sqrt(2)`, including at low radii where the fixed 7/16 theorem
does not apply.

## 1. Complete statement

Let `2 <= R <= 3/sqrt(2)` and put

    C=R/sqrt(2), s=C-1, z=C-3/16,
    D_R={ (x,y): x^2+y^2 <= R^2 },
    I=[-C,C] x {z}.

**Section theorem.** Every actual closed unit square S contained in
`D_R intersect {y>=s}` has a horizontal section through its open interior
at height z. That section clipped to I has length at least one, and
strictly greater than one when S is not axis-parallel to the displayed
frame.

**Cap theorem.** If three actual unit squares with pairwise disjoint open
interiors lie in this cap, then `R=3/sqrt(2)` and all three are axis-parallel.
Their centers, ordered from left to right, are precisely

    (-1,1), (0,h), (1,1),
    1 <= h <= (sqrt(17)-1)/2.

Conversely all these equality configurations fit. Consequently, throughout
`2<=R<=sqrt(1105)/16`, the whole cap `y>=(R-sqrt(2))/sqrt(2)` contains
at most two actual units. Equality of a unit's floor with the cap boundary
is retained.

This adapts the section method of `UNRESTRICTED_THREE_SQUARE_CAP.md`, but
every required new comparison is proved below. It does not substitute new
constants into that older theorem without proof. The actual clipped line
has length `sqrt(2)*R`, strictly below three in the nine-square window.

## 2. Complete one-square section and scalar domains

Describe the actual frame of S by one of

    (a,b),(-b,a) or (a,-b),(b,a),
    a>=b>=0, a^2+b^2=1.

This changes only the description of the axes. Write its actual center
as (x,y), and put

    h0=(a+b)/2, t0=(a-b)/2,
    w=a+b, delta=w-1, Delta=z-y.

Actual containment gives

    s+h0 <= y <= R-h0.                              (1)

The exact complete scalar range is

    sqrt(2)<=C<=3/2,
    sqrt(2)-1<=s<=1/2,
    R<=3/sqrt(2)<17/8,
    z-s=13/16<5/6,
    R-z<=3/sqrt(2)-21/16<5/6.                      (2)

For the last strict comparison, square `3/sqrt(2)<103/48`; the squared
reserve is 241/2304. Equations (1)--(2) give

    |Delta|<5/6-h0<h0,                              (3)

since 2h0=w>=1>5/6. Thus this line lies strictly between the two
horizontal support lines of S, including b=0.

For b>0, its complete horizontal section has exact length

    W=min(1/a,(h0-|Delta|)/(a*b)).                   (4)

Both terms exceed one: a<1, and on 1<=w<=sqrt(2),

    w-a*b=w-(w^2-1)/2>=sqrt(2)-1/2>5/6,
    h0-|Delta|>w-5/6>a*b.

Let ell and r be its actual left and right endpoints. To show clipping
preserves a length greater than one, it suffices to show

    ell<C-1, r>1-C.                                (5)

If neither is clipped use (4); if one is clipped use (5); if both are
clipped use 2C>=2sqrt(2)>1. Reflection exchanges the two frame forms and
the endpoint inequalities. It suffices to prove the left bound in both
actual frame forms.

## 3. The exact circle tangent has slope one

Set g(Y)=sqrt(R^2-Y^2) for 0<=Y<=R. The coupled parameters give

    s+1=C, g(C)=C, g'(C)=-1.

Circle concavity gives

    g(C+delta)<=C-delta,
    g(C-(1-a))<=C+(1-a).                            (6)

Every radical used below is at a lower height of an actual contained
vertex and is therefore defined. If C+delta<=R, the exact difference
of squares further gives

    D:=C-g(C+delta)
      =(2C*delta+delta^2)/(C+g(C+delta))
      >=delta+delta^2/(2C)>=delta+delta^2/3.         (7)

Here g(C+delta)<=C and C<=3/2; the delta=0 endpoint is retained.

## 4. Positive tilt: both actual left edges

Take actual axes (a,b),(-b,a) with b>0. Direct intersection gives

    ell=max(ell1,ell2),
    ell1=x-(1/2+b*Delta)/a,
    ell2=x+(a*Delta-1/2)/b.                         (8)

The actual top vertex P=(x+t0,y+h0) has height at least s+w=C+delta.
For the first edge,

    a*ell1=a*P_x+b*P_y-1-b*z.

The unrestricted circle maximum of a*g(Y)+b*Y has height Rb. The
actual lower height is strictly beyond it, because

    s+w-R*b=s+a-(R-1)*b>=s+(2-R)*b
             >sqrt(2)-1-1/8>0.

Thus that expression decreases over all actual possible heights.
Using (6),

    a*ell1<=a*C-a*delta+b*(w-13/16)-1.              (9)

The following whole-angle inequality is sufficient:

    b*(w-3/4)<1-a+(3/4)*a*(w-1).                   (10)

For its difference E, direct expansion gives

    4E=b*(3-a)-7*a*(1-a)
       =b/(1+a)*(3+2*a-a^2-7*a*b)>0.

Indeed 2a-a^2>=3/4 since a>=1/sqrt(2)>1/2, and ab<=1/2, so the
last bracket is at least 1/4. The actual tangent coefficient one is
at least 3/4 and 13/16>=3/4. Therefore (10) is stronger than the
comparison needed in (9), proving ell1<C-1.

The second edge is active exactly when Delta>=t0. Then (1) gives

    a=h0+t0<=z-s=13/16.                             (11)

The identity b*ell2=b*P_x-a*P_y+a*z, monotonicity of b*g(Y)-a*Y
for positive Y, and (7) give

    C-ell2>=D+(a/b)*(w-13/16)
           >=(w-1)+(w-1)^2/3+w-13/16.              (12)

Since w decreases with a on this quarter circle, (11) implies
w>=w0=(13+sqrt(87))/16. The right side of (12) increases with w.
Replacing its first coefficient one by the smaller 23/24 only
weakens it. At w0 that smaller expression minus one is exactly

    (44*sqrt(87)-405)/384>0,

because 44^2*87-405^2=4407>0. Thus every active ell2 is below C-1.
If it is inactive, ell1 gives the bound. This proves the first
inequality of (5) in the full positive-tilt case.

## 5. Negative tilt: one cubic and one circle support

For actual axes (a,-b),(b,a) with b>0, the complete formula is

    ell=max(m1,m2),
    m1=x+(b*Delta-1/2)/a,
    m2=x+(-a*Delta-1/2)/b.                          (13)

Use the actual rightmost vertex P=(x+h0,y+t0), of height at least
s+a=C-(1-a). The identity a*m1=a*P_x-b*P_y+b*z-1, monotonicity of
a*g(Y)-b*Y, and (6) yield

    a*(m1-(C-1))<=b*(13/16-F(a)),
    F(a)=a+b*(1-a)/(1+a).                          (14)

Put k=b/(1+a), so 0<=k<=sqrt(2)-1<5/12 and

    a=(1-k^2)/(1+k^2),
    F(a)-13/16=(3-29*k^2+32*k^3)/(16*(1+k^2)).      (15)

The function k^2*(29-32k) increases on [0,5/12], because its derivative
is 2k*(29-48k)>=0. Hence the numerator in (15) is at least

    3-(5/12)^2*(29-32*(5/12))=121/432>0.

This proves m1<C-1 on the entire actual orientation interval.

For m2, use the actual top vertex P=(x-t0,y+h0) and circle support:

    b*m2=b*P_x+a*P_y-a*z-1<=R-a*z-1.

The function a*z+(C-1)*sqrt(1-a^2) is concave for
1/sqrt(2)<=a<=1, so its minimum is at an endpoint. Both endpoint
values strictly exceed R-1:

    z-(R-1)=13/16-(R-C)>0,
    (z+C-1)/sqrt(2)-(R-1)=1-19/(16*sqrt(2))>0.      (16)

For the first, R<17/8 and 1-1/sqrt(2)<3/10 give
R-C<51/80<13/16. For the second, 19^2<16^2*2.
Thus a*z+b*(C-1)>R-1, proving m2<C-1.

Sections 4--5 establish the left bound in (5) for both frame forms.
Reflection gives the right bound. Together with (4), every rotated
unit has clipped interior section strictly longer than one.

## 6. Parallel units, full capacity and exact equality

If b=0, the actual unit is axis-parallel and its center obeys

    y>=s+1/2,
    (|x|+1/2)^2+(y+1/2)^2<=R^2,
    y+1/2>=s+1=C.

As R^2=2C^2, this implies |x|+1/2<=C. Its section is therefore a
unit interval wholly inside I. Equation (3) already proves the line
passes strictly between its horizontal boundary sides. This completes
the section theorem at every actual orientation.

For physically interior-disjoint actual units, the relative interiors
of their horizontal sections are disjoint: nonendpoint section points
are in the actual open square interiors. Three such clipped sections
have total length at least three inside I, whose actual length is

    2C=sqrt(2)*R<=3.

Equality holds throughout. Thus R=3/sqrt(2), all units are axis-parallel,
and their unit intervals tile [-3/2,3/2]. The center x coordinates are
-1,0,1, and all center heights are at least one. At an outer unit,

    (3/2)^2+(y+1/2)^2<=9/2

forces y=1. At the middle unit the exact remaining interval is

    1<=h<=sqrt(9/2-1/4)-1/2=(sqrt(17)-1)/2.

Conversely these displayed configurations fit with disjoint open
interiors. This proves the full equality statement as well.

Finally 1105/256<9/2, with exact reserve 47/256, so the original
nine-square upper radius is strictly below the cap equality radius.
Three whole units above the natural floor are impossible throughout
that original window, including every weak floor and frame endpoint.

## 7. Caller boundary and preservation

This theorem requires a proved *whole-unit* cap. A center, contact
point, force resultant, or one chosen physical circle corner beyond
the floor does not suffice. A closing-pocket caller must prove its
actual occupied crosscut and the correct containing-circle lift.
No original house, hexagon, parent or global checkbox follows without
that literal join.

The section geometry, exact circle inequalities, all four side formulas,
and complete scalar comparisons are reproduced here. The old fixed-floor
cap theorem is methodological provenance, not an operative extra premise.
No finite geometric certificate, angle mesh, pose sample, mean change,
normal reselection, Lean/Lake command, CI, metadata edit, staging, commit
or remote action was used. Full separate independent review is required.
