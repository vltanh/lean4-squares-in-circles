# A high vertical slice forces a unit square outside the disk

## Lemma

Let S be a unit square, with arbitrary orientation, lying in the closed
half-plane x>=h and tangent to the line x=h. Assume

    h>=1/10,             63/100<=d<=71/100.

If its intersection with x=h+1/2 lies wholly in y>=d, then some vertex of
S has squared norm strictly greater than

    1+(d+1)^2.                                             (1)

The slice is always a nondegenerate segment. This is a one-square lemma;
no claim about independently moving several packed squares is used.
Its proof covers the full orientation interval analytically.

Choose a frame angle theta in [-pi/4,pi/4] by the right-angle symmetry of
the square. Write t=|theta|, c=cos(t), s=sin(t), L=c+s and D=c-s.
Tangency fixes its center abscissa to h+L/2. The slice requirement gives
a lower bound on its center height. Below we use vertices whose two
coordinates at that lower bound are positive. Increasing the center height
or increasing h can only increase their squared norms. We may therefore
put h=1/10 in the numerical comparisons.

## 1. Positive frame angles up to pi/6

For theta=t and s<=1/2, the slice's lower endpoint is on the edge from
the bottom vertex to the rightmost vertex. Its lower-height condition is

    p_y >= d+L/2-(s/c)(1/2-s).

The top vertex consequently has coordinatewise lower bounds

    (h+c, d+g(t)),       g(t)=s+(1-s/2)/c.                 (2)

Here g(0)=1 and g'(t)>=1/2 on 0<=s<=1/2. Indeed

    g'=c+(s-1/2)/c^2,
    c^2(g'-1/2)=c^3+s-1/2-c^2/2 >= s-s^2>=0.

The penultimate comparison uses
c^3=(1-s^2)^(3/2)>=1-(3/2)s^2, the tangent bound for that convex power.

At h=1/10, half the derivative of the top vertex's squared norm is

    -(h+c)s+(d+g)g'
      >= -(11/10)(1/2)+(163/100)(1/2)=53/200>0.

At t=0 its squared norm minus (1) is (11/10)^2-1=21/100.
The difference is therefore positive throughout this angle interval.

## 2. Positive frame angles from pi/6 to pi/4

For s>=1/2, the slice lower endpoint lies on the edge from the leftmost
vertex to the bottom vertex. Now

    p_y>=d-D/2+c/(2s),

and the top vertex is bounded below by

    (h+c, d+g(t)),       g(t)=s+c/(2s).                    (3)

The function g decreases on this interval, since

    g'=c-1/(2s^2)<0.

Its minimum is g(pi/4)=1/sqrt(2)+1/2>6/5. Also h+c>4/5.
Thus the squared norm in (3), minus (1), exceeds

    (4/5)^2+(d+6/5)^2-1-(d+1)^2
      =2/25+(2/5)d>0.

This proves the lemma for all nonnegative frame angles, including zero.

## 3. Negative frame angles: two candidate vertices

For theta=-t, the slice lower endpoint is on the edge from the leftmost
vertex to the bottom vertex. The center-height condition gives

    p_y>=d+D/2+s/(2c).

The rightmost and top vertices therefore have positive lower bounds

    V_R=(h+L, d+g_R),       g_R=D+(1/2)tan(t),
    V_T=(h+s, d+g_T),       g_T=c+(1/2)tan(t).              (4)

For t>0,

    0<g_R<1<g_T.

For example
1-g_R=s[1+s/(1+c)-1/(2c)]>0, because c>=1/sqrt(2)>1/2.
Also g_T(0)=1 and

    g_T'=-s+1/(2c^2)>0.

For the last sign use
2s(1-s^2)<=4/(3sqrt(3))<1; the maximum follows by differentiation
on [0,1], and 16<27 proves the strict numerical comparison.

The right vertex's squared norm minus (1) decreases with d, so it is
bounded below by the expression with d=71/100. The corresponding top
vertex difference increases with d, so it is bounded below by the
expression with d=63/100. Define these two lower bounds at h=1/10 as

    E_R(t)=(1/10+c+s)^2+(71/100+c-s+tan(t)/2)^2
               -1-(171/100)^2,
    E_T(t)=(1/10+s)^2+(63/100+c+tan(t)/2)^2
               -1-(163/100)^2.                           (5)

We use E_R up to t0=arctan(7/10), and E_T after that point.

## 4. Strict concavity of E_R up to t0

Put T=tan(t). Direct differentiation gives

    E_R''/2 = -(1/10)L-(71/100)D-(T/2)D
              -(1+T^2)^(3/2)
              +(71/100)T(1+T^2)
              +(T^2/2)(1+T^2)+(1/4)(1+T^2)^2.           (6)

Drop the first three nonpositive terms and use
(1+T^2)^(3/2)>=1+(3/2)T^2. It follows that

    E_R''/2 <= f(T),
    f(T)=-3/4+(71/100)T-T^2/2+(71/100)T^3+(3/4)T^4.

The derivative

    f'(T)=71/100-T+(213/100)T^2+3T^3

is positive for 0<=T<=7/10. Hence throughout that interval

    f(T)<=f(7/10)=-14879/200000<0.

Thus E_R is strictly concave. Its endpoint values are positive:

    E_R(0)=21/100,
    E_R(t0)=-1581/2000+244/(25sqrt(149))
             >976/1225-1581/2000=611/98000>0.             (7)

The comparison uses sqrt(149)<49/4, which follows by squaring.
Concavity places E_R above the chord joining its endpoint values, so
E_R>0 on the whole closed interval [0,t0].

## 5. E_T increases after t0

Both coordinates defining V_T in (4) increase with t: s'=c>0 and
g_T'>0 as proved above. Their lower bounds are positive. Consequently
E_T strictly increases on [t0,pi/4]. Its initial value satisfies

    E_T(t0)=-3373/2000+21/sqrt(149)
             >12/7-3373/2000=389/14000>0.                 (8)

Again sqrt(149)<49/4 suffices. This proves positivity on the remaining
angle interval. At least one of the two actual vertices in (4) therefore
has squared norm greater than (1) for every negative frame angle.

Sections 1--5 prove the lemma. The split at t0 joins two analytically
controlled vertex bounds; it is not a numerical cover of the angle range.
Equation (6) and the rational endpoint values were also checked
symbolically, but their displayed differentiation and sign arguments are
the proof for the entire continuous domain.
