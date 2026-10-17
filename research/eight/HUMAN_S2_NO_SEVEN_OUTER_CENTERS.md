# The all-single-side S2 pattern cannot have seven outer centers

## Theorem (entire S2/k=7 macro-case eliminated)

Let eight unit squares, each of completely arbitrary orientation,
have pairwise disjoint open interiors in a disk centered at zero
with squared radius

    q<=q_plus=9789/2500.

Let C be the unique origin-containing square. Suppose its
seven exterior squares each have **exactly one** available
central-owned whole-square side separator, and that their
opposite-side population type is

    S2=(3+0,2+2).

Then **the seven exterior centers cannot all have norm >=1**:

    **S2 => k<=6.**                                    (1)

This is a complete elimination of the S2/k=7
combination, with **no central-center offset
exception** and no common-frame, selected contact,
physical stress or numerical-search hypothesis.

It strictly strengthens the earlier partial
HUMAN_S2_SEVEN_OUTER_CENTER_BAND.md result, which
excluded this branch only when the signed central
coordinate on the 2+2 axis had |t|>=1/8.

## 1. Whole-cap polar elevation from the exact square envelope

Normalize the S2 statuses by rotations/reflections:

    R:3, L:0, U:2, D:2.

Write the central square center as (a,t). Then the
two upper/lower outward cap offsets are

    h_U=1/2+t,       h_D=1/2-t,

and their exact opposite 2+2 capacity bound gives

    |t|<5/24.                                         (2)

Every U-square center has positive y coordinate
and every D-square center has negative y coordinate.
Every R-square center has positive x coordinate.

Recall two already proved arbitrary-frame facts.

**Exact one-square cap envelope** (HUMAN_ONE_SQUARE_CAP_ENVELOPE.md):
if a complete unit square is in D_R and wholly in
{y>=h} for h>=2/5, its center p=(x,y) satisfies

    y>=h+1/2,
    |x|<=sqrt(q-(1+h)^2)-1/2.                       (3)

**Universal center radius** (farthest-vertex formula):
all square centers have

    |p|<r0:=283/200,                                (4)

because r0^2+r0+1/2=156689/40000 >
q_plus=156624/40000.

We measure a center's **polar elevation** alpha
from the nearer horizontal half-axis, between
0 and pi/2. A U-center with
y>0 and y/|x|>tan(alpha) has polar angle
theta_U in (alpha,pi-alpha).
A D-center with y<0 and |y|/|x|>tan(alpha)
has angle theta_D in (-pi+alpha,-alpha).

We prove that the U and D populations have
lower polar elevations alpha_U,alpha_D satisfying

    alpha_U+alpha_D>pi/2+3/250.                 (5)

The chosen elevations are determined only by
their *whole-square cap offsets*, not
their frames or center sign of x.

## 2. Moderately centered 2+2 axis: |t|<=1/10

The farther of the U,D sides has offset

    h_far=1/2+|t|>=1/2,

and the nearer has

    h_near=1/2-|t|>=2/5.

On the **farther** side, (3) and q<=q_plus give

    |longitudinal center coordinate|
       >=h_far+1/2>=1,

    |transverse center coordinate|
       <=sqrt(q_plus-(3/2)^2)-1/2
       < 4/5.                                        (6)

The last inequality is the exact rational square
comparison q_plus-9/4=4164/2500 <
(13/10)^2=4225/2500.
Thus every far-side center has polar elevation

    > atan(5/4).                                    (7)

On the **nearer** side, likewise,

    |longitudinal|>=2/5+1/2=9/10,

    |transverse|
       <=sqrt(q_plus-(7/5)^2)-1/2
       < 9/10,                                      (8)

because q_plus-(7/5)^2=4889/2500 <
(7/5)^2=4900/2500.
Hence every near-side center elevation is

    > atan(1)=pi/4.                                (9)

The two elevations, whichever one belongs to
U or D, therefore obey

    alpha_U+alpha_D
       >atan(5/4)+pi/4
       =pi/2+atan(1/9).                             (10)

The equality follows from the tangent subtraction
formula for atan(5/4)-pi/4, whose tangent is

    [(5/4)-1]/[1+(5/4)]=1/9.

For 0<x<1, atan(x)>x/2. Thus

    atan(1/9)>1/18>3/250,

proving (5) in this central band.

## 3. More displaced 2+2 axis: 1/10<|t|<5/24

Now

    h_far>3/5,          h_near>7/24.             (11)

For the farther side, (3) is available,
and gives

    |longitudinal|>3/5+1/2=11/10,

    |transverse|
       <=sqrt(q_plus-(8/5)^2)-1/2
       < 2/3,                                        (12)

because q_plus-64/25=3389/2500 <
(7/6)^2=49/36; the latter is the
integer inequality 3389*36=122004<122500=49*2500.

Consequently the far center elevation is

    >atan((11/10)/(2/3))=atan(33/20).           (13)

For the nearer side, h_near<2/5 may hold,
so we must **not** apply (3) outside its
proved domain. Instead use just its
whole-side center projection and (4):

    |longitudinal|>7/24+1/2=19/24,
    |p|<283/200.                                    (14)

The sine of the near center elevation is
at least (19/24)/(283/200)=475/849,
strictly. Since

    13*(475)^2-4*(849)^2
      =49921>0,                                     (15)

we have

    475/849 >2/sqrt(13)
             =sin(atan(2/3)).

Both elevations lie in (0,pi/2), where
sine increases, so every near-side
center elevation is

    >atan(2/3).                                     (16)

Summing (13),(16) gives

    alpha_U+alpha_D
       >atan(33/20)+atan(2/3)
       =pi/2+atan(6/139).                           (17)

To verify the identity, the tangent product
(33/20)*(2/3)=11/10>1, so the sum is
above pi/2, and its excess tangent is

    [(11/10)-1]/[(33/20)+(2/3)]
       =(1/10)/(139/60)=6/139.

Again atan(x)>x/2 on (0,1), giving

    atan(6/139)>3/139>3/250.

This proves (5) also in the displaced band.
No angle mesh or unproved global square
cap extension was used.

## 4. Seven outer-center rays cannot fit the resulting arc

The hand theorem HUMAN_STABLE_OUTER_ANGLE.md
supplies, for any **two distinct outer centers**
in this exact disk range, smaller angular gap

    >delta0:=pi/4-1/500.                             (18)

From (5), all U-center rays lie in
(alpha_U,pi-alpha_U), while all D rays
lie in (-pi+alpha_D,-alpha_D).
All R rays have positive x and so lie
in (-pi/2,pi/2). Therefore all seven
exterior center rays lie in one
ordinary, nonwrapping interval

    (-pi+alpha_D, pi-alpha_U)

of total width

    W=2*pi-(alpha_U+alpha_D)
       <3*pi/2-3/250
       =6*(pi/4-1/500)=6*delta0.               (19)

If all seven exterior centers were outer,
sort their seven ray angles in this interval.
The six successive **linear** differences
would each exceed delta0: for differences
<=pi use (18), and for differences >pi
the assertion is immediate. Their sum
would exceed 6*delta0, contradicting
the enclosing width bound (19).

Thus at least one exterior center has
norm <1, proving S2/k=7 impossible. QED.

## 5. Branch implications and honest scope

In the full n=8 finite taxonomy,
S2=(3+0,2+2) has only the outer-center
subbranches

    **k=3,4,5,6**;    k=7 is eliminated.

Further already hand-proved restrictions
apply to those survivors:
* S2/k=3 requires triple-side offset <7/50
  and signed center coordinate |t|>1/10
  along the 2+2 axis.
* S2/k=4 is excluded when the triple-side
  offset is >=7/50 and |t|<=1/10.

This theorem removes an entire
contact-graph/center-count macro-case,
not merely a subinterval. It does not
reject all S2 packings, and it does not
apply automatically to status branches
that have an L-side square or an own-axis
corner exception. The sharp candidate
has S4 statuses, so its valid k=7
outer-contact realization is untouched.

The missing unrestricted lower bound
R8>=Rhat remains OPEN.
