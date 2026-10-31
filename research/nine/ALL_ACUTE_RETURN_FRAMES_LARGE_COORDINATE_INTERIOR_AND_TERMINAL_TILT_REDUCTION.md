# Every acute return frame has a uniform large-coordinate exclusion

Date: October 28, 2026 UTC. Author: two_circle_v_review continuation.

**Status: complete proposed continuous geometric theorem and actual
terminal-axis corollaries, submitted for full root and separate
independent review.** This removes the ordering of the two return-frame
components from a large-coordinate obstruction. It checks all four
actual corners, the whole side-parameter interval and every equality
endpoint in its stated scalar domain. It is a necessary reduction of
the remaining unique-circle V-owned interface, not a whole D02 closure.

## 1. A complete force-free all-frame theorem

Let

    x>=9/8, y>=1/2, R^2=x^2+y^2>=4,
    e,f>0, e^2+f^2=1, 0<=r<=1.

Put

    E=(1-x,y-1+r*f),
    u=(e,-f), v=(f,e),
    W=E+[0,1]u+[0,1]v.                              (1)

Assume either of these complete alternatives:

1. y<=x, with no additional scalar or upper-radius premise;
2. y>=x, R^2<=5, and

       r*e*y<=x*(1-r*f).                            (2)

**Theorem A.** Every corner of the actual W has norm strictly less
than R. Hence its whole closed square lies strictly inside D_R.

There is no ordering between e and f. The complete first alternative
in fact needs only x>=1. If e<=f, the existing ordered-frame theorem
gives the stronger threshold x>=1 in the second alternative too.
The new work below treats e>f there. Every r endpoint, y=x,
x=9/8, R^2=4 and R^2=5 is retained whenever its actual alternative
permits it. The strict e,f>0 premise is not enlarged to an aligned
frame. No force, degree, mask or physical circle contact is assumed
in the force-free theorem.

## 2. The exact four-corner deficits and the complete y<=x alternative

Write B=1-r*f in [1-f,1], so B>0. Relative to the point
Z=(-x,y), whose norm is R, the four actual corner increments are

| Corner | Horizontal increment A | Downward increment D |
| --- | --- | --- |
| E | 1 | B |
| E+u | 1+e | B+f |
| E+v | 1+f | B-e |
| E+u+v | 1+e+f | B+f-e |

The exact squared-radius deficit of each corner is

    Delta=A*(2x-A)+D*(2y-D).                        (3)

For E, x>=1, B in(0,1] and 2y>=1 give Delta>=1>0.
For E+u with y>=1, the first term is at least f^2, and
concavity on D in[1,1+f] gives a second term at least e^2.
Thus its deficit is at least one. If 1/2<=y<1, then x>sqrt(3)>3/2.
The first term exceeds (1+e)*(2-e), while the second is at least
-f-f^2. Their sum exceeds 1+e-f>0. Neither argument uses e<=f.

For E+v put A=1+f and k=r*f+e-1. Its deficit is

    Delta_01=A*(2x-A)-2y*k-k^2.                      (4)

If k<=0, the first term is at least e^2>0 and the second part
(-k)*(2y+k) is nonnegative because 0<=-k<1<=2y.
If k>0 and y<=x, then k<=j=e+f-1 and x>=sqrt(2). Consequently

    Delta_01>=2sqrt(2)*(2-e)-(1+f)^2-j^2
       >=6sqrt(2)-8+(e-(sqrt(2)-1))^2>0.            (5)

The expansion uses only e^2+f^2=1 and 2ef<=1. It does not
use an ordering of e,f.

The squared norm of E+u+v is convex in r, so its two closed
endpoints suffice. At r=0 its deficit is

    2[(x+y-2)*(1+f)+(x-y)*e]>0                     (6)

when y<=x: x+y>2 follows from x,y>0 and R>=2.
At r=1 the increments are A=1+e+f<=1+sqrt(2), D=1-e in(0,1).
Since x>=sqrt(2), both terms of (3) are strictly positive.
Convexity therefore treats every r in[0,1]. This proves the entire
y<=x alternative already at x>=1 and without an upper radius.

## 3. The E+v corner for y>=x and e>f

The ordered-frame theorem already treats e<=f. Suppose e>f,
y>=x>=1, 4<=R^2<=5, and (2). The first two corners still have
the bounds of Section 2. We now prove the remaining two corners.

Inequality (2) gives

    r<=r_*:=x/(e*y+f*x), 0<r_*<1.

Put

    L=e*y+f*x,
    K=e-1+f*r_*=e-e*y/L,
    D_0(x)=(1+f)*(2x-1-f)-2y*K-K^2.                (7)

If the actual k in (4) is positive, then K>=k>0. On positive
k, (4) decreases strictly as k increases, so D_0 is a lower
bound. If k<=0, Section 2 already gives strict positivity.

For fixed R,e,f, vary the algebraic coordinate x over
1<=x<=R/sqrt(2), with y=sqrt(R^2-x^2). Direct differentiation gives

    J=e*f*R^2/L^2,
    y'=-x/y, K'=J/y>0,
    D_0'/2=[y*(1+f-J)+K*(x-J)]/y.                  (8)

The square (e*y-f*x)^2>=0 gives

    J<=R^2/(4xy)=(y/x+x/y)/4<=5/8.

Indeed 1<=y/x<=2 follows from x>=1 and R^2<=5. Thus D_0'>0
whenever K>0. If K<=0, then K>e-1>-1 and

    D_0>=(1+f)*(1-f)+(-K)*(2y+K)>0.                (9)

The positive-K region is an interval, because K'>0. If it starts
after x=1, (9) gives its positive initial value. Otherwise only
x=1 remains to check. At x=1, y>=sqrt(3), and the exact factor is

    D_0(1)=e*y*P(y)/(e*y+f)^2,
    P(y)=2e(1-e)y^2-(2e-1)(2f-e)y-2f(f-e).        (10)

Here e>f implies e>1/sqrt(2)>1/2. For every 0<e<1,

    2e-1<e^2,
    2f(2e-1)<2f*e^2<=e,

where 2ef<=1 supplies the last inequality. Therefore

    (2e-1)(2f-e)<2e(1-e).                          (11)

Also -2f(f-e)>0. Substitution in (10) gives the whole-domain bound

    P(y)>2e(1-e)y(y-1)>0, y>=sqrt(3).

All outside factors in (10) are positive. Equations (8)--(11)
therefore prove Delta_01>0 for the complete e>f, y>=x interval,
including equality in (2). This argument needs only x>=1.

## 4. The E+u+v corner for y>=x and e>f

No torque inequality or upper-radius bound is needed for this corner.
Its squared norm is again convex in r. At r=0, (6) rewrites as

    Delta_11(0)=4(x-1)*(1+f)+2(y-x)*(1+f-e)>0.      (12)

Both terms are nonnegative and they cannot both vanish under R>=2.
At r=1 put

    A=1+e+f, D=1-e in(0,1).

If x>=sqrt(2), both terms of (3) are positive because
2x>=2sqrt(2)>A and 2y>D. Otherwise 9/8<=x<=sqrt(2), and
y>=sqrt(4-x^2). The deficit increases with y. Along this lower
circle its derivative is

    d/dx [A*(2x-A)+D*(2sqrt(4-x^2)-D)]
       =2A-2D*x/sqrt(4-x^2)>0,

because x/sqrt(4-x^2)<=1 and A>D. Thus its minimum is at
x=9/8, y=5sqrt(7)/8. Since sqrt(7)>21/8, with squared reserve
7/64, the deficit is strictly greater than

    F=A*(9/4-A)+D*(105/32-D).                       (13)

Write t=1-e. Since e>f, 0<t<1-1/sqrt(2)<3/10 and
f=sqrt(t*(2-t)). Expanding (13) gives exactly

    32F=16+97t-32t^2-(56-64t)*f.                    (14)

The two quantities 16+97t-32t^2 and (56-64t)*f are positive.
Their squared difference is

    P_1(t)=256-3168t+25857t^2-21568t^3+5120t^4.

On the whole interval 0<t<3/10, the coefficient estimate

    25857-21568t>19386>19000

gives the single completed-square comparison

    P_1(t)>256-3200t+19000t^2
           =19000*(t-8/95)^2+2304/19>0.             (15)

Both sides were positive before squaring, so (15) implies F>0.
This proves Delta_11(1)>0. Convexity treats every r in[0,1].

Sections 2--4 and the complete ordered-frame theorem exhaust every
acute frame. The squared norm of a square attains its maximum at
a corner, so the whole closed W is strictly inside. Theorem A is proved.

## 5. Literal full unique-tip geometry and its force equation

Here is an actual physical application in the remaining V-owned
return interface. Retain the original U,V,W and their true contacts,
physical masks, original normals, actual applications and all original
forces. In V's own orthonormal frame about the unchanged circle origin,
suppose its unique physical circle corner is (-X,Y), with

    V=[-X,1-X] times [Y-1,Y], X,Y>1/2,
    X^2+Y^2=R^2, 2<R<=sqrt(1105/256).

V is truly loaded of positive pair degree two, with exactly U,W as
its positive pair neighbors. U is across the actual bottom V side
and W across the actual right V side. Let their original applications be

    P=(-X+p,Y-1), Q=(1-X,Y-1+q), 0<p,q<1.

The complete loaded V2 force and torque give

    F_V=(-nu,mu)=Lambda*(-X,Y),
    mu=Lambda*Y, nu=Lambda*X, Lambda>0,
    Y*p=X*(1-q).                                   (16)

These are the original applications and magnitudes. No equation is
asserted at a higher-degree W.

The actual U axes inward from P are

    u_0=(a,-b), v_0=(-b,-a), a,b>0, a^2+b^2=1.

The actual UV and UW contacts are physical singletons at relative-
interior points of the externally owned V and W sides. Its UW
application is the actual adjacent vertex P+u_0. Both original
normals therefore strictly expose the stated U vertices. Since V owns
the original VW side normal and V,W are nonparallel, Q is W's unique
left vertex. Write the actual W as

    W=Q+[0,1](s,c)+[0,1](c,-s),
    c,s>0, c^2+s^2=1.

The original UW normal has positive horizontal component: if its
coordinates are (m_x,m_y), strict exposure at P+u_0 gives
m_y>-(b/a)*m_x and m_y<(a/b)*m_x, forcing m_x>0. Thus its only
W-axis possibilities are (s,c) and (c,-s). The minimum-(c,-s) side
lies above Q, whereas P+u_0 lies below V's bottom side and hence
below Q. That possibility is impossible. The actual UW side is
therefore the minimum-(s,c) side, and its genuine side-interior
application gives, for its original sigma in(0,1),

    P+u_0=Q+sigma*(c,-s),
    p=1-a+c*sigma, q=s*sigma-b>0.                   (17)

In particular b<s and c<a. Define the scalar r=q/s, which satisfies
0<r<1; it is not a replacement for either actual contact parameter.
Then (17) gives

    p-r*c=1-a+(c/s)*b>0.

Combining this with (16) proves the exact strict inequality

    r*c*Y<X*(1-r*s).                                (18)

The actual W now has exactly the form (1), with x=X,y=Y,e=c,f=s.
All hypotheses are literal properties of the unchanged square.

If X>=9/8, apply Theorem A according to the actual order of X,Y;
R^2<=1105/256<5 supplies the only needed upper-radius premise.
Every actual W corner would be strictly inside the circle. Thus,
whenever W is physically boundary,

    X<9/8, Y>5sqrt(7)/8>33/20.                      (19)

The last comparison uses sqrt(7)>66/25, whose squared reserve is
19/625. If c<=s, the original ordered-frame theorem strengthens
(19) to

    X<1, Y>sqrt(3).                                 (20)

Independently, Section 2 excludes Y<=X whenever X>=1. If X<1 and
Y<=X, then R^2<2, impossible. Therefore the entire surviving chart has

    Y>X.                                           (21)

These statements use only the genuine V2, actual U/W contact geometry
and physical boundary W. U and W may have arbitrary true degrees at
this stage. No terminal T, U3 or pocket allocation is needed for
(19)--(21).

## 6. A further whole-tilt restriction from the genuine terminal moment

Now impose the complete actual singleton-terminal-axis component:
an unloaded U3, a loaded boundary path V,W,...,T of three through six
units, exactly the spokes UV,UW,UT, and the compatible actual outer
order U,V,W,...,T,U. V and T retain their genuine degree two. The
other bodies retain their entire true stars and all path means.
UT is the sole U-owned spoke and physically singleton.

The full U force and torque in the chart of Section 5 give the actual
terminal normal v_0 and actual point

    P_T=P+v_0+theta*u_0,
    theta=b^2+k*a*b in(0,1), k=c/s.                 (22)

For completeness, the forces toward V and W have respectively
direction North and (s,c). Their positive sum has positive horizontal
and vertical components, so v_0 is the only possible opposing U own
axis. If their original magnitudes are mu,omega and the terminal
magnitude is tau, the unchanged horizontal force is omega*s=tau*b.
Torque about P is omega*(a*c+b*s)=tau*theta, giving (22).

The occupied U arc through P+u_0 is clockwise. Its opposite short
arc would have all outward normals in a half-plane with a strict
positive component, contradicting the full U force. The complete
true T2 torque and its actual clockwise physical boundary edge
therefore give

    det(P_T,v_0)>0,
    theta<z_1:=a*(X-p)+b*(Y-1).                    (23)

This is the original moment inequality, including the complete mean
on T's other boundary edge. It uses no false W2 equation.

For the whole range k>1, (17) gives

    0<b<s<1/sqrt(2).

Expanding the strict positive quantity z_1-theta using (17),(22)
gives

    0<aX+bY-a-b+1-2b^2-a*k*(q+2b).

Since k>1,q>0 and aX+bY<=R, it follows that

    R>(a+b)*(1+2b)-1.                               (24)

The right side increases strictly for 0<b<1/sqrt(2), because
a=sqrt(1-b^2) has derivative -b/a and

    d/db [(a+b)*(1+2b)-1]
       =(1-b/a)*(1+2b)+2(a+b)>0.

At b=3/5 its value is 52/25. But

    (52/25)^2-1105/256=1599/160000>0.

Thus the entire k>1 physical domain has

    b<3/5, a>4/5.                                  (25)

Equation (23) has a separate useful geometric consequence. On the
actual terminal U side, points have the form P+v_0+t*u_0. Their
squared norm has derivative 2*(t-z_1). Since 0<theta<z_1,
the norm decreases strictly along the whole segment from t=0 to
the actual t=theta. Therefore

    |P_T|<|P+v_0|.                                  (26)

Neither (25) nor (26) by itself excludes physical T. They are exact
necessary consequences on the whole stated component, to be used
only with their genuine terminal moment premise.

## 7. Literal original join and the remaining obligation

In original M6.B6.HEXAGON.D02.L01345 use U=2,V=1,W=0,T=3 and the
full loaded path 1,0,5,4,3. The published complete return cover gives
the V-owned g=-Jn nonparallel singleton interface with n dot m>0.
After the single rigid change to V's frame, its actual supports have
exactly the Section 5 chart. The original force and torque at the
true V2 give (16). The genuine U3 and T2 give (22)--(23).

Thus every surviving unique-physical-circle V-owned certificate
must satisfy (19),(21), together with (20) if c<=s, or (25) if c>s.
All actual W/T masks, every path mean, all individual zero weights,
the true W3 and all three extra squares remain. The original U
axes, W axes, side applications and terminal point have not moved.

These are continuous whole-domain reductions. The new theorem does
not prove closing-pocket capacity for this remaining unique V mask,
does not exclude the other W-owned return interface, and changes no
original fine or coarse flag. Its finite displayed inequalities are
analytic comparisons, not a finite pose or coefficient certificate.

## 8. Exact operative inputs and review boundary

The source hashes below are recorded after the complete new proof is
checked. The ordered-frame theorem is used only in its full actual
e<=f domain; Sections 2--4 prove every new e>f implication explicitly.
The complete original return cover supplies only the actual entry,
not the new large-coordinate inequality or a missing unique-mask exit.

| Complete source | SHA256 | Exact operative use |
| --- | --- | --- |
| PARALLEL_TIP_LARGE_X_RETURN_ALL_CORNERS_INSIDE_CIRCLE.md | 35ed0820293125307c28d2d6b0e14b841b5578517e67fa7aea90f42bb3544b35 | Complete ordered e<=f theorem at x>=1; all new unordered-frame arguments are printed above |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | True V2 and U3 force/torque, original actual side means and strict singleton support conventions |
| D02_SINGLETON_TERMINAL_AXIS_TWO_NONPARALLEL_RETURN_COVER.md | 7997a9a7eacc0aedf85801eda33b5e7a0ca2e4ce37b86b95f7cb1ba3b6c28ce9 | Exact original V-owned nonparallel remaining interface, its full U3/V2/W3/T2 and unchanged actual port geometry |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Full boundary-path endpoint moment signs and compatible occupied U arc, only in Section 6 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Degree-free physical boundary-edge moment sign used by the genuine T2 torque |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load/degree join with every one of the three extras retained |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 in the original caller |

No Lean/Lake compilation, CI/workflow dispatch, source-normal
reselection, physical mean replacement, degree truncation, original
ledger edit, commit, push or other remote action is part of this proof.
Root and separate independent full review remain required.
