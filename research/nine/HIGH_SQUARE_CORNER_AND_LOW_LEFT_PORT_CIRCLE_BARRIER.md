# A high actual square blocks every unit chord from its upper strip to a low left port

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed force-free geometric theorem, awaiting full
independent review and root adoption. No original family gate is claimed.**

The theorem has no force, degree, selected normal, circle-load, physical
circle-contact, or mask premise. It applies to any two actual contained
unit squares, including a completing unit. All points below are points
of the same unchanged actual bodies.

## 1. Complete physical statement

Let H and B be actual closed unit squares with disjoint open interiors,
contained in the same disk about the original origin, where

    R^2<=1105/256.

Suppose the exact actual position of H is

    H=[h-1,h] x [g-1,g],
    h<=0, 37/50<=g<=1.                              (1)

Then B cannot contain both actual points P,V satisfying

    P_x<h, P_y<7/10,
    h-1<=V_x<=h, V_y>=g.                            (2)

Both horizontal endpoints for V and equality at H's top are included.
There is no assumed position or orientation for B. In particular the
theorem does not require an original selected HB edge.

## 2. The only possible physical separating axis is an oblique B axis

Put A_0=1-h>=1 and U=(-A_0,g), H's actual top-left corner.
Since the segment PV belongs to B, disjointness first forces

    P_x<=-A_0.                                      (3)

Indeed, if P_x>-A_0, the segment from V at or above H's top
to P below it would enter int H: both abscissas are at most h,
P_x<h, and after leaving a possible V endpoint at x=-A_0 or
x=h the crossing has abscissa strictly inside (-A_0,h).
Just below height g it is also above g-1. A point of B in int H
would force intersection of the two open interiors, since B is
the closure of its own interior.

Two interior-disjoint rectangles admit a separating axis parallel
to an own axis of at least one of them. This elementary rectangle
fact follows by separating the origin from the interior of their
Minkowski difference: each edge normal of that polygon is an own
axis of one rectangle. The equality/touching case uses the same
closed supporting half-plane.

No H-axis separation is possible here. If B lay wholly to the
right of H, it could not contain P_x<h. If it lay wholly above
H, it could not contain P_y<7/10<g. If it lay wholly below H,
it could not contain V_y>=g. Finally, if B lay wholly to the
left of H, it would lie in x<=h-1<=-1. The complete force-free
unit cap theorem then gives max_B y<7/10, contradicting V_y>=g.
That cap theorem covers every B orientation and is pinned in
Section 5 below.

Consequently there is a separating axis owned by B. Orient its
unit normal n from H toward B, so

    min_B(n.z)>=max_H(n.z).                         (4)

This is an auxiliary physical supporting half-plane; it is never
assigned to a pair force and changes no selected normal.

The Northeast quadrant is impossible because P lies strictly left
of h and strictly below g. The Southwest quadrant is impossible
because V lies weakly right of H's left side and strictly above
its bottom. The Southeast quadrant is impossible because V lies
weakly left of H's right side and strictly above its bottom.
The axis endpoints were already excluded. Thus the entire possible
normal is

    n=(-s,c), s,c>0, s^2+c^2=1.

Its perpendicular B axis will be t=(c,s). In these actual B
coordinates write

    B=[k,k+1] n+[ell,ell+1] t,
    H_0=U.n=A_0 s+g c>0,
    T_0=U.t=-A_0 c+g s,
    k>=H_0.                                        (5)

Equations (2)--(3) give

    P.t<T_0<=V.t.

Hence T_0 belongs to B's entire actual t interval, including the
possible endpoint when V=U.

## 3. Containment forces the oblique separator to be nearly North

The actual point (k+1)n+T_0 t belongs to the far n side of B.
Containment therefore gives

    R^2>=(k+1)^2+T_0^2
        >=(H_0+1)^2+T_0^2
         =A_0^2+g^2+2H_0+1.                       (6)

Using A_0>=1 and g>=37/50 in (6) proves

    H_0<9/10.                                      (7)

The exact strict reserve is

    19/5+(37/50)^2-1105/256=4991/160000>0.

It follows that

    0<s<1/3, c>9/10.                               (8)

For if s>=1/3, the concave function
f(s)=s+(37/50)sqrt(1-s^2) on [1/3,1] has minimum at an
endpoint. Its values satisfy f(1)=1 and

    f(1/3)>1/3+(37/50)(14/15)=128/125>1,

using sqrt(2)>7/5. Thus H_0>=f(s)>=1, contrary to (7).
Then c^2>8/9>(9/10)^2 proves the second assertion in (8).
In particular T_0<-(9/10)+1/3<0.

## 4. The original low port forces an actual far corner outside the circle

Put eta=g-7/10>=1/25. The physical P has P.n>=k>=H_0.
Resolve its original height relative to U in the actual n,t axes:

    P_y-g=c(P.n-H_0)+s(P.t-T_0)<-eta.

Consequently

    ell<=P.t<T_0-eta/s<0.                           (9)

The actual far corner Z=(k+1)n+ell t of B therefore satisfies

    |Z|^2>(H_0+1)^2+(T_0-eta/s)^2.                 (10)

The two positive terms on the right can be bounded with A_0=1
and g=37/50. For the second positive square root, write

    -T_0+eta/s=A_0 c+g(c^2/s)-(7/10)/s.

It increases with both A_0 and g. Its comparison value is positive
by (8). Hence (10) gives

    |Z|^2>
      [1+s+(37/50)c]^2+[c-(37/50)s+1/(25s)]^2
       =6221/2500+2s+(37/25)c+(2/25)(c/s)+1/(625s^2).
                                                               (11)

Since c>9/10, the ordinary arithmetic-geometric mean inequality
gives

    2s+(2/25)(c/s)
       >2s+9/(125s)
       >=2 sqrt(18/125)>3/4.                       (12)

The final squared reserve is 72/125-9/16=27/2000>0.
Dropping only the positive final term in (11) now yields

    |Z|^2>6221/2500+333/250+3/4
          =5713/1250
          =1105/256+40639/160000.                 (13)

This contradicts containment of that actual B corner. The theorem
is proved across every B frame, both V side endpoints, equality
V_y=g, and every original means that might supply P or V.

The obstruction is quantitative and concerns whole physical units.
It does not infer a virtual force at H, choose a mean, remove a
circle coefficient, or require B to touch the containing circle.

## 5. Exact operative input and verification boundary

| Source | SHA256 | Literal use |
| --- | --- | --- |
| UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md | 2b90b565591b3c9bbc30c2c1af48cf117771b96bbc58ad81441f9e99497067d6 | Its complete Section 1 force-free cap: every actual contained unit in x<=-1 has max y<7/10; no roof or force premise imported |

Every other part of the geometric proof is printed in full here.
No pose sample, angle mesh, finite exclusion packet, Lean compilation,
CI, changed normal, altered mean, deleted force, metadata edit or
remote mutation is used. A graph caller must still provide the
actual H, actual P,V in one B, and the complete hypotheses (1)--(2).
