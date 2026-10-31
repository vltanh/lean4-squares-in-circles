# Two unloaded pentagon ends exclude every D-owned parallel return

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed radius-free owner-interface theorem,
frozen for full independent and root review.** This completes the
same-D-axis return row left by
INNER_PENTAGON_D_OWNED_PARALLEL_RETURN_FORCES_OWNED_OPPOSITE_END.md.
The new argument excludes its remaining A-owned HA interface.

Its main geometric improvement is that the entire actual C lies
strictly above the D-to-H application, rather than merely above
the lower H corner. Full A3 and the unchanged contact chain then
put the original AB/B geometry on the wrong side of that height.
No circle equation or positive boundary coefficient is needed.

## 1. Exact original scope and complete entry

Keep the original actual unit squares and positive graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is unloaded with its entire positive degree four. A and D are
unloaded with their entire positive neighborhoods H,B,E and H,C,E.
The original B3, C3 and E2 equations and all three extra actual
units remain intact. Use the common selected physical certificate,
including its strict point normals and its compatible pre-extraction
three-singleton rule. All actual squares have disjoint open interiors.

The complete two-unloaded-end H-owner theorem excludes both H-owned
HA and H-owned HD, including actual shared sides. Suppose D owns
DH and the original DC normal is that same D axis. The complete
preceding parallel-return theorem, Sections 1--3, gives the following
unchanged chart, after a whole vertical reflection if necessary:

    D=[0,1]^2,
    F_DH=(-gamma,0) at P=(0,t),
    F_DC=(-mu,0) at Q_C=(0,s),
    F_DE=(gamma+mu,0) at Q_E=(1,u),
    gamma,mu>0,
    u=(gamma*t+mu*s)/(gamma+mu),
    0<t<u<s<=1,
    H,C subset {x<=0}, E subset {x>=1},
    max_H x=max_C x=0.                                 (1)

The D-to-H application P is a strict H vertex and a relative
interior point of the real D side. No third actual unit can
contain P: the D half-plane and H's strict quadrant leave two
remaining angular gaps each smaller than a square's right angle.

The entire actual H and its other two original applications have
the exact form

    e=(-a,-b), f=(-b,a), a,b>0, a^2+b^2=1,
    H=P+[0,1]e+[0,1]f,
    V=P+e=(-a,t-b), W=P+f=(-b,t+a),
    P_HA=V, P_HC=W,
    a<=sqrt(2)-1<1/2,
    b>sqrt(3)/2>4/5.                                  (2)

Both HA and HC strictly expose the stated H vertices. In particular
the original inward normal N of C at W satisfies

    N_y>0, N.e<0, N.f>0.                               (3)

These facts are the complete conclusions of Sections 2--3 of the
preceding source before any free-HA hypothesis is used. Their
proof keeps all H4 forces and the entire HC side-mean alternative
until that alternative is excluded. Put L=s-t, so 0<L<1.

The same source's Sections 4--5 give, for the original A-to-E force,

    (F_AE)_y>=0.                                      (4)

For clarity its literal entry here is independent of HA's owner.
Every actual AE point T has T_x>=1 and T_x<=-a+sqrt(2)<2.
If T_y>=t, the two actual A points V,T would have

    |T-V|^2>=(1+a)^2+b^2=2+2*a>2,

contrary to A's diameter. Thus T_y<t<u. The complete force-free
support-normal lemma of that source applies to the real E with
minimum-x support Q_E=(1,u), at the unchanged T with T_x<2 and
T_y<u. It gives (4) for every original AE owner and mean.

**Theorem.** The chart (1)--(4) is impossible. Consequently the
entire D-owned DH / same-D-axis DC feature is excluded for the
original two-unloaded-end pentagon, and likewise at the reflected
end. This includes all CD, DE and AB shared means and all external
frames. No whole H4_D0.L124 closure is asserted.

The preceding theorem already excludes free HA in this chart.
The H-owned alternative is excluded as above. It therefore remains
to treat actual A-side ownership of HA, which occupies Sections 4--7.

## 2. A stronger complete C-height separation

We prove directly from the original (1)--(3) that

    min_(Z in C) Z_y>t.                                (5)

This is a whole-unit statement, with every original CD support
mean and every HC owner included.

### 2.1. The entire aligned C frame

If C is aligned with D, its maximum-x support gives

    C=[-1,0] times [r,r+1].

The actual point W has -1<W_x=-b<0. Therefore an inward support
normal at W with positive y component can occur only on the lower
horizontal edge, including its actual mean. Thus r=W_y=t+a>t.
The upper edge has negative inward y component, and W cannot lie
on either vertical edge. This proves (5) at every aligned CD mean.

### 2.2. The entire tilted C frame

If C is not aligned, Q_C is its unique rightmost vertex. Write its
actual inward axes as

    u_C=(-p,-q), v_C=(-q,p),
    p,q>0, p^2+q^2=1,
    C=Q_C+[0,1]u_C+[0,1]v_C.                           (6)

The original W has coordinates relative to Q_C

    W-Q_C=(-b,a-L).                                   (7)

We cover every support feature of this unchanged square.

The right vertex Q_C is impossible because b>0. The opposite
vertex Q_C+u_C+v_C has first coordinate -p-q<-1, whereas W_x=-b>-1.
The upper vertex Q_C+v_C has inward normal cone generated by u_C
and -v_C, both with strictly negative y component. The two open
edges incident there have the same negative-y inward axes. These
features are incompatible with N_y>0 in (3).

At the lower vertex Q_C+u_C, the minimum height of C is W_y=t+a>t,
which proves (5) in that feature without any further normal choice.

On the open edge Q_C+[0,1]u_C, write W=Q_C+lambda*u_C with
0<lambda<1. Equations (7) give

    b=lambda*p, L=a+lambda*q.

Hence p>b and q<a. The whole square's minimum height is

    s-q=t+a-(1-lambda)*q>t,                            (8)

as required. Both endpoints of this edge were already considered.

The only remaining open edge is Q_C+u_C+[0,1]v_C. Its inward
normal must be N=-u_C=(p,q). At W=Q_C+u_C+lambda*v_C, the exact
coordinate equations give

    b=p+lambda*q,
    a-L=-q+lambda*p,
    L=a+(1-b*p)/q.                                    (9)

The strict original H-f support in (3) says

    N.f=-b*p+a*q>0.

Substituting b*p<a*q in (9) would yield

    L>a+(1-a*q)/q=1/q>1,

contrary to L<1. This excludes the final open edge. All four
vertices, all four sides, and all their closed normal endpoints
have now been included. Equations (5) and (8) prove the complete
stronger height separation.

## 3. The sharp actual-unit support span used below

We use the radius-free span already proved in Section 2 of
INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md.
If an actual unit K has minimum-n support at an actual point Q,
where n is unit, and v is unit with n.v<0, then

    max_(Z in K) v.(Z-Q)<=sqrt(1-(n.v)^2).              (10)

Here is the complete local justification. At a vertex Q, use the
two actual inward orthonormal axes. Their n components are
nonnegative. Both v components cannot be positive, since that
would give n.v>0. The sole possible positive component is at
most the maximum of v.r on the closed unit semicircle n.r>=0,
namely sqrt(1-(n.v)^2). At a side support, the normal displacement
has nonpositive v projection; the actual tangent interval has
length one and gives at most the absolute perpendicular v
component. This is the same displayed bound. Side endpoints and
all original weighted means are included.

No new contact or unit is introduced by using (10).

## 4. The actual A-owned frame and complete original A3 equations

Assume A owns HA. Let n be the original unit normal from H into A.
The H vertex V in (2) makes n_y<0. Its x component must be positive:
if n_x<=0, A's owned normal axis contributes nonpositively to rightward
reach from V and its one-unit tangent interval contributes at most
one. But A contains an actual AE point at x>=1, more than one to
the right of V_x=-a. This is impossible. Consequently write

    n=(c,-d), j=(d,c), c,d>0, c^2+d^2=1,
    A=V+[0,1]n+[-kappa,1-kappa]j,
    0<kappa<1.                                        (11)

The strict point convention makes V a relative interior point
of this actual A side. The full A-to-H force is -Gamma*n,
with Gamma>0. In the H frame the unit H-to-A direction is

    n=delta*e-eta*f,
    delta=b*d-a*c>0,
    eta=b*c+a*d>0,
    delta^2+eta^2=1.                                  (12)

The actual triangle A-H-B, with its A-owned AH axis, gives
F_AB.n<=0. By (4) and A's entire force equation,

    (F_AB)_y=-(F_AH)_y-(F_AE)_y<0,

since (F_AH)_y=Gamma*d>0. Therefore there are exact original
components rho>=0 and sigma>0 such that

    F_AB=-rho*n-sigma*j,
    F_AE=(Gamma+rho)*n+sigma*j.                         (13)

The second force strictly exposes A's vertex

    T=V+n+(1-kappa)j.                                 (14)

The first force's original application is

    R=V+tau*n-kappa*j, 0<=tau<=1,
    rho>0 implies tau=0.                              (15)

In the rho=0 case this is the complete original AB side-mean
interval, with both endpoints retained.

Full A3 torque about V, using every force in (13), is exactly

    sigma*(1-tau)=(1-kappa)*Gamma+rho.                  (16)

Indeed the AB moment in the orthonormal frame (n,j) is
-tau*sigma-kappa*rho and the AE moment is
sigma-(1-kappa)*(Gamma+rho); AH contributes zero at V.
No original equation has been shortened.

Because T belongs to E, (1) and (14) give

    -a+c+(1-kappa)*d>=1,
    c+d>1+a,
    c>a, d<b.                                        (17)

For the last assertion, c<=a would give c+d<1+a, since d<1;
the unit identities then convert c>a to d<b.

## 5. Every A-owned-axis AB return puts the whole B below t

First take rho=0 in (13), retaining every mean tau in (15).
The actual inward unit normal of B at R is -j=(-d,-c).
Apply (10) to B in the upward direction. Its whole upward
span from the unchanged R is at most d. Consequently

    max_B y<=R_y+d
            =t-b+(1-tau)*d-kappa*c
            <t,                                      (18)

using d<b in (17). This applies whether AB is a physical
singleton or a positive-length shared side, at every original
mean, and with no assumption about B's frame or its other forces.

But the whole C lies strictly above t by (5), contradicting the
actual BC contact. Thus rho=0 is completely excluded.

## 6. A nonaxis AB return forces a strict southwest HB normal

It remains to take rho>0. Then tau=0 in (15), and (16) gives

    sigma=(1-kappa)*Gamma+rho<Gamma+rho.                (19)

The nonnegative original AE vertical component in (4), expressed
by (13), gives

    -(Gamma+rho)*d+sigma*c>=0.

Combining with (19) yields d<c, so in particular c>1/sqrt(2)>1/2.

We first identify the entire original HB feature. The point P is
unavailable to any third unit by Section 1. The point V is likewise
unavailable to B: the A tangent half-plane at its side-interior
application and H's strict vertex quadrant leave only two angular
gaps, each smaller than pi/2. A third actual square cannot occupy
either gap. The opposite strict H vertex W cannot be an HB
application because it is opposite the strict HA vertex V and
the actual A and B touch.

Every H-owned HB axis is also impossible. The +e and -f axes
have negative dot product with the strict original HC direction
(-C,D0), C,D0>0, in the H frame, contrary to the actual H-B-C
triangle. The -e and +f axes have negative dot product with the
strict original HA direction (delta,-eta), contrary to H-A-B.
Thus the original HB strictly exposes the remaining H vertex

    Z=P+e+f=V+f,
    n_HB=x*e+y*f, x,y>0, x^2+y^2=1.                    (20)

The actual AB contact imposes a quantitative constraint on these
unchanged normals. Formula (10) at V in A, in the direction f,
gives max_A f.(X-V)<=delta. At Z in B, in direction -f, it gives
min_B f.(X-V)>=1-x. A common physical AB point therefore requires

    delta+x>=1.                                      (21)

On the other hand (12), c>1/2 and the unit identities imply

    delta+a=b*d+a*(1-c)
             <=sqrt(d^2+(1-c)^2)
             =sqrt(2-2*c)<1.                          (22)

Hence x>=1-delta>a, and therefore y<b. Returning to the world
coordinates in (2), the unchanged HB direction satisfies

    (n_HB)_x=-a*x-b*y<0,
    (n_HB)_y=-b*x+a*y<-b*a+a*b=0.                     (23)

Thus the original H-to-B normal is strictly southwest. This used
the actual AB contact and full-unit reach, not a new selected normal.

## 7. Actual B ownership contradicts its original HB application

In the current rho>0 feature all three A ports are physical
singletons at pairwise distinct actual points:

    AH at V,
    AB at R=V-kappa*j,
    AE at T=V+n+(1-kappa)j.

The AH normal is owned by A at its real side-interior point.
The two other forces in (13) are strict nonaxis A directions,
so their A supports are the displayed vertices. A strict A
support vertex makes the physical intersection a singleton.
The inequalities 0<kappa<1 make the three points distinct.

The common pre-extraction rule for an unloaded true degree-three
star with three distinct physical singleton ports therefore
excludes a free AB normal. Since this normal is not an A axis,
it is necessarily an actual B axis. This is an inherited
restriction on the unchanged common certificate; no normal is
chosen again after extracting the stress.

By (13), the actual unit inward AB normal of B has the form

    n_AB=(-k,-h), k,h>0, k^2+h^2=1,                    (24)

and is an own axis of B. The unchanged R is on its minimum
n_AB side. The other original inward normal n_HB from (23) is
also strictly southwest, so n_HB.n_AB>0. In B's actual own
coordinates a minimum-n_HB support must therefore have minimum
n_AB coordinate. Applying this to the actual HB point Z gives

    n_AB.(Z-R)=0.                                    (25)

All B side means and all its other forces remain; only its
original supporting half-planes have been used in (25).

Now the actual BC contact and (5) show max_B y>t. The sharp
upward span (10) from its original R under (24) is at most k.
Since R_y=t-b-kappa*c, this gives

    k>b+kappa*c>b,
    h<a,
    kappa*c<1-b,
    kappa*d<1-b.                                     (26)

The last inequality uses d<c. The actual vector between the
two original B applications is, by (11), (15), and (20),

    Z-R=f+kappa*j=(-b+kappa*d,a+kappa*c).

Both scalar factors b-kappa*d and a+kappa*c are positive.
Equations (24)--(26) give the strict lower bound

    n_AB.(Z-R)
      =k*(b-kappa*d)-h*(a+kappa*c)
      >b*(2*b-1)-a*(a+1-b)
      > (4/5)*(3/5)-(1/2)*(1/2+1/5)
      =13/100>0.                                    (27)

The penultimate step uses precisely a<1/2 and b>4/5 from (2).
All compared quantities have the displayed positive signs.
This contradicts the exact original support equality (25).

Thus rho>0 is impossible as well. Sections 5--7 exclude every
A-owned HA return feature in the entire chart (1)--(4).

## 8. Complete interface assembly and exact remaining scope

The already complete H-owner theorem excludes H ownership of
either unloaded end. The predecessor 708f source excludes free
HA whenever D owns DH and DC uses that same D axis. The present
proof excludes the remaining A-owned HA interface, including
every original AB mean and either possible AB owner. Hence the
entire D-owned same-axis-return row is now excluded, with all
original H4/A3/D3 equations and all physical masks retained.

The graph reflection exchanging A,D and B,C gives the identical
whole row at the other end. No circle equation, boundary-neighbor
properness theorem, shifted circle origin, external concurrence,
or additional-square placement entered the argument.

The nonparallel D-owned return rows and the remaining mixed/free
interfaces are not declared closed here. In particular this
source does not close the original whole H4_D0.L124 load family
or authorize any fine/coarse ledger change by itself.

## 9. Frozen direct sources and preservation

| Source | SHA-256 | Exact operative use |
| --- | --- | --- |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_EAST_RETURN_AND_WHOLE_H_OWNER_EXCLUSION.md | fcd6217a246b06e39ed34eb4bbd94c8e12ab47dd958cbf8de04859b2815f5d96 | Entire H-owned HA/HD exclusion in the unchanged two-unloaded-end graph |
| INNER_PENTAGON_D_OWNED_PARALLEL_RETURN_FORCES_OWNED_OPPOSITE_END.md | 708f169478c51fdda0ff8d4dff61a0d113bf88ac80c5f6fa3ab9efcaee4d47da | Complete same-axis D3 chart, full H4 corner entry, all-frame AE normal sign, and the whole free-HA exit |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Only the sharp actual-unit support-span lemma, completely restated and justified in Section 3 |
| GENERAL_UNLOADED_THREE_DISTINCT_SINGLETON_PORTS_HAVE_NO_FREE_NORMAL_SELECTION.md | 7700a4547542af9fc25b0e0b3d14f2113529069df0b007443c18d690da1137bb | Compatible pre-extraction selection at the actual full A3 with its three distinct physical singleton ports |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Original actual-triangle owned-axis obstruction and opposite strict-vertex noncontact |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Common strict point-normal convention and unchanged physical contacts |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original complete force, moment, support and shared-mean conventions |

Every original physical unit, full force, circle mask, zero individual
coefficient, shared interval and actual weighted mean remains. The
argument introduces no sampled parameter cover, numerical certificate,
post-extraction normal change, Lean edit, build, CI, metadata change,
commit or remote action. These exact bytes require full separate
independent review and root rederivation before adoption.
