# Two strict owned roofs: uniform perpendicular-interface angle reduction

**Date:** October 30, 2026. **New hand-proof reduction, not a closed original row.**
**Input PR #11 head:** 7947c0396948d13a2f37674b4fbcf4b60df7b53c.
No external script, numerical sampling, selected new force certificate, or new packing is used.
The ordinary-Lean algebraic fragment is in
`LeanDrafts/TwoStrictPerpendicularTorque.lean` (UNCOMPILED).

## Result — correct angle alternatives, with a necessary singular exception

In the literal physical-two, two-strict-inner-corner triangle of the
six-body D02 rows, assume:

* A and D are **unloaded true-degree-three hubs** with their original entire
  stars A:{V,D,B}, D:{V,A,C};
* the two positive strict V-roof contacts at P,Q are **owned by A,D**,
  respectively (genuine hub-side-interior roof points);
* the positive AD contact is a **genuine A-owned singleton** perpendicular
  to A's roof. It is *not* a shared AD segment;
* all original points, means, positive force magnitudes, physical circle
  masks, and full moment equations remain; in the D02 caller V has its full
  loaded true-two equations, and all nine physical squares remain.

Write the roof directions
    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
with c,s,C,S>0, c²+s²=C²+S²=1 and
    alpha=atan2(s,c), beta=atan2(S,C), theta=alpha+beta in (0,pi).
Put H=s*C+c*S=sin(theta)>0 and J=c*C-s*S=cos(theta).

**Theorem.** Under these hypotheses either

    (a) 0<theta<pi/4, with J>H>0,

or

    (b) theta=pi/2, with J=0 and a distinct side-mean torque equation
        at D given in Section 5.

In particular all regular sectors pi/4<=theta<pi/2 and pi/2<theta<pi
are excluded, including theta=pi/4. The theta=pi/2 exceptional sector
is NOT excluded by this theorem. It is necessary to record it explicitly;
the unrestricted claim theta<pi/4 has not been established.

The proof uses only the actual full A3/D3 stars and the triangle support
geometry, and therefore applies also to the **loaded-N row D02.L1345**
under the same local original hub/roof/AD premises. It does not apply the
unloaded N2 transmitter rule to loaded N. It proves a reusable **feature
reduction**, not a closure of L135, L1345 or C1.6.b0.

## 1. Entire physical triangle and support geometry

Fix the already proved physical-two chart

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

The A-to-V force is mu*h at P and the D-to-V force is nu*k at Q,
where mu,nu>0. Both hub-owned strict roof applications are genuine
relative-interior points of the respective maximum-h and maximum-k
sides of A and D.

Write the AD direction g from A to D. As the AD normal is perpendicular
to A's roof, it is either +e or -e. The physical triangle normal
obstruction at D requires k.(-g)>=0. But k.e=H>0, so g=+e
would give k.(-e)=-H<0. Necessarily

    g=-e,   F_AB=-mu*h+gamma*e,
    F_DC=-nu*k-gamma*e,  gamma>0.                 (1)

Here F_AB and F_DC are the actual third positive forces; they are not
shortened degree-two replacements.

Since A maximizes h at P and minimizes e at the original AD contact W,
and D maximizes k at Q and maximizes e at W, we have

    W=Q+rho*v
     =P+(s-H*rho)*h-(c-J*rho)*e.                 (2)

The identity Q-P=s*h-c*e, v=-H*h+J*e is exact. As W is a
relative-interior point of A's minimum-e side, its h-coordinate is
strictly between -1 and 0. Therefore

    -1<s-H*rho<0;   rho>s/H>0.                  (3)

Put ell=c-J*rho. P is a relative-interior point of A's maximum-h
side, so the minimum-e displacement from P to W is strictly between
-1 and 0:

    0<ell<1.                                    (4)

No AD mean is moved: W is its *original singleton application*. No
positive-length AD side is collapsed to W.

## 2. All obtuse sum angles are excluded by whole-unit support

The D roof Q is a relative-interior point of D's maximum-k side.
Since e=H*k+J*v and H>0, D's maximum-e support occurs:

* at the **positive v endpoint** of that roof side if J>0;
* at the **negative v endpoint** if J<0;
* on the entire roof side if J=0.

If J<0, (2) has rho<0 because Q lies strictly between the roof
side endpoints. This contradicts (3), rho>0. Thus J>=0.
Because 0<theta<pi, the only alternatives are

    0<theta<pi/2 (J>0), or theta=pi/2 (J=0).      (5)

In the regular case J>0, W is the positive-v endpoint of D's
maximum-k roof side, and Q is strictly inside that side. Hence

    s/H<rho<1,  0<ell=c-J*rho<1.                 (6)

The singular case J=0 must not be handled by pretending the original
D-to-C force exposes a unique D corner.

## 3. The complete D3 torque removes the entire regular wide-angle sector

For J>0 the unchanged full third force from (1) is

    F_DC=-(nu+gamma*H)*k-gamma*J*v.               (7)

Both coefficients are strictly negative, so the physical D-to-C
support is the unique original D corner

    L=Q-k+(rho-1)*v.                             (8)

Compute the full D3 moment about Q, using the original D-to-V
application Q, the original D-to-A application W, and the actual
D-to-C application L. In the positively oriented orthonormal frame
(k,v), det(k,v)=1. There is no hidden circle torque at unloaded D:

    0=det(W-Q,gamma*e)+det(L-Q,F_DC)
     =-gamma*rho*H+gamma*J+(rho-1)*(nu+gamma*H)
     =gamma*(J-H)-nu*(1-rho).                    (9)

Thus

    nu*(1-rho)=gamma*(J-H).                      (10)

The left side is strictly positive because nu>0 and rho<1; gamma>0,
so J>H. As J=cos(theta), H=sin(theta), 0<theta<pi/2,
this is precisely

    0<theta<pi/4.                                (11)

The boundary theta=pi/4 would force the positive left side of (10)
to vanish; it is excluded. Neither the radius nor the B/C/N equations
enter this contradiction, and every individual V corner coefficient
is retained.

## 4. An exact scalar reduction for the surviving regular branch

The original third A force is F_AB=-mu*h+gamma*e, with both strict
own-axis components. Its unique actual support point is

    K=P-h+(1-ell)*e.

Using the unchanged A-to-V point P, A-to-D point W and A-to-B point K,
the complete unloaded A3 torque about P is

    0=gamma*(H*rho-s)-gamma+mu*(1-ell),

hence

    mu*(1-ell)=gamma*(1+s-H*rho).               (12)

The original physical-two V2 torque is (with d from the actual radius)

    mu*(d*s+c/2)=nu*(d*S+C/2).                   (13)

Combining (10), (12) and (13), with **no division** and no choice of
new means, gives the reusable necessary polynomial identity

    (1+s-H*rho)*(1-rho)*(d*s+c/2)
      =(1-c+J*rho)*(J-H)*(d*S+C/2).              (14)

For the regular case, the complete necessary algebraic input is:
positive c,s,C,S satisfying their two unit equations; H=s*C+c*S,
J=c*C-s*S, 0<H<J; rho in (s/H,1); ell=c-J*rho in (0,1);
the exact equality (14); the original full V2 circle-force equations,
all actual support/physical mask and all nine contained units.
Equation (14) is a **necessary filter**, not an infeasibility certificate.
It may be used by a Lean-internal rational/polynomial table checker,
but no external script output is an accepted proof.

## 5. Singular theta=pi/2 is an actual distinct branch

At J=0, one has H=1 and e=k, so D's V and A return normals
are the SAME D own side axis. Its full third force is

    F_DC=-(nu+gamma)*k.

It exposes D's entire minimum-k side, **not a unique corner**. The
original mean may lie at

    L=Q-k+lambda*v,  rho-1<=lambda<=rho.

The full D torque about Q is exactly

    (nu+gamma)*lambda=gamma*rho.                 (15)

Because nu,gamma,rho>0, this places 0<lambda<rho, a value in the
allowed full side interval. Therefore the unique-corner proof of
Section 3 is inapplicable here; (15) itself yields no contradiction.
The A3 equation remains (12) with H=1, ell=c, and V2 remains (13)
with C=s,S=c.

Any future **complete** singular exclusion must use more original
information, such as the B/C loaded stars, actual channel N, physical
corner masks or whole-nine-square packing capacity. No artificial
genuine-interior mean or generic-normal perturbation is imposed.

## 6. Exact next gate and accounting

* **Regular perpendicular, 0<theta<pi/4:** use (6), (10), (12)–(14)
  together with the unchanged original B/C/N equations and the three
  physical completing units. A whole-family contradiction is still needed.
* **Singular perpendicular, theta=pi/2:** retain the full side mean
  lambda and (15); exclude using the real remaining B/C/N geometry.
* **Free strict roof with nonfree AD:** the distinct previously open
  two-strict owner feature is not covered by this owned-roof theorem.
* **Loaded N:** do not transfer the unloaded N2 side/diagonal transmitter
  equation from L135 to L1345.

Previously closed unique-V and West/strict features stay closed.
Previously excluded two-strict free-AD, both-owned-roof shared AD and
same-axis singleton AD stay at their exact scopes. There is **no new
whole original-row closure**, so the branch's original authoritative
ledger stays 37/58 coarse, 2373/2513 fine (21 and 140 open).
C1.6.b3 still has disconnected Types I and II; no complete parent proof
of that row has been found or pushed.

This is a hand derivation. Independent geometric audit, Lean/Lake
compilation, actual kernel replay and Palomar/NanoDa acceptance remain
unperformed. Do not mark a canonical gate checked from this reduction.
