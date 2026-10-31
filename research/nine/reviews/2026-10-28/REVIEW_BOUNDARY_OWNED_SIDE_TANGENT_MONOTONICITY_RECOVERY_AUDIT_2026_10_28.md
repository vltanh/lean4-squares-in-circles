# Independent complete review of the boundary owned-side tangent theorem

Date: October 28, 2026. Reviewer: recovery_audit.

**Verdict: PASS, complete at the printed force-free and arbitrary-full-star
scope.** I read the entire new source and independently rederived all its
geometric cases, strict reserves, physical-mask implication and full-star
projection. This is a fresh review of these exact new bytes, not inherited
acceptance from an earlier draft or a historical checkpoint.

Reviewed source:

    BOUNDARY_PAIR_OWNED_SIDE_TANGENT_MONOTONICITY.md
    bytes: 9179
    SHA-256: e780594b818d44ceceb26c93aae229c243b736a328f289fdef474f0d08e6db4d
    Git blob: d810f7ed87af784ddc501f7ec94c2fd07261519a

The source is self-contained and has no direct mathematical input table.
I requested no changes to its bytes. The review changes no original
fine/coarse ID or gate, source, force system, physical square or metadata.

## 1. Complete positive-inner-corner check

For K=[N,N+1]x[B,B+1], N,B>0, its farthest corner gives

    R^2=N^2+B^2+2(N+B)+2.

Let an actual neighboring unit L have P=(N,B) as its minimum-g support,
where g=(-u,-v), u,v>0 and u^2+v^2=1. At a vertex P of L, its two
actual inward axes r,s satisfy g.r,g.s>=0. Neither can have both
displayed coordinates positive. Since each has length one,

    P.r<=max(N,B), P.s<=max(N,B).

Thus each adjacent L corner has squared norm at most
|P|^2+1+2max(N,B), with strict reserve 1+2min(N,B) below R^2.

For w=r+s, orthogonality gives |w|^2=2. The nonnegative components
of g in this frame have squared sum one, hence g.w>=1. If w_x+w_y
were positive, at most one coordinate of w could be negative, and
its absolute value would be less than one. Discarding the nonpositive
contribution of the positive coordinate would then give g.w<1,
a contradiction. Therefore w_x+w_y<=0.

Writing w=alpha(1,1)/sqrt(2)+beta(1,-1)/sqrt(2) gives alpha<=0
and alpha^2+beta^2=2. Consequently

    P.w=((N+B)alpha+(N-B)beta)/sqrt(2)<=|N-B|.

The opposite L corner has squared norm at most |P|^2+2+2|N-B|,
with strict reserve 4min(N,B)>0. The corner P itself is also strictly
inside. Convexity of squared norm then puts every actual point of L
strictly inside the same circle.

I checked the complete side-support continuation separately. Its exact
pose is P+[0,1]g+[-rho,1-rho]Jg, rho in[0,1]. Every individual corner
is affine in rho. At either endpoint the vertex-support proof applies
to that endpoint pose, with the same strict bounds. Convexity therefore
gives strict containment for every original intermediate rho. This
is an analytic bound over a continuous pose parameter; it does not
replace an original force mean or move the actual packing.

Both side endpoints, either permitted L support axis and every possible
relative L orientation are covered. The proof uses no force, circle
coefficient, degree, upper-radius assumption or nonoverlap relaxation.

## 2. Exhaustion of all forbidden negative tangent normals

The main statement has actual own coordinates

    K=[N,N+1]x[B,B+1], N>0, B>=-1/2,
    R^2=(N+1)^2+(B+1)^2, R>1.

The farthest-corner identity remains valid at B=-1/2, when both
far-normal-side corners physically touch the circle. The premise
det(p,g)>0 concerns the real support application about the unchanged
circle origin, for every original side mean.

Suppose g_j<0. I checked all three possible signs of g_n.

1. If g_n>0, put g=(u,-v), u,v>0, A=N+1. Its actual K support is
   p=(A,B). The positive determinant implies B<0 and
   0<q=v/u<-B/A. The support height is
   h=(A-Bq)/sqrt(1+q^2); its derivative on the entire comparison
   interval is (-B-Aq)/(1+q^2)^(3/2)>=0. Hence h>=A.
   Since -1/2<=B<0, A>sqrt(R^2-1)>R-1. Every actual unit on the
   other side has width at least one in the g direction, so its
   containment would require h<=R-1. This is a strict contradiction.
2. If g_n=0, the normal is (0,-1), and every actual support point
   has p_n>=N>0. Its moment is -p_n<0, including all side means.
3. If g_n<0, put g=(-u,-v). Its unique actual support is (N,B).
   Positive moment Bu-Nv>0 forces B>0. Section 1 then puts the
   whole actual L strictly inside the circle, contradicting that
   L is a physical boundary unit.

This covers every normal with g_j<0. The allowed conclusion is exactly
g_j>=0. No step unjustifiably strengthens it to a strict inequality.
The only radius comparison in this complete proof is R>1; no upper
bound is hidden in the inner-corner argument.

## 3. Full physical mask and arbitrary-degree projection

For an actual owned inward normal n with minimum support N>0, all
physical circle corners lie on the far normal side. The near-side
corner with the same tangent coordinate has squared norm smaller by
2N+1>0. If the center tangent coordinate B+1/2 were negative, every
physical circle corner would have the strictly negative tangent
coordinate B. Any nonzero nonnegative combination F of those real
corners would therefore have F.j<0.

Thus F.j>=0 implies B>=-1/2, and the force-free theorem applies.
At B=-1/2 it preserves both physical circle corners and either zero
individual coefficient. The proof does not replace F by the center,
restrict the physical mask, or assume a nonzero weight at each corner.

For the complete original positive neighborhood, the source retains
every incoming term lambda_i m_i, every outgoing boundary term
mu_k g_k and the exact full equation

    F+sum mu_k g_k-sum lambda_i m_i=0.

Assuming F.j>0 supplies the physical-mask premise just checked.
Each outgoing boundary contact with det(p_k,g_k)>0 then has
g_k.j>=0, whereas every retained incoming term has m_i.j<=0.
The full tangent projection gives F.j<=0, contradicting the
assumption. This proves the asserted F.j<=0 without a degree bound,
without a two-force substitution and without constructing a grouped
mean. An owned incoming n term simply has tangent component zero.

I also checked the reflected version: reflecting the actual chart
reverses both oriented tangent coordinates and determinants. Incoming
components >=0 with negative outgoing moments consequently give
F.j>=0. No physical load roles or squares need to be exchanged.

## 4. Accepted scope and caller obligations

The force-free theorem applies to actual physical boundary contacts
at arbitrary true degrees, with original full means, all support owners
and all physical masks. The full-star corollary applies to any complete
neighborhood satisfying its explicitly stated directional hypotheses.
The proof does not supply those hypotheses for an arbitrary packing.

In particular a caller must prove N>0 relative to the original circle
origin, establish the actual directed boundary-contact moments, and
retain every true-star term. A coordinate translation to a contact
cannot be used to infer N>0. These limitations are correctly stated
in the source and remain part of this approval.

No whole original family is closed by this generic review. The separate
H4 D-owned/nonaxis caller has its own complete review. No Lean run,
CI, pose sample, numerical certificate, remote mutation or ledger edit
was used in this hand audit.
