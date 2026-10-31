# Every physical triangle body meets its full external-resultant ray

Date: October 27, 2026.

**Status: accepted complete hand strengthening after full-source root and
separate independent reviews in
REVIEW_TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY_ROOT_2026_10_27.md and
REVIEW_TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY_HEXAGON_2026_10_27.md.**
This finishes the parallel alternative of the general triangle ray lemma.
It changes no existing proof or gate by itself.

## 1. Entire original local scope

Let K,U,V be an actual positive triangle of three original
interior-disjoint unit squares in the containing circle, with

    79/40<=R<=sqrt(1105)/16.

At each body retain its full external force system, including every
circle force and every actual attached positive pair force. Assume
each such complete external aggregate has zero origin moment. Keep
all original force and torque equations, every physical corner mask,
individual zero weight, actual normal and shared-side mean. There is
no degree or boundary-load assumption on any triangle body.

At K write its two actual outward triangle normals n_1,n_2,
their positive magnitudes mu_1,mu_2, and

    N=mu_1 n_1+mu_2 n_2.

Its full external resultant is F_K=-N. The actual external-resultant
theorem makes this vector nonzero.

**Theorem.** The actual closed K meets the nonnegative ray of its
full external resultant:

    K intersect {t F_K:t>=0} is nonempty.                 (1)

This concerns the same aggregate occurring in the original K
equation. No branch force is identified with it until any possible
own circle force and other attachments have been accounted for.

## 2. The full zero-moment and nonparallel reductions

Suppose instead K avoids the whole ray {-t N:t>=0}. The complete
triangle ray lemma in
TWO_TRIANGLE_TIP_LEAVES_D_TYPE_EXCLUSION.md, Section 1, applies
exactly at this local scope. Its proof is independent of the later
D-leaf caller. It first excludes zero common cycle moment in both
parallel/nonparallel K cases, using actual proper ports at the other
nonparallel bodies. If K were nonparallel, positive radial concurrence
would give q_K=-tau N with tau>0 and all its proper original ports.
ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md then excludes
that case at the full arbitrary-neighbor-degree scope.

The remaining conclusion of the accepted general ray lemma is

    n_1=n_2=m, with m an actual K side axis,
    h=h_K(m)>0,       h m belongs to K.                  (2)

The nonzero common cycle moment makes its actual ports distinct;
their positive weighted mean is exactly h m. This keeps every
original side mean rather than choosing a new application.

## 3. Avoiding the ray forces that whole side beyond height one

In K's actual m,Jm axes, its m interval is [h-1,h]. The point h m
in (2) says its transverse interval contains zero. If h<=1, the
positive height h would make [h-1,h] contain zero as well, so O
would belong to K. But O belongs to the forbidden ray. Therefore

    h>1.                                                (3)

This is the additional implication beyond the prior h>0 conclusion.
It includes original mean endpoints and transverse zero endpoints,
because the excluded ray and K are both closed.

## 4. The two unchanged neighboring units cannot fit in that cap

Both actual neighbors U,V lie beyond the same support m.x>=h.
Every unit has projection halfwidth at least 1/2, so each actual
center c satisfies

    c.m>=h+1/2>3/2.

The sharp contained-unit center bound is |c|<M=91/60 throughout
the original radius window. For completeness, a farthest corner
gives |c|^2+|c|+1/2<=1105/256, while

    M^2+M+1/2-1105/256=31/57600>0.

Thus both centers belong to the same open rectangle in these axes:

    3/2<x<91/60,
    |y|<sqrt((91/60)^2-9/4)=sqrt(181)/60.

Its squared diameter is

    (1/60)^2+4*(181/3600)=725/3600=29/144<1.

The two distinct actual centers would be less than one apart.
Their radius-1/2 open incircles would overlap, contrary to the
interior-disjoint original units. This excludes the parallel
alternative and proves (1).

## 5. A useful exact consequence for two triangles at one clear root

Suppose two actual triangle blocks meet only at K, and K has no
other positive force and is physically circle-clear. Retain every
actual private force and circle atom in the two branches. If each
branch's complete private aggregate has zero origin moment, the
two actual K pair sums are N and -N by the full K equation.
At every other vertex of either actual triangle block, each outside
branch attaches at that single vertex; summing that branch's original
private torque equations makes its whole contribution have zero
origin moment. Thus the zero-external-moment hypothesis of Section 1
holds at all three bodies of each triangle, not only at K.

Apply (1) separately to the two actual triangles, with their full
external aggregates at K. The closed K meets both opposite rays
{t N:t>=0} and {-t N:t>=0}. Convexity therefore gives

    O belongs to K.                                      (4)

This is closed containment, not an origin-interior assertion. If
either ray is met only at O, or if both points lie on a side of
K through O, those original boundary cases remain. No body degree
inside a decorated branch has been changed to obtain (4).

The theorem supplies a local geometric consequence, not an entire
coarse-cell closure. It uses no new generic normal selection,
numerical pose, coefficient certificate, Lean compilation or CI.
