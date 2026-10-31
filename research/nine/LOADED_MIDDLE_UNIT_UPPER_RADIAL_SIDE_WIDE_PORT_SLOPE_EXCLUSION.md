# A loaded middle unit cannot reach a radial upper side from a low southeast port of slope at least one sixth

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed hand local theorem, awaiting separate full
independent review and root adoption.** The entire original loaded
middle star is retained. The upper-side theorem uses only an actual
port height less than one and a downward normal slope at least one
sixth. It does not require the old narrow port box, a boundary status
for the other neighbor, or any equation at either neighbor.

## 1. Actual statement and exact accepted inputs

All actual closed unit squares have pairwise disjoint open interiors
and lie in the same unchanged disk centered at O, of radius

    sqrt(2)<R<1+sqrt(2).

Use an actual orthonormal frame n,f about O. Let an actual unit C be

    C=[d,d+1]n+[-1/2,1/2]f,       d>=1.

The main upper-side theorem needs only this actual rectangle, not a
circle load or force equation at C. Let M be an actual loaded unit
of true positive degree two, with exactly its original neighbors B,C.
B retains arbitrary degree, loads and physical circle mask. Write g
for the original B-to-M unit normal at the unchanged application Q,
and h for the original C-to-M unit normal at the unchanged application
P. Keep all original positive force magnitudes, side means and circle
weights. In particular zero individual weights at physical circle
corners are not suppressed.

**Upper-side theorem.** The following actual data are impossible:

    h=f, P=(X,1/2), d<=X<=d+1,
    g_n>0>g_f,       -g_f/g_n>=1/6,       Q_f<1.        (1)

The full closed interval for X and every original mean at Q remain.
There is no bound on Q_n in this theorem.

**Combined upper-contact theorem.** If, in addition, d<61/60, then
the following full support cover is impossible:

    h_f>0, h_n<=0,
    g_n>0>g_f, -g_f/g_n>=1/6,
    1/6<Q_n<1,       0<Q_f<1.                          (2)

The strict h_n<0 feature has P=(d,1/2); the h_n=0 feature is the
entire upper side in (1). The strict feature will use only physical
port geometry, not M's equation or its circle mask.

The exact accepted direct inputs are:

| Source | SHA256 | Used scope |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original loaded M2 equation, actual applications, and nonnegative physical circle weights |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Full proper radial concurrence for the actual nonparallel M2 forces; inside M only after its unique physical corner is proved |
| RADIAL_BOUNDARY_UPPER_CONTACT_LOADED_MIDDLE_SHORT_PORT_EXCLUSION.md | 4497b0c781a518ff6c04e92fe8f7b0b121965a740c14ccb1a56864c7754d8106 | Section 2's force-free obtuse-support short-chord fact only |

The new upper-side proof below is supplied in full. The older theorem's
height less than 9/10 conclusion is not invoked at the larger height
range in (1).

## 2. The complete upper-side physical frame and port cover

Suppose (1) holds. M lies above its unchanged minimum-f support at
P=(X,1/2). If M owns f, its f interval is [1/2,3/2]. Since
g_n>0>g_f, its minimum-g point is its upper-left vertex and has
height 3/2. It cannot be the actual Q of height less than one.

Otherwise P is M's unique lowest vertex. Its complete inward frame
can be written

    u=(-c,s), v=(s,c), c,s>0, c^2+s^2=1,
    M=P+[0,1]u+[0,1]v.

There is no prior order between c and s. Since g.u<0, the entire
minimum-g support of M is one of the following actual features:

    g.v<0: Q=P+u+v;
    g.v>0: Q=P+u;
    g.v=0: Q=P+u+tau v, 0<=tau<=1.                    (3)

The first has Q_f=1/2+s+c>3/2 and is impossible. Each other
feature has Q_f>=1/2+s. Consequently the entire remaining domain
satisfies

    0<s<1/2,       c>sqrt(3)/2>6/7,       c>s.        (4)

The exact comparison for c>6/7 is 3/4-36/49=3/196>0.
All endpoints of the mean tau are still in (3).

## 3. The actual circle mask is determined before concurrence is used

Put Z=P+v=(X+s,1/2+c). Compare all four actual corners of M:

    |Z|^2-|P|^2=1+2Xs+c>0,
    |P+u+v|^2-|Z|^2=-2Xc+s+1
                         <-sqrt(3)+3/2<0,
    |Z|^2-|P+u|^2=2X(s+c)+(c-s)>0.                  (5)

Here X>=d>=1 and (4) suffice for every strict comparison. Thus Z
is M's unique farthest corner. M has a positive total original
circle load, so Z is its unique actual physical circle corner and
its full resultant is a positive multiple of Z. This conclusion
concerns the physical mask, not just the positive coefficients.

The actual M outward normals are -g and -f. They are nonparallel
because g_n>0. Apply the accepted full-star concurrence theorem to
these two original forces. It yields their actual intersection q,
a positive multiple of Z, with the proper incoming-ray relations.
The original C-to-M line has n coordinate X, so exactly

    q=[X/(X+s)]Z,
    q_n=X,
    q_f=X(1/2+c)/(X+s),
    q=Q+ell g,       ell>=0.                          (6)

No boundary premise at B is needed for this theorem. The monotonicity
of X/(X+s) for X>=1 gives the useful unchanged lower bound

    q_f>=(1/2+c)/(1+s).                               (7)

The proof does not assert q_f>1 throughout the larger range (4).
The exact normal slope and the actual full mean distinguish the two
remaining rows in (3).

## 4. The complete strict-vertex return contradicts the slope

If g.v>0, Q=P+u=(X-c,1/2+s). Comparing the n coordinates in
(6) gives ell*g_n=c>0. Hence the actual downward slope k is

    k=-g_f/g_n=(1/2+s-q_f)/c
       <=[s(3/2+s)/c-1]/(1+s).                       (8)

For 0<s<1/2 one has s(3/2+s)<1. By (4), 1/c<7/6.
The bracketed numerator on the right of (8) is therefore less
than 1/6. Since 1+s>1, the whole expression is less than 1/6:
if that numerator is negative the conclusion is immediate; if it
is nonnegative, division only decreases it. Thus k<1/6, contrary
to (1). This includes every allowed X and needs no upper bound
on Q_n or on the positive original force magnitudes.

## 5. The entire owned side mean contradicts the height by itself

If g.v=0, the signs and unit length of g force g=-u=(c,-s).
Keep the original Q=P+u+tau v, 0<=tau<=1. Equation (6) is

    q=P+(1-ell)u+tau v.

Its n coordinate X implies 1-ell=tau*s/c, and its f coordinate
therefore gives

    q_f=1/2+tau/c,
    tau=c(q_f-1/2),
    Q_f=1/2+s+c^2(q_f-1/2).                          (9)

Use (7) in (9). The factor c^2 is positive, so

    Q_f-1
       >=[s^2-1/2+s^3/2+(1-s^2)c]/(1+s).            (10)

Since 0<c<1, c>c^2=1-s^2. The numerator in (10) is strictly
greater than

    1/2-s^2+s^3/2+s^4>1/4>0,

where 0<s<1/2 was used in the last step. Consequently Q_f>1,
contrary to the actual premise. This row did not need k>=1/6.
Both original mean endpoints tau=0 and tau=1 were retained until
the contradiction; no concurrence or endpoint force was deleted.

Sections 2--5 exhaust the complete support cover and prove (1).

## 6. The strict-inner contact and the combined theorem

Suppose (2) holds with h_n<0. The actual C support is
P=(d,1/2). The two actual outward M normals are -g and -h,
and their dot product is

    g.h=g_n h_n+g_f h_f<0.

The force-free obtuse-support fact says their actual points must
be at distance at least one, including arbitrary side means and
normal-cone endpoints. But the unchanged coordinates in (2) give

    0<d-Q_n<61/60-1/6=17/20,
    |Q_f-1/2|<1/2,
    |Q-P|^2<(17/20)^2+(1/2)^2=389/400<1.            (11)

The exact reserve is 11/400. This contradiction is entirely
physical and uses no M load, degree or concurrence premise.
When h_n=0, its unit length and h_f>0 give h=f, so the already
proved whole upper-side theorem applies. This proves (2).

## 7. Broad scope and the unchanged original caller

The upper-side theorem needs only one actual loaded M2, its two
real neighbors, X>=1, the upper C support, Q_f<1, and the exact
downward slope at least 1/6. Neighbor B need not be physically
boundary. Both neighbors may have arbitrary actual degrees and
additional original loads. The full upper-side mean proof itself
excludes its owned-side row for every positive downward slope.

In the original S123 opposite-root owned-boundary caller, C is
the actual radial two-corner unit, 1<d<61/60, and its full C2
equation supplies h_f>0 and h_n<=0. All nine original units and
the actual B--M--C path remain; no B--C edge is introduced.
A caller must separately prove the unchanged Q coordinates and
slope in (2) for each original B return before invoking this exit.

This source does not itself replace a complete scalar certificate,
close an original family flag, or remove a high-radius obligation.
It uses no numerical pose enumeration, interval certificate, Lean,
Lake, CI, metadata edit or remote operation. Separate complete
independent review of these exact bytes is still required.
