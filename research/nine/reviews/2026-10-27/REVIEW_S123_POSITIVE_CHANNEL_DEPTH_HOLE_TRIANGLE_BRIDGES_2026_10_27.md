# Independent review: the positive-channel depth-bounded hole and slider

Date: October 27, 2026.
Reviewer: triangle_bridges, independent of the source author rooted_blocks.

**Decision: ACCEPTED, complete physical hole theorem and exact conditional
canonical-strip caller. No mathematical correction requested.**

## 1. Exact source, checker and direct scope

I read the whole frozen source and arithmetic implementation:

    S123_POSITIVE_CHANNEL_ROOT_DEPTH_HOLE_EMPTY.md
    SHA256 55e99b52853e4e29fb720f244cecee14b0e933794dc91a4b00b00a103e4370df;

    certificates/s123_positive_channel_hole_certificate.py
    SHA256 40b42546de8c744a78d80820de57cd16397131fd4468e63fd6df462f015b1685.

I read the complete contact-ring winding and actual-square chord
dependencies previously and checked their precise use here. The
canonical choice is only the existing minimum of the sum of squared
center norms among radius minimizers, before normal selection.

The physical statement assumes the actual strict channel t>0,
V>=1/50, actual root support r*x+V*t=epsilon and the original
side-transmitter interval. Every actual M frame, physical mask and
C/B mean remains. Its Section6 gives the literal whole unique-opposite
M caller; the positive radial-M domain with smaller V is explicitly
outside the conclusion.

## 2. Full winding and occupied-piece calculation

All five actual applications are distinct. I checked the height and
norm comparisons for E,P,S,Q,D, including the actual separation
D-E=n and P_f=1/2 versus D_f=-T. The actual center/contact loop
is therefore Jordan by the disjoint open square spokes.

Its clockwise orientation is also literal: in n,f coordinates
D--E is the lower edge. The other contacts lie above f=-T.
For S this follows directly from S in A: J+r is in[0,1], so
S_f-E_f=x-t(J+r)>=x-t>0, since t<3/5 and x>4/5.
The Q and P assertions follow from their displayed f bounds.

The actual A/B/C triangles are on the inward side of their
clockwise chords and have disjoint interiors. Positive-area pieces
have winding one in magnitude by the full contact homotopy;
degenerate pieces have zero area and are retained.

I independently expanded the seven-edge polygon after inserting the
auxiliary I. In world coordinates its first three determinants are
r, F(r-u), u(Y-F). In n,f coordinates the remaining terms sum
to q(1-p)-d-(d+1)T. Taking minus one half gives exactly

    H0(Y)=[d+(d+1)T-r(1+F)+2uF-uY-q(1-p)]/2.

The point I need not lie in M or the hole: its use is solely this
signed-area identity. The removed comparison triangle has area
a0*b0/2. For a short actual M chord this is at most1/4;
for a long chord the genuine inward M piece has area at least
sqrt(ell^2-1)/2, leaving at most1/4. The latter piece is
supplied by the original actual-square chord theorem and is disjoint
from the ABC pieces. Thus no fictitious occupied region is subtracted.

## 3. The whole actual-mean comparison

I re-differentiated the exact H0 expression and obtained

    H0'(Y)=t[1-2(ut+Yx)]/2.

For every comparison Y between F and its actual value,
ux-Yt>epsilon, so ut+Yx>=Y>=F>37/50. The derivative is
strictly negative throughout that complete interval. Hence replacing
Y by F in the scalar upper bound is valid and changes no actual
application. The displayed formula for H0(F) follows exactly.

The actual support/positivity guards place every original configuration
in the larger closed three-variable certificate domain. The estimate
t<3/5 follows from t/x<u/F<25/37; the square-root and reciprocal
domains are positive. The t=0 endpoint of the larger comparison box
does not impose a strict-channel vertex formula on an original
zero-channel side mean.

## 4. Complete arithmetic reproduction and independent reconstruction

I checked every author outward-integer operation, guard and subdivision
rule. The |r| guard uses the correct upper epsilon endpoint on both
sides; W and q guards use the required strict signs; T<=0 and a
strictly negative radicand are the only other possible exclusions.
Clamping a negative lower radicand endpoint to zero enlarges, rather
than restricts, the enclosure. A positive lower gap alone accepts a
remaining box. Every unresolved box is split with its common face
retained; no depth or precision endpoint is accepted.

The saved checker reproduces all printed data:

    splits404, terminals405, visits809, depth15;
    positive285, r-guard74, q-guard43, W-guard3;
    minimum positive gap19715476/2^40.

I then wrote the separate reconstruction

    certificates/review_s123_positive_channel_hole_fraction.py
    SHA256 8648efa55b43ce5f3233f25ad925a0be17bac96c0bd3215fcbb54b0ad6a589ab.

It imports only the reviewer's previously independent exact Fraction
Range class from review_s123_zero_strict_middle_near_fraction_sat.py,
not any author arithmetic. All algebraic interval operations are
unrounded rational calculations. Square roots alone use a separate
outward2^-48 rational enclosure with integer square root.

The independent complete reconstruction yields precisely the same
405 terminals, all guard counts,809 visits and depth15. Its uniform
strict lower gap exceeds5047162915/2^48. Thus the complete feasible
domain has H0(F)+1/4<1; no sampled configuration or unexplored
region enters the proof.

## 5. The actual inner rectangle and all-nine slider

I checked the winding-one rectangle in the actual n,f frame.
A and its chord are in n<=epsilon. Any portion of the B chord
with n>epsilon has f>1/2 by its world height>=F. The M chord
is above f=1/2, the C chord is at n>=d, and the actual U chord
is the bottom segment f=-T. These are complete barriers to the
open rectangle(epsilon,d) times(-T,1/2).

If U.top_f<1/2 and U is closed-disjoint from M, a sufficiently
small motion along positive f remains separated from A,C by their
unchanged support lines and from M by positive distance. Its new
strip has world height below1/2 and cannot meet B. Every new
point outside the core lies in the bounded hole. An extra-square
interior cannot cross the original core Jordan loop, and the full
area theorem excludes any whole inner unit. Thus every original
extra and the genuine leaf remain disjoint under the actual motion.

The original U center moves transversely toward zero, reducing both
its largest corner radius and its squared center norm. This proves
the precise conditional alternative, without assigning a force to
an additional physical contact.

## 6. Complete unique-opposite-M caller and retained limits

The caller uses the fully independently accepted27eee13e domain,
whose separate hexagon review is8c30ec90. Its Q_n>epsilon makes
X-a1 positive; hence the original world Y is below1/2+b1<49/50.
Since Y>=1-V, V>1/50 in every literal unique-opposite positive
channel, including both original root types.

That M lies wholly above f=1/2, so the conditional slider gives
U.top_f>=1/2. I checked the physical upper bound from its actual
lower edge at n=d, with the unchanged C mean X and both mean
endpoints retained. The complete bound
(b1/a1)(X-d)<21/200 gives the full contained U strip exactly
as claimed. It does not center a general unique M.

The positive radial-M row with V<1/50, any exterior near-extra
screen, and the final arc routing remain separate. No whole S123
closure is inferred. All actual loads, normals, physical masks,
means and all nine squares are preserved. No compilation, CI,
remote mutation or shared metadata action was used.
