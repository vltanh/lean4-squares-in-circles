# Independent derivation of the wide-inner-main vertical gap

November 2, 2026. This is a hand verification of the proposed auxiliary
lemma: in the original outer-actual/main-cone domain, if
H=max(hB,hC)≥59/100, then |yB−yC|>81/100. It introduces no numerical
table, Lean, Lake, or CI.

The finished source `WIDE_WEAK_MIDDLE_PAIR_VERTICAL_GAP_HAND_PROOF.md`
was independently read after this derivation. Its full physical caller,
two width ranges, rational reserves, and lower-side application agree
with the derivation below and pass review.

The accepted weak-middle outer-link reserve supplies

\[
1/2\le K=\min(h_B,h_C)\le H<13/20,
\qquad \eta(H)+\eta(K)<1/30,
\]

where eta(h)=h+1/(4h)−1. Since eta increases for h≥1/2 and
eta(3/5)=1/60, necessarily K<3/5. The actual outer links give

\[
 0<x_C-x_B\le d:=61/30-H-K.
\]

The original two-square support inequality in Section 2 of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md` gives support sum
at least 1+H−K on every genuine separating owner axis, regardless of
the two chiralities.

Suppose |yC−yB|≤81/100. A frame of halfwidth h has absolute components
a=h+sqrt(1/2−h²), b=h−sqrt(1/2−h²). Throughout the full inner range,
b/a<1/2. For instance at the largest endpoint h=13/20, the equivalent
comparison h<3sqrt(1/2−h²) follows by squaring. Every axis projection
is bounded by one of

\[
                   ad+(81/100)b,
                   bd+(81/100)a.
\]

For fixed d these both increase with folded frame angle. Indeed their
derivatives have signs 81/100−d tan(theta) and d−(81/100)tan(theta).
Here 11/15≤d≤283/300, so both signs are positive when tan(theta)<1/2.
The frame belonging to H therefore gives the largest possible
projection. Write k=sqrt(1/2−H²), a=H+k, b=H−k.

For fixed H, the two support-minus-projection residuals decrease as K
increases: their K derivatives are respectively a−1 and b−1. It
suffices to substitute K=min(H,3/5), a closed enlargement.

## H between 59/100 and 3/5

Now d=61/30−2H and the lower support is one. The residual for the
first projection is

\[
R_1=1-H(853/300-2H)-k(367/300-2H).
\]

Its derivative equals

\[
4H-853/300+(H/k)(367/300-2H)+2k>0.
\]

The last strict comparison follows from H≥59/100, k≥sqrt(7/50)>3/8−1/100,
and 367/300−2H>0; these weaker rational bounds already suffice.
At H=59/100, use k<39/100. This gives R1>13/7500.

For the second projection, since d>81/100,

\[
 bd+(81/100)a
 =H(853/300-2H)+k(81/100-d)
 <H(853/300-2H)\le493/500.
\]

The last function increases on this interval and its endpoint value
at H=3/5 is 493/500. The second residual is therefore greater than
7/500. Both original axis forms fall strictly short of the required
support.

## H between 3/5 and 13/20

Substitute K=3/5 and d=43/30−H. The two residuals become

\[
 R_1=A-k(187/300-H),\qquad
 R_2=A+k(187/300-H),
\]

where

\[
 A=H^2-(373/300)H+2/5
   =(H-373/600)^2+4871/360000.
\]

On this interval k<3/8. The positive part of 187/300−H is at most
7/300, while its negative part has absolute value at most 2/75.
Consequently

\[
 R_1>4871/360000-(3/8)(7/300)=1721/360000>0,
\]

\[
 R_2>4871/360000-(3/8)(2/75)=1271/360000>0.
\]

Every original separating axis is excluded. This proves the strict
vertical gap |yB−yC|>81/100, including both possible vertical orders,
both independent chiralities, and the interval boundary H=3/5.

## Application to an original lower-side extra

The independently accepted quarter theorem gives yB,yC<−1/4 under
the original 010/11 selected bad-floor hypotheses. The accepted
original lower-side pair envelope gives its assigned main M the lower
bound yM>f(hM), where f(h)>−9/20 throughout [1/2,13/20]. If hM≥59/100,
the lemma applies. M cannot be below the other main: their difference
would then be less than 1/5, contrary to 81/100. Thus M is above.
The original outer-cone lower bound on the other main is −6/5, giving

\[
                      y_M>-6/5+81/100=-39/100.
\]

This application is a valid strengthening of the lower-side envelope
in the wide assigned-main region. It does not itself exclude that
region or close the whole 010/11 mask.
