module

public import SquaresInCircles.Eight.Owners.All.HighSecondary
public import SquaresInCircles.Eight.Owners.All.HighBridgePolynomials
public import SquaresInCircles.Eight.Owners.All.HighZeroPositive

/-!
# Eight squares: transfer of the four bridge polynomials to their exact trigonometric duals

All Taylor signs are fixed on the whole interval.  The positive
quadratic norm envelope uses only a square completion and the original
circle norm.
-/

section
/-!
## The exact six-edge residual bonus from the four original G1 types

Alternating the two scalar residual potentials pays the difference
between the endpoint type potentials.  A path from middle to middle
either stays middle or pays two exits.  Only the established four-type
G1 constants are used.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

def sixTypeCost (a b c d e f g : Fin 4) : ℝ :=
  handGamma a b+handGamma b c+handGamma c d+handGamma d e+handGamma e f+handGamma f g
def middlePotential (i : Fin 4) : ℝ := if i=2 then 93/10000 else 0

theorem bonus_symm (i j : Fin 4) : bonus i j=bonus j i := by
  simp only [bonus,abs_sub_comm,show (i=2 ∧ j=2)↔(j=2 ∧ i=2) from and_comm]

theorem residual_steps (i j : Fin 4) :
    8833/10000+tau i+tau j-53/2000≤handGamma i j ∧
    8833/10000-tau i-tau j+53/2000≤handGamma i j := by
  fin_cases i <;> fin_cases j <;> norm_num [handGamma,handGammaNumerator,tau]

theorem middle_steps (i j : Fin 4) :
    8833/10000+middlePotential i-middlePotential j≤handGamma i j ∧
    8833/10000-middlePotential i+middlePotential j≤handGamma i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [handGamma,handGammaNumerator,middlePotential]

theorem six_type_absolute (a b c d e f g : Fin 4) :
    |tau a-tau g|≤ sixTypeCost a b c d e f g-6*(8833/10000) := by
  have h0 := residual_steps a b
  have h1 := residual_steps b c
  have h2 := residual_steps c d
  have h3 := residual_steps d e
  have h4 := residual_steps e f
  have h5 := residual_steps f g
  apply abs_le.mpr
  dsimp [sixTypeCost]
  constructor
  · linarith [h0.2,h1.1,h2.2,h3.1,h4.2,h5.1]
  · linarith [h0.1,h1.2,h2.1,h3.2,h4.1,h5.2]

theorem six_type_middle (a b c d e : Fin 4) :
    (93/5000:ℝ)≤ sixTypeCost 2 a b c d e 2-6*(8833/10000) := by
  have h0 := middle_steps 2 a
  have h1 := middle_steps a b
  have h2 := middle_steps b c
  have h3 := middle_steps c d
  have h4 := middle_steps d e
  have h5 := middle_steps e 2
  have hM : middlePotential 2=(93/10000:ℝ) := by norm_num [middlePotential]
  by_cases ha : a=2
  · by_cases hb : b=2
    · by_cases hc : c=2
      · by_cases hd : d=2
        · by_cases he : e=2
          · norm_num [sixTypeCost,ha,hb,hc,hd,he,handGamma,handGammaNumerator]
          · have hz : middlePotential e=0 := by simp [middlePotential,he]
            dsimp [sixTypeCost]
            linarith [h0.1,h1.1,h2.1,h3.1,h4.1,h5.2]
        · have hz : middlePotential d=0 := by simp [middlePotential,hd]
          dsimp [sixTypeCost]
          linarith [h0.1,h1.1,h2.1,h3.1,h4.2,h5.2]
      · have hz : middlePotential c=0 := by simp [middlePotential,hc]
        dsimp [sixTypeCost]
        linarith [h0.1,h1.1,h2.1,h3.2,h4.2,h5.2]
    · have hz : middlePotential b=0 := by simp [middlePotential,hb]
      dsimp [sixTypeCost]
      linarith [h0.1,h1.1,h2.2,h3.2,h4.2,h5.2]
  · have hz : middlePotential a=0 := by simp [middlePotential,ha]
    dsimp [sixTypeCost]
    linarith [h0.1,h1.2,h2.2,h3.2,h4.2,h5.2]

theorem six_type_bonus (a b c d e f g : Fin 4) :
    6*(8833/10000)+bonus a g≤ sixTypeCost a b c d e f g := by
  have hAbs := six_type_absolute a b c d e f g
  have hM : (if a=2 ∧ g=2 then (93/5000:ℝ) else 0)≤
      sixTypeCost a b c d e f g-6*(8833/10000) := by
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      exact six_type_middle b c d e f
    · exact (abs_nonneg _).trans hAbs
  have hh := max_le hAbs hM
  dsimp [bonus]
  linarith

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## The outer-bridge cap from the six unchanged original physical edges

The actual G1 inequalities telescope with the same marker at each
shared vertex.  The six-edge frame path pays the width of DE by the
metric triangle inequality.  The residual type bonus is derived from
the original six chart pairs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open Candidate FramePair GlobalOuterAnchor

def markerCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) (i : Vertex) : ℝ :=
  Candidate.phi theta i+((stateOf C i).signedLabel-(stateOf C (next i)).signedLabel)

theorem markerCharge_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    (∑i,markerCharge C theta i)=2*Real.pi := by
  simp only [markerCharge,Finset.sum_add_distrib,sum_phi,sum_marker_difference,add_zero]

theorem frame_pair_bound {C : BoundaryCycle Q0} (F : Candidate.Frame C) (i : Vertex) :
    handGamma (stateOf C i).branch.type (stateOf C (next i)).branch.type<
      markerCharge C F.theta i-(9/50)*frameCost |delta F.theta i| := by
  have hh := FrameAllPairs.all_pair C i
  rw [State.cost,pairAngle_charge,← frameCost_eq_actual F i] at hh
  have hphase : pairAngle C i=Candidate.phi F.theta i :=
    (pairAngle_gap C i).trans (F.physical_angle i).symm
  rw [hphase] at hh
  change handGamma (stateOf C i).branch.type (stateOf C (next i)).branch.type<_ at hh
  dsimp [markerCharge]
  linarith

theorem markerCharge_DE (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (hD : transverse (stateOf C D)≤0) (hE : transverse (stateOf C E)≤0) :
    markerCharge C theta D=unsignedCharge (stateOf C D) (stateOf C E) (delta theta D) := by
  have hd := GlobalQuarterSign.signed_of_nonpos (stateOf C D) hD
  have he := GlobalQuarterSign.signed_of_nonpos (stateOf C E) hE
  rw [markerCharge,show next D=E by decide,hd,he]
  simp only [unsignedCharge,Candidate.phi,show word D=1 by decide,Int.cast_one,one_mul]
  ring

theorem six_edge_return {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    frameCost |delta F.theta D|≤
      frameCost |delta F.theta E|+frameCost |delta F.theta H|+
      frameCost |delta F.theta G|+frameCost |delta F.theta A|+
      frameCost |delta F.theta B|+frameCost |delta F.theta T| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [F.spread j i,Real.pi_gt_three]
  have hG := frameCost_triangle (hrange E H) (hrange H G) (hrange E G)
    (by linarith [abs_sub_le (F.theta G) (F.theta H) (F.theta E)])
  have hA := frameCost_triangle (hrange E G) (hrange G A) (hrange E A)
    (by linarith [abs_sub_le (F.theta A) (F.theta G) (F.theta E)])
  have hB := frameCost_triangle (hrange E A) (hrange A B) (hrange E B)
    (by linarith [abs_sub_le (F.theta B) (F.theta A) (F.theta E)])
  have hT := frameCost_triangle (hrange E B) (hrange B T) (hrange E T)
    (by linarith [abs_sub_le (F.theta T) (F.theta B) (F.theta E)])
  have hD := frameCost_triangle (hrange E T) (hrange T D) (hrange E D)
    (by linarith [abs_sub_le (F.theta D) (F.theta T) (F.theta E)])
  have hsum : frameCost |F.theta D-F.theta E|≤
      frameCost |F.theta H-F.theta E|+frameCost |F.theta G-F.theta H|+
      frameCost |F.theta A-F.theta G|+frameCost |F.theta B-F.theta A|+
      frameCost |F.theta T-F.theta B|+frameCost |F.theta D-F.theta T| := by linarith
  have eE : delta F.theta E=F.theta H-F.theta E := by rw [delta,show next E=H by decide]
  have eH : delta F.theta H=F.theta G-F.theta H := by rw [delta,show next H=G by decide]
  have eG : delta F.theta G=F.theta A-F.theta G := by rw [delta,show next G=A by decide]
  have eA : delta F.theta A=F.theta B-F.theta A := by rw [delta,show next A=B by decide]
  have eB : delta F.theta B=F.theta T-F.theta B := by rw [delta,show next B=T by decide]
  have eT : delta F.theta T=F.theta D-F.theta T := by rw [delta,show next T=D by decide]
  have eD : delta F.theta D=F.theta E-F.theta D := by rw [delta,show next D=E by decide]
  rw [eE,eH,eG,eA,eB,eT,eD,abs_sub_comm (F.theta E) (F.theta D)]
  exact hsum

theorem frame_six_pairs {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    sixTypeCost (stateOf C E).branch.type (stateOf C H).branch.type
      (stateOf C G).branch.type (stateOf C A).branch.type (stateOf C B).branch.type
      (stateOf C T).branch.type (stateOf C D).branch.type<
    markerCharge C F.theta E+markerCharge C F.theta H+markerCharge C F.theta G+
      markerCharge C F.theta A+markerCharge C F.theta B+markerCharge C F.theta T-
      (9/50)*(frameCost |delta F.theta E|+frameCost |delta F.theta H|+
        frameCost |delta F.theta G|+frameCost |delta F.theta A|+
        frameCost |delta F.theta B|+frameCost |delta F.theta T|) := by
  have hE := frame_pair_bound F E
  have hH := frame_pair_bound F H
  have hG := frame_pair_bound F G
  have hA := frame_pair_bound F A
  have hB := frame_pair_bound F B
  have hT := frame_pair_bound F T
  dsimp [sixTypeCost,E,H,G,A,B,T,D,next] at hE hH hG hA hB hT ⊢
  linarith

/-- The only cap used by the complete bridge theorem is now a
consequence of the actual original seven-cycle. -/
theorem original_cap {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hD : transverse (stateOf C D)≤0) (hE : transverse (stateOf C E)≤0) :
    augmentedUnsigned (stateOf C D) (stateOf C E) (delta F.theta D)<
      cap-bonus (stateOf C D).branch.type (stateOf C E).branch.type := by
  have htypes := six_type_bonus (stateOf C E).branch.type (stateOf C H).branch.type
    (stateOf C G).branch.type (stateOf C A).branch.type (stateOf C B).branch.type
    (stateOf C T).branch.type (stateOf C D).branch.type
  rw [bonus_symm (stateOf C E).branch.type (stateOf C D).branch.type] at htypes
  have hpairs := frame_six_pairs F
  have hreturn := six_edge_return F
  have hsum := markerCharge_sum C F.theta
  rw [Fin.sum_univ_seven] at hsum
  have hDE := markerCharge_DE C F.theta hD hE
  have hcomp : markerCharge C F.theta E+markerCharge C F.theta H+markerCharge C F.theta G+
      markerCharge C F.theta A+markerCharge C F.theta B+markerCharge C F.theta T+
      unsignedCharge (stateOf C D) (stateOf C E) (delta F.theta D)=2*Real.pi := by
    dsimp [H,G,A,B,T,D,E] at hDE ⊢
    linarith
  dsimp [augmentedUnsigned,cap]
  linarith [Arithmetic.two_pi_lt_710_over_113]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## Fixed dual supports on the complete low and middle arcs

The low-source loss is a direct circle difference identity and one
quadratic completion.  The middle source uses its whole shifted
circle.  All target minima retain the original low, middle or high
marker.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

def lowDualA (mu : ℝ) : ℝ := -kappa+rho*FrameHighArc.u+(rho+mu)*FrameLowArc.u
def lowDualB (mu : ℝ) : ℝ := -rho*FrameHighArc.v+(rho+mu)*FrameLowArc.v
def lowDualC (mu : ℝ) : ℝ := rho*FrameHighArc.k+(rho+mu)*FrameLowArc.u*a0
def midDualA (mu : ℝ) : ℝ := -kappa+rho*FrameHighArc.u+(rho+mu)*FrameMidArc.p
def midDualB (mu : ℝ) : ℝ := -rho*FrameHighArc.v+(rho+mu)*FrameMidArc.q
def midDualC (mu : ℝ) : ℝ := rho*FrameHighArc.k-(rho+mu)*FrameMidArc.cM
def midShiftC (mu : ℝ) : ℝ := midDualC mu+(midDualA mu+midDualB mu)/2
def sourceNorm (mu lambda z : ℝ) : ℝ :=
  Real.sqrt ((midDualA mu+lambda*Real.cos z)^2+(midDualB mu-lambda*Real.sin z)^2)

theorem arcK_low (mu b : ℝ) :
    arcK .low mu b=lowDualC mu-lowDualA mu*A b-lowDualB mu*b := by
  rw [arcK,arcPotential,arcMarker_low]
  dsimp [FrameHighArc.H,FrameLowArc.L,lowDualA,lowDualB,lowDualC]
  ring

theorem arcK_middle (mu b : ℝ) :
    arcK .middle mu b=midDualC mu-midDualA mu*A b-midDualB mu*b := by
  rw [arcK,arcPotential,arcMarker_middle]
  dsimp [FrameHighArc.H,FrameMidArc.M,midDualA,midDualB,midDualC]
  ring

theorem high_constant_lower : (118248/125000:ℝ)<FrameHighArc.k := by
  dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
  linarith [Arithmetic.pi_hand_enclosure.1,c0_precise.1]

theorem dual_endpoint_constants :
    (2113/2500:ℝ)<arcK .low (17/10) b1 ∧
    -(1673/10000:ℝ)<arcK .low 5 b1 ∧
    (109221/10000:ℝ)< midShiftC (17/10) ∧
    (115297/5000:ℝ)< midShiftC 5 := by
  have hk := high_constant_lower
  have ha0 := a0_precise
  have ha1 := a1_precise
  have hb1 := b1_precise
  repeat' constructor
  all_goals first
    | rw [arcK_low,A_b1]
    | skip
  all_goals dsimp [midShiftC,midDualA,midDualB,midDualC,
    lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
  all_goals linarith

theorem affine_arc_lower {p q c l u b g : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hu : u≤c0) (hb : b∈Icc l u)
    (hleft : g<c+p*A l+q*l) (hright : g<c+p*A u+q*u) :
    g<c+p*A b+q*b := by
  have hh := linear_endpoint_lower (q := q) hp hl hu hb
  have he : g-c< min (linear p q l) (linear p q u) := by
    apply lt_min <;> dsimp [linear] <;> linarith
  have h := he.trans_le hh
  dsimp [linear] at h
  linarith

theorem low_dual_target (t : State) (ht : t.branch=.low) :
    -(4029/2500:ℝ)< -K t (17/10)-(59/25)*t.b := by
  rw [K_arc t (by simp [ht,Branch.type]),ht,arcK_low]
  have h := affine_arc_lower (p := lowDualA (17/10))
    (q := lowDualB (17/10)-59/25) (c := -lowDualC (17/10))
    (g := -(4029/2500:ℝ)) (by norm_num [lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u])
    (by norm_num) b1_mem.2 (state_low_chart t ht).2
  have he0 : -(4029/2500:ℝ)< -lowDualC (17/10)+lowDualA (17/10)*A 0+
      (lowDualB (17/10)-59/25)*0 := by
    rw [A_zero]
    dsimp [lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2]
  have he1 : -(4029/2500:ℝ)< -lowDualC (17/10)+lowDualA (17/10)*A b1+
      (lowDualB (17/10)-59/25)*b1 := by
    rw [A_b1]
    dsimp [lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2,a1_precise.1,b1_precise.1]
  have hh := h he0 he1
  linarith

theorem nonlow_dual_target (t : State) (ht : t.branch=.middle ∨ t.branch=.high) :
    -(1357/1000:ℝ)< -K t 5-(93/20)*t.b := by
  rcases ht with ht | ht
  · rw [K_arc t (by simp [ht,Branch.type]),ht,arcK_middle]
    have h := affine_arc_lower (p := midDualA 5) (q := midDualB 5-93/20)
      (c := -midDualC 5) (g := -(1357/1000:ℝ))
      (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
      b1_mem.1 b2_mem.2 (state_mid_chart t ht).2
    have he0 : -(1357/1000:ℝ)< -midDualC 5+midDualA 5*A b1+(midDualB 5-93/20)*b1 := by
      rw [A_b1]
      dsimp [midDualA,midDualB,midDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
        FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a1_precise.1,b1_precise.1]
    have he1 : -(1357/1000:ℝ)< -midDualC 5+midDualA 5*A b2+(midDualB 5-93/20)*b2 := by
      rw [A_b2]
      dsimp [midDualA,midDualB,midDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
        FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a2_bounds.1,b2_precise.1]
    have hh := h he0 he1
    linarith
  · have hh := circle_product_support t
      (f := kappa+5*FrameHighArc.u) (g := 93/20-5*FrameHighArc.v)
      (K := 18689/2000) (by norm_num)
      (by norm_num [Q0,kappa,FrameHighArc.u,FrameHighArc.v])
    rw [K,potential_high t ht,unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_high]
    dsimp [FrameHighArc.H] at *
    rw [← (FrameHighArc.state_high_chart t ht).1]
    have hk := high_constant_lower
    dsimp [kappa,FrameHighArc.u,FrameHighArc.v] at *
    linarith

theorem circle_endpoint_loss {x t X T a b e k loss : ℝ}
    (hc : x^2+t^2=X^2+T^2) (hX : 0<X) (ha : 0≤a)
    (hk : 0<k) (hcurv : 2*k*X≤a) (ht : t≤T)
    (hd : a*T-b*X≤e*X) (hdisc : e^2<4*k*loss) :
    -loss<(-a*x-b*t)-(-a*X-b*T) := by
  have hid : 2*X*((-a*x-b*t)-(-a*X-b*T))=
      a*(x-X)^2+a*(t-T)^2+2*(a*T-b*X)*(t-T) := by
    linear_combination -a*hc
  have h1 := mul_nonneg ha (sq_nonneg (x-X))
  have h2 := mul_nonneg (sub_nonneg.mpr hcurv) (sq_nonneg (t-T))
  have h3 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd) (sub_nonpos.mpr ht)
  have hq := positive_quadratic (z := t-T) hk hdisc
  have hq' := mul_pos (show 0<2*X by linarith) hq
  nlinarith only [hid,h1,h2,h3,hq',hX]

theorem circle_endpoint_min {x t X T a b : ℝ}
    (hc : x^2+t^2=X^2+T^2) (hX : 0<X) (ha : 0≤a) (ht : t≤T)
    (hd : a*T-b*X≤0) : -a*X-b*T≤ -a*x-b*t := by
  have hid : 2*X*((-a*x-b*t)-(-a*X-b*T))=
      a*(x-X)^2+a*(t-T)^2+2*(a*T-b*X)*(t-T) := by
    linear_combination -a*hc
  have h1 := mul_nonneg ha (sq_nonneg (x-X))
  have h2 := mul_nonneg ha (sq_nonneg (t-T))
  have h3 := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr ht)
  nlinarith only [hid,h1,h2,h3,hX]

def lowAngle (z : ℝ) : ℝ := Real.sin z+(459/1000)*Real.cos z

theorem lowAngle_deriv (z : ℝ) :
    HasDerivAt lowAngle (Real.cos z-(459/1000)*Real.sin z) z := by
  have h : HasDerivAt (fun x => Real.sin x+(459/1000)*Real.cos x)
      (Real.cos z+(459/1000)*(-Real.sin z)) z :=
    (Real.hasDerivAt_sin z).fun_add ((Real.hasDerivAt_cos z).const_mul (459/1000))
  exact h.congr_deriv (by ring)

theorem lowAngle_bound {z : ℝ} (hz : z∈Icc 0 frameCap) : lowAngle z<9953/10000 := by
  have hmono : MonotoneOn lowAngle (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (lowAngle_deriv z).continuousAt.continuousWithinAt
    · exact fun z _ => lowAngle_deriv z
    · intro z hz
      have hh := transport_trig (Ioo_subset_Icc_self hz)
      linarith [hh.1,hh.2.2.2.1]
  have hh := hmono hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2
  have hs := Arithmetic.sin_le_sin9 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc := Arithmetic.cos_le_cos8 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8,frameCap] at hs hc
  dsimp [lowAngle,frameCap] at hh ⊢
  linarith

theorem low_source_derivative_bound {mu lambda e z : ℝ}
    (hz : z∈Icc 0 frameCap) (hl : 0≤lambda)
    (ha : 0≤lowDualA mu+lambda*Real.cos z)
    (he : (459/1000)*lowDualA mu-lowDualB mu+lambda*(9953/10000)≤e) :
    (lowDualA mu+lambda*Real.cos z)*(b1+1/2)-
      (lowDualB mu-lambda*Real.sin z)*(a1+1/2)≤e*(a1+1/2) := by
  have hr : b1+1/2≤(459/1000)*(a1+1/2) := by
    linarith [b1_precise.2,a1_precise.1]
  have hh := mul_le_mul_of_nonneg_left hr ha
  have hangle := mul_le_mul_of_nonneg_left (lowAngle_bound hz).le hl
  have hraw : (459/1000)*(lowDualA mu+lambda*Real.cos z)-
      (lowDualB mu-lambda*Real.sin z)≤e := by
    dsimp [lowAngle] at hangle
    nlinarith only [he,hangle]
  have hscaled := mul_le_mul_of_nonneg_right hraw
    (show 0≤a1+1/2 by linarith [a1_precise.1])
  nlinarith only [hh,hscaled]

theorem low_source_low_target (s : State) (hs : s.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    2113/2500-(59/25)*a1*Real.cos z+(59/25)*b1*Real.sin z-1/625<
      K s (17/10)-(59/25)*s.a*Real.cos z+(59/25)*s.b*Real.sin z := by
  have tr := transport_trig hz
  have hchart := state_low_chart s hs
  let f : ℝ := lowDualA (17/10)+(59/25)*Real.cos z
  let g : ℝ := lowDualB (17/10)-(59/25)*Real.sin z
  have hf : (253/100:ℝ)<f := by
    dsimp [f,lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u]
    linarith [tr.1]
  have hcurv : 2*(7/10)*(a1+1/2)≤f := by linarith [a1_precise.2]
  have hd := low_source_derivative_bound (mu := (17/10:ℝ)) (lambda := (59/25:ℝ))
    (e := (13/200:ℝ)) hz (by norm_num) (show 0≤f by linarith)
    (by norm_num [lowDualA,lowDualB,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v])
  have hh := circle_endpoint_loss
    (x := s.a+1/2) (t := s.b+1/2) (X := a1+1/2) (T := b1+1/2)
    (a := f) (b := g) (e := (13/200:ℝ)) (k := (7/10:ℝ)) (loss := (1/625:ℝ))
    ((s.outer_eq (by simp [hs,Branch.type])).trans endpoint_circle.symm)
    (by linarith [a1_precise.1]) (by linarith) (by norm_num) hcurv
    (by linarith [hchart.2.2]) hd (by norm_num)
  have hcut := dual_endpoint_constants.1
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_low]
  rw [arcK_low,A_b1] at hcut
  rw [← hchart.1]
  dsimp [f,g] at hh
  nlinarith only [hh,hcut]

theorem low_source_nonlow_target (s : State) (hs : s.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    -1673/10000-(93/20)*a1*Real.cos z+(93/20)*b1*Real.sin z<
      K s 5-(93/20)*s.a*Real.cos z+(93/20)*s.b*Real.sin z := by
  have tr := transport_trig hz
  have hchart := state_low_chart s hs
  let f : ℝ := lowDualA 5+(93/20)*Real.cos z
  let g : ℝ := lowDualB 5-(93/20)*Real.sin z
  have hf : 0≤f := by
    dsimp [f,lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u]
    linarith [tr.1]
  have hd := low_source_derivative_bound (mu := (5:ℝ)) (lambda := (93/20:ℝ))
    (e := (0:ℝ)) hz (by norm_num) hf
    (by norm_num [lowDualA,lowDualB,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v])
  have hh := circle_endpoint_min
    (x := s.a+1/2) (t := s.b+1/2) (X := a1+1/2) (T := b1+1/2) (a := f) (b := g)
    ((s.outer_eq (by simp [hs,Branch.type])).trans endpoint_circle.symm)
    (by linarith [a1_precise.1]) hf (by linarith [hchart.2.2]) (by simpa using hd)
  have hcut := dual_endpoint_constants.2.1
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_low]
  rw [arcK_low,A_b1] at hcut
  rw [← hchart.1]
  dsimp [f,g] at hh
  nlinarith only [hh,hcut]

theorem sourceNorm_nonnegative (mu lambda z : ℝ) : 0≤ sourceNorm mu lambda z :=
  Real.sqrt_nonneg _

theorem sourceNorm_sq (mu lambda z : ℝ) :
    (sourceNorm mu lambda z)^2=midDualA mu^2+midDualB mu^2+lambda^2+
      2*lambda*(midDualA mu*Real.cos z-midDualB mu*Real.sin z) := by
  rw [sourceNorm,Real.sq_sqrt (by positivity)]
  linear_combination lambda^2*(Real.sin_sq_add_cos_sq z)

theorem middle_source_support (s : State) (hs : s.branch=.middle) (mu lambda z : ℝ) :
    midShiftC mu+(lambda/2)*(Real.cos z-Real.sin z)-R*sourceNorm mu lambda z≤
      K s mu-lambda*s.a*Real.cos z+lambda*s.b*Real.sin z := by
  have hcircle := s.outer_eq (by simp [hs,Branch.type])
  have hh := circle_linear_lower hcircle (-midDualA mu-lambda*Real.cos z)
    (-midDualB mu+lambda*Real.sin z)
  have hnorm : Real.sqrt ((-midDualA mu-lambda*Real.cos z)^2+
      (-midDualB mu+lambda*Real.sin z)^2)=sourceNorm mu lambda z := by
    unfold sourceNorm
    congr 1
    ring
  rw [hnorm] at hh
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_middle,
    ← (state_mid_chart s hs).1]
  dsimp [midShiftC]
  nlinarith only [hh]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open Polynomial FrameCircleArc FrameLowArc FrameMidArc GlobalOuterAnchor

def endpointScalar (mu lambda K g bonus z : ℝ) : ℝ :=
  (1+mu)*(Real.pi/2-z)-mu*(cap-bonus)+K+g+lambda*GlobalOuterAnchor.width (-z)+
    mu*(9/50)*frameCost z-lambda*a1*Real.cos z+lambda*b1*Real.sin z
def circleBase (mu lambda K g bonus z : ℝ) : ℝ :=
  (1+mu)*(Real.pi/2-z)-mu*(cap-bonus)+K+g+lambda/2-mu*(9/100)+
    (lambda+mu*(9/100))*Real.cos z+mu*(9/100)*Real.sin z
def circleScalar (mu lambda K g bonus z : ℝ) : ℝ :=
  circleBase mu lambda K g bonus z-R*sourceNorm mu lambda z

theorem S7_le_sin {z : ℝ} (hz : 0≤z) : Arithmetic.sin7 z≤Real.sin z := by
  simpa only [Arithmetic.sin7] using sin_lower_seven hz

@[simp] theorem Am_cast (mu : ℚ) : (DualPolynomial.Am mu:ℝ)=midDualA (mu:ℝ) := by
  norm_num [DualPolynomial.Am,midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p]
@[simp] theorem Bm_cast (mu : ℚ) : (DualPolynomial.Bm mu:ℝ)=midDualB (mu:ℝ) := by
  norm_num [DualPolynomial.Bm,midDualB,rho,FrameHighArc.v,FrameMidArc.q]

theorem endpoint_polynomial_lower (mu lambda K g bonus : ℚ)
    (hmu : (0:ℝ)≤(mu:ℝ)) (hl : (0:ℝ)≤(lambda:ℝ))
    (hcos : (lambda:ℝ)*(1/2-(DualPolynomial.a1Upper:ℝ))+(mu:ℝ)*(9/100)≤0)
    (hsin : 0≤(lambda:ℝ)*(1/2+(DualPolynomial.b1Lower:ℝ))+(mu:ℝ)*(9/100))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z (DualPolynomial.endpointPoly mu lambda K g bonus)≤
      endpointScalar (mu:ℝ) (lambda:ℝ) (K:ℝ) (g:ℝ) (bonus:ℝ) z := by
  have tr := transport_trig hz
  have hpi := mul_le_mul_of_nonneg_left
    (show (DualPolynomial.piLow:ℝ)≤Real.pi by
      norm_num [DualPolynomial.piLow]; linarith [Arithmetic.pi_hand_enclosure.1])
    (show 0≤(1+(mu:ℝ))/2 by linarith)
  have ha : a1≤(DualPolynomial.a1Upper:ℝ) := by
    norm_num [DualPolynomial.a1Upper]
    linarith [a1_precise.2]
  have hb : (DualPolynomial.b1Lower:ℝ)≤b1 := by
    norm_num [DualPolynomial.b1Lower]
    exact b1_precise.1.le
  have hpa := mul_nonneg (mul_nonneg hl (show 0≤Real.cos z by linarith [tr.1]))
    (sub_nonneg.mpr ha)
  have hpb := mul_nonneg (mul_nonneg hl tr.2.2.1) (sub_nonneg.mpr hb)
  have hc := mul_le_mul_of_nonpos_left (Arithmetic.cos_le_cos8 hz.1) hcos
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1) hsin
  simp only [DualPolynomial.endpointPoly,map_add,map_sub,map_mul,aeval_C,aeval_X,
    DualPolynomial.C8_eval,DualPolynomial.S7_eval,eq_ratCast]
  push_cast
  dsimp [endpointScalar]
  rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  dsimp [frameCost,DualPolynomial.capQ,cap]
  linarith only [hpi,hpa,hpb,hc,hs]

theorem low_low_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)+1/625<endpointScalar (17/10) (59/25) (2113/2500) (-4029/2500) 0 z := by
  have hh := endpoint_polynomial_lower (17/10) (59/25) (2113/2500) (-4029/2500) 0
    (by norm_num) (by norm_num)
    (by norm_num [DualPolynomial.a1Upper]) (by norm_num [DualPolynomial.b1Lower]) hz
  have hp := DualPolynomial.lowLow_positive hz
  simp only [DualPolynomial.lowLow,map_sub,aeval_C] at hp
  norm_num [DualPolynomial.eta] at hp hh ⊢
  linarith

theorem low_nonlow_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<endpointScalar 5 (93/20) (-1673/10000) (-1357/1000) (93/10000) z := by
  have hh := endpoint_polynomial_lower 5 (93/20) (-1673/10000) (-1357/1000) (93/10000)
    (by norm_num) (by norm_num)
    (by norm_num [DualPolynomial.a1Upper]) (by norm_num [DualPolynomial.b1Lower]) hz
  have hp := DualPolynomial.lowNonlow_positive hz
  simp only [DualPolynomial.lowNonlow,map_sub,aeval_C] at hp
  norm_num [DualPolynomial.eta] at hp hh ⊢
  linarith

theorem norm_polynomial_upper (mu lambda : ℚ)
    (hl : (0:ℝ)≤(lambda:ℝ)) (ha : 0≤ midDualA (mu:ℝ)) (hb : 0≤ midDualB (mu:ℝ))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (sourceNorm (mu:ℝ) (lambda:ℝ) z)^2≤aeval z (DualPolynomial.normSqPoly mu lambda) := by
  have hc := mul_le_mul_of_nonneg_left (Arithmetic.cos_le_cos8 hz.1) ha
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1) hb
  have hh := mul_le_mul_of_nonneg_left (show midDualA (mu:ℝ)*Real.cos z-
      midDualB (mu:ℝ)*Real.sin z ≤ midDualA (mu:ℝ)*Arithmetic.cos8 z-
        midDualB (mu:ℝ)*Arithmetic.sin7 z by linarith)
    (show 0≤2*(lambda:ℝ) by linarith)
  rw [sourceNorm_sq]
  simp only [DualPolynomial.normSqPoly,map_add,map_sub,map_mul,map_pow,aeval_C,
    DualPolynomial.C8_eval,DualPolynomial.S7_eval,eq_ratCast]
  push_cast
  simp only [Am_cast,Bm_cast]
  linarith only [hh]

theorem distance_polynomial_lower (mu lambda K g bonus : ℚ)
    (hmu : (0:ℝ)≤(mu:ℝ)) (hl : (0:ℝ)≤(lambda:ℝ))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z (DualPolynomial.distancePoly mu lambda K g bonus)≤
      circleBase (mu:ℝ) (lambda:ℝ) (K:ℝ) (g:ℝ) (bonus:ℝ) z-957/1000 := by
  have hp := mul_le_mul_of_nonneg_left
    (show (DualPolynomial.piLow:ℝ)≤Real.pi by
      norm_num [DualPolynomial.piLow]; linarith [Arithmetic.pi_hand_enclosure.1])
    (show 0≤(1+(mu:ℝ))/2 by linarith)
  have hc := mul_le_mul_of_nonneg_left (Arithmetic.cos10_le_cos hz.1)
    (show 0≤(lambda:ℝ)+(mu:ℝ)*(9/100) by positivity)
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1)
    (show 0≤(mu:ℝ)*(9/100) by positivity)
  simp only [DualPolynomial.distancePoly,map_add,map_sub,map_mul,aeval_C,aeval_X,
    DualPolynomial.C10_eval,DualPolynomial.S7_eval,eq_ratCast]
  push_cast
  dsimp [circleBase,DualPolynomial.capQ,DualPolynomial.eta,cap]
  linarith only [hp,hc,hs]

theorem quadratic_norm_envelope {p D N S r upper : ℝ}
    (hp : 0<p) (hN : 0≤N) (hu : 0≤upper) (hr : r≤upper)
    (hS : N^2≤S) (hP : 0<2*p*D-upper*(p^2+S)) : r*N<D := by
  have h1 := mul_nonneg hu (sq_nonneg (p-N))
  have h2 := mul_nonneg hu (sub_nonneg.mpr hS)
  have hscaled : 0<2*p*(D-upper*N) := by nlinarith only [h1,h2,hP]
  have hD : upper*N<D := by
    have hh := (mul_pos_iff_of_pos_left (show 0<2*p by linarith)).1 hscaled
    linarith
  exact (mul_le_mul_of_nonneg_right hr hN).trans_lt hD

theorem middle_low_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<circleScalar (17/10) (59/25) (109221/10000) (-4029/2500) (93/10000) z := by
  have hp := DualPolynomial.midLow_positive hz
  simp only [DualPolynomial.midLow,map_sub,map_mul,map_add,map_pow,aeval_C,eq_ratCast,
    Rat.cast_ofNat] at hp
  have hS := norm_polynomial_upper (17/10) (59/25) (by norm_num)
    (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
    (by norm_num [midDualB,rho,FrameHighArc.v,FrameMidArc.q]) hz
  have hR : R≤(DualPolynomial.radiusUpper:ℝ) := by
    have := FrameHighArc.radius_bound
    norm_num [DualPolynomial.radiusUpper,FrameHighArc.radiusUpper] at this ⊢
    exact this.le
  have hN := quadratic_norm_envelope (DualPolynomial.pLow_positive hz)
    (sourceNorm_nonnegative _ _ z)
    (by norm_num [DualPolynomial.radiusUpper]) hR hS hp
  have hd := distance_polynomial_lower (17/10) (59/25) (109221/10000)
    (-4029/2500) (93/10000) (by norm_num) (by norm_num) hz
  push_cast at hd hN
  dsimp [circleScalar]
  linarith only [hd,hN]

theorem middle_nonlow_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<circleScalar 5 (93/20) (115297/5000) (-1357/1000) (43/2500) z := by
  have hp := DualPolynomial.midNonlow_positive hz
  simp only [DualPolynomial.midNonlow,map_sub,map_mul,map_add,map_pow,aeval_C,eq_ratCast,
    Rat.cast_ofNat] at hp
  have hS := norm_polynomial_upper 5 (93/20) (by norm_num)
    (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
    (by norm_num [midDualB,rho,FrameHighArc.v,FrameMidArc.q]) hz
  have hR : R≤(DualPolynomial.radiusUpper:ℝ) := by
    have := FrameHighArc.radius_bound
    norm_num [DualPolynomial.radiusUpper,FrameHighArc.radiusUpper] at this ⊢
    exact this.le
  have hN := quadratic_norm_envelope (DualPolynomial.pNonlow_positive hz)
    (sourceNorm_nonnegative _ _ z)
    (by norm_num [DualPolynomial.radiusUpper]) hR hS hp
  have hd := distance_polynomial_lower 5 (93/20) (115297/5000)
    (-1357/1000) (43/2500) (by norm_num) (by norm_num) hz
  push_cast at hd hN
  dsimp [circleScalar]
  linarith only [hd,hN]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end
