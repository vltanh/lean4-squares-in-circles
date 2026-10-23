module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperOnePolynomial
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperZero

/-!
# The exceptional upper primary owner's complete diagonal branch

Uncompiled transcription of Sections 3--4 of the three-family note.
The two polynomial signs are used exactly in the two signs of z to
bound omega'. The resulting angular curvature, join value and join
slope imply the stated .9004 reference bound on the entire branch.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.OneDiagonal
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def numerator (x : ℝ) : ℝ := z0+(Q0-1-z0^2)*Real.sin x+z0*(Real.sin x)^2

theorem numerator_bounds {x : ℝ} (hx : DiagonalDomain x) :
    0<numerator x ∧ numerator x≤OnePolynomial.N (Real.sin x) := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hz0 : (499/1250:ℝ)<z0 ∧ z0<(2/5:ℝ) := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,ShortMixedZero.fine_diagonal_bounds.2]
  have hcoef : 0<Q0-1-z0^2 ∧ Q0-1-z0^2<(27563/10000:ℝ) := by
    norm_num [Q0]
    constructor <;> nlinarith
  have hterm := mul_nonneg hcoef.1.le ht.2.2.1
  have hterm2 := mul_nonneg hz0.1.le (sq_nonneg (Real.sin x))
  have hh := mul_le_mul_of_nonneg_right hcoef.2.le ht.2.2.1
  have hh2 := mul_le_mul_of_nonneg_right hz0.2.le (sq_nonneg (Real.sin x))
  dsimp [numerator,OnePolynomial.N]
  constructor <;> linarith

theorem omegaD_formula (x : ℝ) : omegaD x=numerator x/(T x)^3 := by
  dsimp [omegaD,SecondWord.SameZero.PJ.Diagonal.factorD,numerator]
  ring

theorem omega_comparison {x m α : ℝ} (hx : DiagonalDomain x)
    (hα : 0≤α) (hm : 1<m) (hmT : m≤T x)
    (hpoly : OnePolynomial.N (Real.sin x)<α*m*(m-1+(Real.sin x)^2/2)^2) :
    omegaD x≤α*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hcos := cosine_upper_square (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hT : 0<T x := by linarith [hm,hmT]
  have hg0 : 0≤m-1+(Real.sin x)^2/2 := by nlinarith [sq_nonneg (Real.sin x)]
  have hg1 : m-1+(Real.sin x)^2/2≤T x-Real.cos x := by linarith
  have hsquare : (m-1+(Real.sin x)^2/2)^2≤(T x-Real.cos x)^2 := by nlinarith
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hmT hα) hsquare
    (sq_nonneg (m-1+(Real.sin x)^2/2))
    (mul_nonneg hα hT.le)
  have hn := (numerator_bounds hx).2
  have hclear : numerator x≤α*T x*(T x-Real.cos x)^2 := by linarith
  rw [omegaD_formula]
  dsimp [omega,SecondWord.SameZero.PJ.Diagonal.factor]
  apply (div_le_iff₀ (pow_pos hT 3)).2
  field_simp [hT.ne']
  nlinarith

theorem nonnegative_factor {x : ℝ} (hx : DiagonalDomain x) (hz : 0≤z x) :
    omegaD x≤(73/100:ℝ)*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hs : Real.sin x∈Icc (0:ℝ) (2/5) := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀] at hz
    exact ⟨ht.2.2.1,by linarith [ShortMixedZero.fine_diagonal_bounds.2]⟩
  have hm : 1<OnePolynomial.lowerT (Real.sin x) := by
    dsimp [OnePolynomial.lowerT]
    linarith [hs.1]
  have hT : OnePolynomial.lowerT (Real.sin x)≤T x := by
    have hp := OnePolynomial.lowerT_square hs
    have hz' : z x≤(2/5:ℝ)-Real.sin x := by
      dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
      linarith [ShortMixedZero.fine_diagonal_bounds.2]
    have hrad := (diagonal_radical hx).2.2
    have hTpos := (diagonal_radical hx).1
    nlinarith
  exact omega_comparison hx (by norm_num) hm hT
    (by linarith [OnePolynomial.nonnegative_polynomial hs])

theorem negative_factor {x : ℝ} (hx : DiagonalDomain x) (hz : z x<0) :
    omegaD x≤(9/10:ℝ)*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hpoly := OnePolynomial.negative_polynomial
    (show Real.sin x∈Icc (0:ℝ) (129/200) from ⟨ht.2.2.1,ht.2.2.2.1.le⟩)
  apply omega_comparison hx (by norm_num : (0:ℝ)≤9/10)
    (by norm_num : (1:ℝ)<1963/1000) (negative_z_data hx hz).2.2.1.le
  linarith

theorem diagonal_ratio_increasing {e : ℝ} (he : IsEvent e) :
    StrictMonoOn (fun x => V x/U x) (Icc e (7/10)) := by
  apply strictMonoOn_of_hasDeriv_pos
    (fun x hx => (diagonal_ratio_hasDerivAt (after_diagonal_domain he hx)).continuousAt.continuousWithinAt)
    (fun x hx => diagonal_ratio_hasDerivAt (after_diagonal_domain he (Ioo_subset_Icc_self hx)))
  intro x hx
  have hd := after_diagonal_domain he (Ioo_subset_Icc_self hx)
  exact div_pos (mul_pos (by norm_num [Q0])
    (by linarith [(diagonal_omega_bounds hd).1]))
    (sq_pos_of_pos (by linarith [(diagonal_coordinate_bounds hd).1]))

theorem negative_ratio {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) (hz : z x<0) :
    (499/1250:ℝ)<V x/U x := by
  have hslo : Real.sin e<z0 := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [(event_trig he).2.1,ShortMixedZero.fine_diagonal_bounds.1]
  have hshi : z0<Real.sin x := by dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z] at hz; linarith
  obtain ⟨y,hy,hyEq⟩ := intermediate_value_Icc hx.1 Real.continuous_sin.continuousOn
    (show z0∈Icc (Real.sin e) (Real.sin x) from ⟨hslo.le,hshi.le⟩)
  have hxy : y<x := by
    apply lt_of_le_of_ne hy.2
    intro h
    subst y
    linarith
  have hy' : y∈Icc e (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
  have hd := after_diagonal_domain he hy'
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hT := (diagonal_radical hd).1
  have hz0 : 0<z0 := by linarith [hslo,(event_trig he).1]
  have hzEq : z y=0 := by dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z]; rw [hyEq]; ring
  have hratio : z0≤V y/U y := by
    apply (le_div_iff₀ (by linarith [(diagonal_coordinate_bounds hd).1] : 0<U y)).2
    have hp := mul_nonneg (mul_nonneg (by linarith : 0≤T y) hz0.le) (sub_nonneg.mpr ht.2.1)
    dsimp [U,V,SecondWord.SameZero.PJ.Diagonal.horizontal,SecondWord.SameZero.PJ.Diagonal.vertical]
    rw [hzEq,hyEq]
    nlinarith
  have hm := diagonal_ratio_increasing he hy' hx hxy
  have hz0' : (499/1250:ℝ)<z0 := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  exact hz0'.trans_le (hratio.trans hm.le)

theorem H_positive {x : ℝ} (hx : DiagonalDomain x) : 0<t 1*U x-P 1*V x := by
  have hc := diagonal_coordinate_bounds hx
  norm_num [P,t]
  nlinarith [hc.1,hc.2.2.2.1]

theorem curvature_from_factor {x α u r w : ℝ} (hx : DiagonalDomain x)
    (hα : omegaD x≤α*(omega x)^2)
    (hu : 0<u) (hU : u<U x) (hr : r≤V x/U x)
    (hw : 0<w) (hω : w<omega x)
    (hcoef : 0<(P 1-α*t 1)+(t 1+α*P 1)*r)
    (hcoef' : 0≤t 1+α*P 1) :
    w^2*u*((P 1-α*t 1)+(t 1+α*P 1)*r)<G2 1 x := by
  have hU0 : 0<U x := hu.trans hU
  have hratio : r*U x≤V x := (le_div_iff₀ hU0).1 hr
  have hrprod := mul_le_mul_of_nonneg_left hratio hcoef'
  have hbracket : u*((P 1-α*t 1)+(t 1+α*P 1)*r)<
      P 1*U x+t 1*V x-α*(t 1*U x-P 1*V x) := by
    have hp := mul_lt_mul_of_pos_right hU hcoef
    nlinarith
  have hw2 : w^2<(omega x)^2 := by nlinarith
  have hpos : 0<u*((P 1-α*t 1)+(t 1+α*P 1)*r) := mul_pos hu hcoef
  have hprod := mul_lt_mul hw2 hbracket hpos.le (sq_pos_of_pos (hw.trans hω))
  have hdrop := mul_le_mul_of_nonneg_right hα (H_positive hx).le
  dsimp [G2]
  nlinarith

theorem curvature {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (1/50:ℝ)<G2 1 x := by
  have hd := after_diagonal_domain he hx
  by_cases hz : 0≤z x
  · have hh := curvature_from_factor hd (nonnegative_factor hd hz)
      (by norm_num : (0:ℝ)<9/5) (nonnegative_z_geometry hd hz).2.1
      (show (5223/20000:ℝ)≤V x/U x from rho_bounds.1.le.trans (diagonal_ratio hd).2)
      (by norm_num : (0:ℝ)<483/1000) (diagonal_omega_bounds hd).1
      (by norm_num [P,t]) (by norm_num [P,t])
    norm_num [P,t] at hh
    linarith
  · have hzn := lt_of_not_ge hz
    have hh := curvature_from_factor hd (negative_factor hd hzn)
      (by norm_num : (0:ℝ)<1399/1000)
      (show (1399/1000:ℝ)<U x by linarith [(diagonal_coordinate_bounds hd).1])
      (negative_ratio he hx hzn).le
      (by norm_num : (0:ℝ)<133/250) (negative_z_data hd hzn).2.2.2
      (by norm_num [P,t]) (by norm_num [P,t])
    norm_num [P,t] at hh
    linarith

theorem J_increasing {e : ℝ} (he : IsEvent e) : MonotoneOn (J 1) (Icc e (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (J_hasDerivAt 1 (after_diagonal_domain he hx)).continuousAt.continuousWithinAt)
    (fun x hx => J_hasDerivAt 1 (after_diagonal_domain he (Ioo_subset_Icc_self hx)))
  intro x hx
  have hd := after_diagonal_domain he (Ioo_subset_Icc_self hx)
  have hc := diagonal_coordinate_bounds hd
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hw := diagonal_omega_bounds hd
  have hU : 0<U x := by linarith [hc.1]
  have hid : J1 1 x*(U x)^2=(p 1+q 1)*z x*U x+
      ((p 1+q 1)*Real.sin x+P 1)*Q0*omega x := by
    dsimp [J1]
    field_simp [hU.ne']
    ring
  have hpositive : 0<J1 1 x*(U x)^2 := by
    rw [hid]
    by_cases hz : 0≤z x
    · have h1 := mul_nonneg (mul_nonneg (by norm_num [p,q] : 0≤p 1+q 1) hz) hU.le
      have h2 : 0<((p 1+q 1)*Real.sin x+P 1)*Q0*omega x := by
        apply mul_pos
        · apply mul_pos
          · norm_num [p,q,P]
            nlinarith [ht.2.2.1]
          · norm_num [Q0]
        · linarith [hw.1]
      linarith
    · have hn := negative_z_data hd (lt_of_not_ge hz)
      have hzlo := (diagonal_z_bounds hd).1
      have hUhi : U x<(494697/250000:ℝ) :=
        (diagonal_U_le_T hd).trans_lt ((diagonal_radical hd).2.1.trans_lt radius_fine.2)
      have hnegative := mul_le_mul
        (show -z x≤(123/500:ℝ) by linarith) hUhi.le hU.le (by norm_num)
      have hpositive := mul_le_mul
        (show (p 1+q 1)*(499/1250)+P 1≤(p 1+q 1)*Real.sin x+P 1 by
          norm_num [p,q,P]; nlinarith [hn.1]) hn.2.2.2.le
          (by norm_num) (by norm_num [p,q,P]; nlinarith [hn.1])
      norm_num [p,q,P,Q0] at hpositive ⊢
      nlinarith
  exact ((mul_pos_iff_of_pos_right (sq_pos_of_pos hU)).1 hpositive).le

theorem J_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    -(71/1000:ℝ)<J 1 x := by
  have hm := J_increasing he ⟨le_rfl,(event_bounds he).2.2.2⟩ hx hx.1
  rw [J_at_event 1 he] at hm
  exact (H_one_at_event he).trans_le hm

theorem join_value {e : ℝ} (he : IsEvent e) : (225169/250000:ℝ)<G 1 e := by
  have heq := diagonal_at_event_coordinates he
  rw [G,heq.1,heq.2]
  have hp : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have ha := ShortOuterZero.fine_axial_bounds.2
  have hd := ShortMixedZero.fine_diagonal_bounds.2
  norm_num [c,p,q,P,t]
  linarith [(event_bounds he).1]

def joinCosBox {e : ℝ} (he : IsEvent e) : Interval (Real.cos e) :=
  Interval.of_bounds ⟨(event_trig he).2.2.1.le,(event_trig he).2.2.2.le⟩
def joinSinBox {e : ℝ} (he : IsEvent e) : Interval (Real.sin e) :=
  Interval.of_bounds ⟨(event_trig he).1.le,(event_trig he).2.1.le⟩
def joinTBox {e : ℝ} (he : IsEvent e) : Interval (T e) := by
  convert (((axial.add (Interval.point (1/2))).mul (joinCosBox he)).add
    ((Interval.point (1/2)).mul (joinSinBox he))) using 1
  have hp := (diagonal_projection (diagonal_at_event he).1).1
  rw [(diagonal_at_event_coordinates he).1,(diagonal_at_event_coordinates he).2] at hp
  linarith

theorem join_slope {e : ℝ} (he : IsEvent e) : -(7/2500:ℝ)<G1 1 e := by
  have hden : 0<(joinTBox he).lo := by
    dsimp [joinTBox,joinCosBox,joinSinBox]
    mixed_fixed
  let W := (Interval.point 1).sub ((joinCosBox he).div (joinTBox he) hden)
  let H := ((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
    (Interval.point (P 1/2))
  let E := (Interval.point 1).sub (H.mul W)
  have hv : E.lo≤G1 1 e := by
    have hh := E.mem.1
    dsimp [E,H,W,G1,omega,SecondWord.SameZero.PJ.Diagonal.factor] at *
    rw [(diagonal_at_event_coordinates he).1,(diagonal_at_event_coordinates he).2]
    linarith
  have hnum : -(7/2500:ℝ)<E.lo := by
    dsimp [E,H,W,joinTBox,joinCosBox,joinSinBox,t,P]
    mixed_fixed
  exact hnum.trans_le hv

theorem reference_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (2251/2500:ℝ)<G 1 x := by
  have ht := curvature_tangent hx ⟨le_rfl,(event_bounds he).2.2.2⟩
    (fun u hu => G_hasDerivAt 1 (after_diagonal_domain he hu))
    (fun u hu => G1_hasDerivAt 1 (after_diagonal_domain he hu))
    (fun u hu => (curvature he hu).le)
  have hp := mul_le_mul_of_nonneg_right (join_slope he).le (sub_nonneg.mpr hx.1)
  have hs := sq_nonneg ((1/50)*(x-e)-7/2500)
  nlinarith [join_value he]

theorem after_contact {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (4489/5000:ℝ)<value 1 B x := by
  have hx' : x∈Icc e (7/10) := ⟨hx,hd.2.1.2⟩
  have hxd := after_diagonal_domain he hx'
  have hD := diagonal_contact_domain hxd
  have hJ := J_lower he hx'
  rw [J_first 1 hxd] at hJ
  have hh := contact_remainder 1 hD hd (diagonal_lower_target hd hxd)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)≤71/1000) hJ.le
    (fun E hE => by simpa [curvatureFloor] using
      (Upper.curvature 1 (between_domain hD hd hE)).le)
  have hG := reference_lower he hx'
  rw [G_value 1 hxd] at hG
  norm_num at hh
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.OneDiagonal
