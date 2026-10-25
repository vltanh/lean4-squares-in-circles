module

public import SquaresInCircles.Eight.TableFree.CrossedClampRates
public import SquaresInCircles.Eight.TableFree.MiddleHardCap
public import SquaresInCircles.Eight.TableFree.CircleGeometry

/-!
# The actual-circle inverse HG cap on the complete clamp interval

Uncompiled source draft.  The inverse is an explicit positive rotated
circle point.  Its transverse corner decreases with the HG error, stays
strictly between .52 and .75, and therefore never encounters the G
tangent floor.  Its induced A cap is always greater than .92.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedClampInverse

def M (b r : ℝ) : ℝ := 1/2+Real.cos r+Real.sin r-b
def W (q b r : ℝ) : ℝ := Real.sqrt (q-(M b r)^2)
def D (q b r : ℝ) : ℝ := M b r*Real.cos r-W q b r*Real.sin r
def X (q b r : ℝ) : ℝ := M b r*Real.sin r+W q b r*Real.cos r
def D1 (q b r : ℝ) : ℝ := X q b r*(Real.cos r-Real.sin r-W q b r)/W q b r
def cap (q b r : ℝ) : ℝ := Real.sqrt (q-(D q b r+1)^2)
def point (q b r : ℝ) : SignedPoint := SignedPoint.outerAt q (1/2-D q b r)

structure Domain (q b : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  tangent : b∈Ioo (3/4 : ℝ) (9/10)

theorem trig {r : ℝ} (hr : r∈Icc (0:ℝ) (1/25)) :
    r∈Icc 0 frameCap ∧ 0≤Real.sin r ∧ Real.sin r≤1/25 ∧
      1249/1250≤Real.cos r ∧ 1≤Real.cos r+Real.sin r := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have hs := (transport_trig hi).2.2.1
  have hsu := (Real.sin_le hr.1).trans hr.2
  have h2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hc : 1249/1250≤Real.cos r := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := r)]
  have hw := edgeWidth_ge_one r
  rw [edgeWidth_positive_formula hi] at hw
  exact ⟨hi,hs,hsu,hc,by linarith⟩

theorem M_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    M b r∈Ioo (3/5 : ℝ) (79/100) := by
  have ht := trig hr
  dsimp [M]
  constructor <;> linarith [S.tangent.1,S.tangent.2,ht.2.2.1,ht.2.2.2.2,Real.cos_le_one r]

theorem W_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    W q b r∈Ioo (9/5 : ℝ) (99/50) ∧ (W q b r)^2=q-(M b r)^2 := by
  have hm := M_bounds S hr
  have hml : 0≤M b r := by linarith [hm.1]
  have hm2 := pow_lt_pow_left₀ hm.2 hml (by decide : (2:ℕ)≠0)
  have hrad : 0≤q-(M b r)^2 := by
    have hq := S.floor
    dsimp [qLow] at hq
    nlinarith
  have hw2 : (W q b r)^2=q-(M b r)^2 := Real.sq_sqrt hrad
  have hw0 : 0≤W q b r := Real.sqrt_nonneg _
  have hqL := S.floor
  have hqU := S.ceiling
  dsimp [qLow,qCap] at hqL hqU
  refine ⟨⟨?_,?_⟩,hw2⟩ <;> nlinarith [sq_nonneg (M b r)]

theorem X_pos {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    0<X q b r := by
  have ht := trig hr
  have hm := M_bounds S hr
  have hw := W_bounds S hr
  have hp := mul_nonneg (show 0≤M b r by linarith [hm.1]) ht.2.1
  have hq := mul_pos (show 0<W q b r by linarith [hw.1.1])
    (show 0<Real.cos r by linarith [ht.2.2.2.1])
  dsimp [X]
  linarith

theorem norm {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    (X q b r)^2+(D q b r)^2=q := by
  have hw := (W_bounds S hr).2
  calc
    _ = ((M b r)^2+(W q b r)^2)*((Real.sin r)^2+(Real.cos r)^2) := by dsimp [X,D]; ring
    _ = q := by rw [Real.sin_sq_add_cos_sq,mul_one,hw]; ring

theorem contact (q b r : ℝ) :
    X q b r*Real.sin r+D q b r*Real.cos r=M b r := by
  dsimp [X,D]
  linear_combination M b r*Real.sin_sq_add_cos_sq r

theorem reverse (q b r : ℝ) :
    X q b r*Real.cos r-D q b r*Real.sin r=W q b r := by
  dsimp [X,D]
  linear_combination W q b r*Real.sin_sq_add_cos_sq r

theorem M_hasDerivAt (b r : ℝ) : HasDerivAt (M b) (Real.cos r-Real.sin r) r := by
  have h : HasDerivAt (fun x => 1/2+Real.cos x+Real.sin x-b) (-Real.sin r+Real.cos r) r :=
    (((Real.hasDerivAt_cos r).const_add (1/2)).fun_add (Real.hasDerivAt_sin r)).sub_const b
  have e : Real.cos r-Real.sin r=-Real.sin r+Real.cos r := by ring
  rw [e]
  exact h

theorem W_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (W q b) (-M b r*(Real.cos r-Real.sin r)/W q b r) r := by
  have hw := W_bounds S hr
  have hr0 : q-(M b r)^2≠0 := by nlinarith [hw.1.1,hw.2]
  have hd := (((M_hasDerivAt b r).pow 2).const_sub q).sqrt hr0
  convert hd using 1
  · rfl
  · dsimp [W]
    field_simp [show Real.sqrt (q-(M b r)^2)≠0 by change W q b r≠0; linarith [hw.1.1]]

theorem D_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (D q b) (D1 q b r) r := by
  have hw := W_bounds S hr
  have hd := ((M_hasDerivAt b r).mul (Real.hasDerivAt_cos r)).sub
    ((W_hasDerivAt S hr).mul (Real.hasDerivAt_sin r))
  convert hd using 1
  · rfl
  · dsimp [D1,X]
    field_simp [show W q b r≠0 by linarith [hw.1.1]]
    ring

theorem D1_neg {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    D1 q b r<0 := by
  have hw := W_bounds S hr
  have ht := trig hr
  have hneg : Real.cos r-Real.sin r-W q b r<0 := by linarith [hw.1.1,ht.2.1,Real.cos_le_one r]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (X_pos S hr) hneg)
    (by linarith [hw.1.1])

theorem D_antitone {q b : ℝ} (S : Domain q b) :
    AntitoneOn (D q b) (Icc (0:ℝ) (1/25)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun r hr => (D_hasDerivAt S hr).continuousAt.continuousWithinAt
  · intro r hr
    exact D_hasDerivAt S (Ioo_subset_Icc_self hr)
  · intro r hr
    exact (D1_neg S (Ioo_subset_Icc_self hr)).le

theorem D_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    D q b r∈Ioo (13/25 : ℝ) (3/4) := by
  have ht := trig hr
  have hm := M_bounds S hr
  have hw := W_bounds S hr
  have hmc := mul_lt_mul_of_pos_right hm.1 (show 0<Real.cos r by linarith [ht.2.2.2.1])
  have hmc' := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by norm_num : (0:ℝ)≤3/5)
  have hws := mul_le_mul hw.1.2.le ht.2.2.1 ht.2.1 (by norm_num : (0:ℝ)≤99/50)
  have hD0 : D q b 0=3/2-b := by simp [D,M]; ring
  have hu := D_antitone S (show (0:ℝ)∈Icc 0 (1/25) by norm_num) hr hr.1
  rw [hD0] at hu
  constructor
  · dsimp [D]
    nlinarith
  · linarith [S.tangent.1]

theorem feasible {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    MiddleHardCap.Feasible q (D q b r) := by
  have hd := D_bounds S hr
  have hq := S.floor
  dsimp [qLow] at hq
  have h2 := pow_le_pow_left₀ (show 0≤D q b r+1 by linarith [hd.1])
    (show D q b r+1≤7/4 by linarith [hd.2]) 2
  exact ⟨S.ceiling,by linarith [hd.1],by nlinarith⟩

theorem cap_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    23/25<cap q b r ∧ cap q b r≤Real.sqrt (q-9/4) ∧
      cap q b r<1291/1000 ∧ (cap q b r)^2+(D q b r+1)^2=q := by
  have hd := D_bounds S hr
  have hfeas := feasible S hr
  have hrad : 0≤q-(D q b r+1)^2 := by linarith [hfeas.corner]
  have hs : (cap q b r)^2=q-(D q b r+1)^2 := Real.sq_sqrt hrad
  have hs0 : 0≤cap q b r := Real.sqrt_nonneg _
  have h2 := pow_le_pow_left₀ (show 0≤D q b r+1 by linarith [hd.1])
    (show D q b r+1≤7/4 by linarith [hd.2]) 2
  have hlow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤38/25)
    (show 38/25≤D q b r+1 by linarith [hd.1]) 2
  have hqL := S.floor
  have hqU := S.ceiling
  dsimp [qLow,qCap] at hqL hqU
  refine ⟨by nlinarith,?_,by nlinarith,by linarith⟩
  exact Real.sqrt_le_sqrt (by nlinarith [hd.1])

theorem cap_eq_hard_cap (q b r : ℝ) :
    cap q b r=HardSplitCap.cap q (D q b r) 0 := by
  simp [cap,HardSplitCap.cap,HardSplitCap.root,HardSplitCap.contact]

end SquaresInCircles.Eight.TableFree.CrossedClampInverse
