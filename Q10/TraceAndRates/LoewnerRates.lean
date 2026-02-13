import autoproof.Q10.TraceAndRates.RateTheory.Contraction

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

/-- Spectral condition number induced by interval endpoints. -/
def spectralKappa (mu L : Real) : Real := L / mu

theorem spectralKappa_gt_one_of_interval
    {mu L : Real}
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L) :
    1 < spectralKappa mu L := by
  unfold spectralKappa
  have hInvPos : 0 < mu⁻¹ := inv_pos.mpr hMuPos
  have hMul : mu * mu⁻¹ < L * mu⁻¹ := mul_lt_mul_of_pos_right hMuLtL hInvPos
  have hMuNe : mu ≠ 0 := ne_of_gt hMuPos
  have hLeft : mu * mu⁻¹ = (1 : Real) := by
    field_simp [hMuNe]
  have hRight : L * mu⁻¹ = L / mu := by
    simp [div_eq_mul_inv]
  simpa [hLeft, hRight] using hMul

/-- Direct condition-number order from Loewner scales:
if `κ₂ = c/β` and `κ₁ = (cδ)/1`, then `κ₂ ≤ κ₁` under `1 ≤ βδ`. -/
theorem spectralKappa_order_from_loewner_scales
    {beta c delta : Real}
    (hCnonneg : 0 ≤ c)
    (hBetaPos : 0 < beta)
    (hBetaDelta : 1 ≤ beta * delta) :
    spectralKappa beta c ≤ spectralKappa (1 : Real) (c * delta) := by
  have hDiv : (1 : Real) / beta ≤ delta := by
    exact (div_le_iff₀ hBetaPos).2 (by simpa [one_mul, mul_comm] using hBetaDelta)
  have hScaled : c * ((1 : Real) / beta) ≤ c * delta :=
    mul_le_mul_of_nonneg_left hDiv hCnonneg
  unfold spectralKappa
  simpa [div_eq_mul_inv] using hScaled

/-- Strict condition-number improvement from Loewner scales:
if `κ₂ = c/β` and `κ₁ = (cδ)/1`, then `κ₂ < κ₁` under `1 < βδ` and `c>0`. -/
theorem spectralKappa_lt_from_loewner_scales
    {beta c delta : Real}
    (hCpos : 0 < c)
    (hBetaPos : 0 < beta)
    (hBetaDelta : 1 < beta * delta) :
    spectralKappa beta c < spectralKappa (1 : Real) (c * delta) := by
  have hDiv : (1 : Real) / beta < delta := by
    exact (div_lt_iff₀ hBetaPos).2 (by simpa [one_mul, mul_comm] using hBetaDelta)
  have hScaled : c * ((1 : Real) / beta) < c * delta :=
    mul_lt_mul_of_pos_left hDiv hCpos
  unfold spectralKappa
  simpa [div_eq_mul_inv] using hScaled

theorem pcgRate_strict_of_spectralKappa_lt
    {mu1 L1 mu2 L2 : Real}
    (hMu1Pos : 0 < mu1) (hMu2Pos : 0 < mu2)
    (hMu1LtL1 : mu1 < L1) (hMu2LtL2 : mu2 < L2)
    (hKappaLt : spectralKappa mu2 L2 < spectralKappa mu1 L1) :
    pcgRate (spectralKappa mu2 L2) < pcgRate (spectralKappa mu1 L1) := by
  have hKappa1 : 1 < spectralKappa mu1 L1 :=
    spectralKappa_gt_one_of_interval hMu1Pos hMu1LtL1
  have hKappa2 : 1 < spectralKappa mu2 L2 :=
    spectralKappa_gt_one_of_interval hMu2Pos hMu2LtL2
  exact pcgRate_strict_mono
    (hKappa1 := hKappa2) (hKappa2 := hKappa1) hKappaLt

/-- Rate-factor order derived directly from Loewner-scale condition numbers. -/
theorem pcgRate_order_from_loewner_scales
    {beta c delta : Real}
    (hCnonneg : 0 ≤ c)
    (hBetaPos : 0 < beta)
    (hBetaLtC : beta < c)
    (hBetaDelta : 1 ≤ beta * delta)
    (hOneLtCd : (1 : Real) < c * delta) :
    pcgRate (spectralKappa beta c)
      ≤ pcgRate (spectralKappa (1 : Real) (c * delta)) := by
  have hKappa2 : 1 < spectralKappa beta c :=
    spectralKappa_gt_one_of_interval hBetaPos hBetaLtC
  have hKappa1 : 1 < spectralKappa (1 : Real) (c * delta) :=
    spectralKappa_gt_one_of_interval (show 0 < (1 : Real) by norm_num) hOneLtCd
  have hOrder : spectralKappa beta c ≤ spectralKappa (1 : Real) (c * delta) :=
    spectralKappa_order_from_loewner_scales
      (hCnonneg := hCnonneg) (hBetaPos := hBetaPos) (hBetaDelta := hBetaDelta)
  exact pcgRate_mono (hKappa1 := hKappa2) (hKappa2 := hKappa1) hOrder

/-- Strict rate improvement derived directly from strict Loewner-scale condition numbers. -/
theorem pcgRate_strict_from_loewner_scales
    {beta c delta : Real}
    (hCpos : 0 < c)
    (hBetaPos : 0 < beta)
    (hBetaLtC : beta < c)
    (hBetaDelta : 1 < beta * delta)
    (hOneLtCd : (1 : Real) < c * delta) :
    pcgRate (spectralKappa beta c)
      < pcgRate (spectralKappa (1 : Real) (c * delta)) := by
  have hKappaLt : spectralKappa beta c < spectralKappa (1 : Real) (c * delta) :=
    spectralKappa_lt_from_loewner_scales
      (hCpos := hCpos) (hBetaPos := hBetaPos) (hBetaDelta := hBetaDelta)
  exact pcgRate_strict_of_spectralKappa_lt
    (mu1 := (1 : Real)) (L1 := c * delta)
    (mu2 := beta) (L2 := c)
    (hMu1Pos := by norm_num)
    (hMu2Pos := hBetaPos)
    (hMu1LtL1 := hOneLtCd)
    (hMu2LtL2 := hBetaLtC)
    (hKappaLt := hKappaLt)

/-- Model tolerance-iteration order from direct Loewner-scale condition numbers. -/
theorem modelTolIter_order_from_loewner_scales
    {beta c delta err0 eps : Real}
    (hCnonneg : 0 ≤ c)
    (hBetaPos : 0 < beta)
    (hBetaLtC : beta < c)
    (hBetaDelta : 1 ≤ beta * delta)
    (hOneLtCd : (1 : Real) < c * delta)
    (hErr0 : 0 < err0) (hEps : 0 < eps) :
    modelTolIter (spectralKappa beta c) err0 eps
      (spectralKappa_gt_one_of_interval hBetaPos hBetaLtC) hErr0 hEps
      ≤
    modelTolIter (spectralKappa (1 : Real) (c * delta)) err0 eps
      (spectralKappa_gt_one_of_interval (show 0 < (1 : Real) by norm_num)
        hOneLtCd) hErr0 hEps := by
  have hKappa2 : 1 < spectralKappa beta c :=
    spectralKappa_gt_one_of_interval hBetaPos hBetaLtC
  have hKappa1 : 1 < spectralKappa (1 : Real) (c * delta) :=
    spectralKappa_gt_one_of_interval (show 0 < (1 : Real) by norm_num) hOneLtCd
  have hOrder : spectralKappa beta c ≤ spectralKappa (1 : Real) (c * delta) :=
    spectralKappa_order_from_loewner_scales
      (hCnonneg := hCnonneg) (hBetaPos := hBetaPos) (hBetaDelta := hBetaDelta)
  exact modelTolIter_le_of_kappa_le
    (hKappa1 := hKappa1) (hKappa2 := hKappa2)
    (hErr0 := hErr0) (hEps := hEps) hOrder

end
end Q10
end AutoProof
