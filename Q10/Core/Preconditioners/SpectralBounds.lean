import autoproof.Q10.Core.Preconditioners.LoewnerBridge

set_option autoImplicit false

open scoped BigOperators Kronecker MatrixOrder
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- If `gramMatrix ≤ g I` (small-factor Gram bounded in Loewner order),
then `M₂ ≤ (1 + g/λ) M₁` in quadratic form. -/
theorem precond2_quadratic_le_scaled_precond1_of_gram_upper
    (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpsd : P.K.PosSemidef)
    {g : Real}
    (hGramLe : gramMatrix P ≤ g • (1 : Matrix (Fin r) (Fin r) Real)) :
    QuadraticLe (precond2Matrix P) (((1 + g / P.lam) : Real) • precond1Matrix P) := by
  have hExtraLeMat : precond2Extra P ≤ g • defaultPreconditioner P := by
    have hKron :
        (gramMatrix P ⊗ₖ P.K)
          ≤ ((g • (1 : Matrix (Fin r) (Fin r) Real)) ⊗ₖ P.K) :=
      kron_left_mono_of_right_posSemidef (C := P.K) hKpsd hGramLe
    have hEq :
        ((g • (1 : Matrix (Fin r) (Fin r) Real)) ⊗ₖ P.K)
          = g • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K) := by
      simpa using (Matrix.smul_kronecker
        (r := g) (A := (1 : Matrix (Fin r) (Fin r) Real)) (B := P.K))
    simpa [precond2Extra, defaultPreconditioner] using hKron.trans_eq hEq
  have hExtraQ : QuadraticLe (precond2Extra P) (g • defaultPreconditioner P) :=
    quadraticLe_of_matrixLe (A := precond2Extra P) (B := g • defaultPreconditioner P) hExtraLeMat
  intro x
  have hM2Decomp :
      star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        = star x ⬝ᵥ (precond2Extra P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    rw [precond2Matrix_decompose]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hPre1Scale :
      star x ⬝ᵥ (precond1Matrix P *ᵥ x)
        = P.lam * (star x ⬝ᵥ (defaultPreconditioner P *ᵥ x)) := by
    simp [precond1Matrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hLamNe : P.lam ≠ 0 := ne_of_gt hLam
  have hDefaultAsPre1 :
      star x ⬝ᵥ (defaultPreconditioner P *ᵥ x)
        = (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) / P.lam := by
    apply (eq_div_iff hLamNe).2
    calc
      star x ⬝ᵥ (defaultPreconditioner P *ᵥ x) * P.lam
          = P.lam * (star x ⬝ᵥ (defaultPreconditioner P *ᵥ x)) := by ring
      _ = star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
            simpa [hPre1Scale] using hPre1Scale.symm
  have hGDefault :
      star x ⬝ᵥ ((g • defaultPreconditioner P) *ᵥ x)
        = (g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
    calc
      star x ⬝ᵥ ((g • defaultPreconditioner P) *ᵥ x)
          = g * (star x ⬝ᵥ (defaultPreconditioner P *ᵥ x)) := by
              simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ = g * ((star x ⬝ᵥ (precond1Matrix P *ᵥ x)) / P.lam) := by
            rw [hDefaultAsPre1]
      _ = (g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by ring
  have hExtra : star x ⬝ᵥ (precond2Extra P *ᵥ x)
      ≤ star x ⬝ᵥ ((g • defaultPreconditioner P) *ᵥ x) := hExtraQ x
  have hCore :
      star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        ≤ (1 + g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
    rw [hM2Decomp]
    calc
      star x ⬝ᵥ (precond2Extra P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x)
          ≤ star x ⬝ᵥ ((g • defaultPreconditioner P) *ᵥ x)
              + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by nlinarith
      _ = (g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x))
            + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by rw [hGDefault]
      _ = (1 + g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by ring
  calc
    star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        ≤ (1 + g / P.lam) * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := hCore
    _ = star x ⬝ᵥ ((((1 + g / P.lam) : Real) • precond1Matrix P) *ᵥ x) := by
          simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Automatic `M₂ ⪯ δ M₁` with an explicit scalar
`δ = 1 + (trace(gramMatrix)+1)/λ`, derived from PSD only. -/
theorem precond2_quadratic_le_scaled_precond1_auto
    (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpsd : P.K.PosSemidef) :
    QuadraticLe (precond2Matrix P)
      (((1 + ((gramMatrix P).trace + 1) / P.lam) : Real) • precond1Matrix P) := by
  have hGramPSD : (gramMatrix P).PosSemidef := gramMatrix_posSemidef (P := P)
  have hGramLe :
      gramMatrix P ≤ ((gramMatrix P).trace + 1) • (1 : Matrix (Fin r) (Fin r) Real) :=
    gramMatrix_le_tracePlusOne_smul_one (P := P)
  exact precond2_quadratic_le_scaled_precond1_of_gram_upper
    (P := P) (hLam := hLam) (hKpsd := hKpsd) (g := (gramMatrix P).trace + 1) (hGramLe := hGramLe)

/-- If the data term is quadratically bounded by `c * precond2Extra`,
then the dense operator is quadratically bounded by `c * precond2Matrix`.
This is a direct `A` vs `M₂` Loewner-style upper certificate. -/
theorem dense_quadratic_le_precond2_of_data_upper
    (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef)
    {c : Real} (hCone : 1 ≤ c)
    (hDataUpper : ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P *ᵥ x) ≤ c * (star x ⬝ᵥ (precond2Extra P *ᵥ x)))
    (x : Fin r × Fin n → Real) :
    star x ⬝ᵥ (denseMatrix P *ᵥ x) ≤ c * (star x ⬝ᵥ (precond2Matrix P *ᵥ x)) := by
  have hDenseDecomp :
      star x ⬝ᵥ (denseMatrix P *ᵥ x)
        = star x ⬝ᵥ (denseDataTerm P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    rw [denseMatrix_decompose]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hPre2Decomp :
      star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        = star x ⬝ᵥ (precond2Extra P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    rw [precond2Matrix_decompose]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hRegPSD : (precond1Matrix P).PosSemidef := by
    simpa [precond1Matrix] using regularizerPreconditioner_posSemidef (P := P) hLam hKpsd
  have hRegNonneg : 0 ≤ star x ⬝ᵥ (precond1Matrix P *ᵥ x) :=
    hRegPSD.dotProduct_mulVec_nonneg x
  have hRegScale :
      star x ⬝ᵥ (precond1Matrix P *ᵥ x)
        ≤ c * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
    nlinarith
  have hData := hDataUpper x
  rw [hDenseDecomp, hPre2Decomp]
  nlinarith

/-- If the data term has a lower quadratic bound `β * precond2Extra`,
then the dense operator has lower quadratic bound `β * precond2Matrix`.
This is a direct `β M₂ ⪯q A` certificate. -/
theorem dense_quadratic_ge_precond2_of_data_lower
    (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef)
    {beta : Real} (hBetaLeOne : beta ≤ 1)
    (hDataLower : ∀ x : Fin r × Fin n → Real,
      beta * (star x ⬝ᵥ (precond2Extra P *ᵥ x))
        ≤ star x ⬝ᵥ (denseDataTerm P *ᵥ x))
    (x : Fin r × Fin n → Real) :
    star x ⬝ᵥ ((beta • precond2Matrix P) *ᵥ x) ≤ star x ⬝ᵥ (denseMatrix P *ᵥ x) := by
  have hDenseDecomp :
      star x ⬝ᵥ (denseMatrix P *ᵥ x)
        = star x ⬝ᵥ (denseDataTerm P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    rw [denseMatrix_decompose]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hPre2Decomp :
      star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        = star x ⬝ᵥ (precond2Extra P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    rw [precond2Matrix_decompose]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hRegPSD : (precond1Matrix P).PosSemidef := by
    simpa [precond1Matrix] using regularizerPreconditioner_posSemidef (P := P) hLam hKpsd
  have hRegNonneg : 0 ≤ star x ⬝ᵥ (precond1Matrix P *ᵥ x) :=
    hRegPSD.dotProduct_mulVec_nonneg x
  have hRegScale :
      beta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x))
        ≤ star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    nlinarith
  have hData := hDataLower x
  have hLeftExpand :
      star x ⬝ᵥ ((beta • precond2Matrix P) *ᵥ x)
        = beta * (star x ⬝ᵥ (precond2Extra P *ᵥ x))
            + beta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
    calc
      star x ⬝ᵥ ((beta • precond2Matrix P) *ᵥ x)
          = beta * (star x ⬝ᵥ (precond2Matrix P *ᵥ x)) := by
              simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ = beta * (star x ⬝ᵥ (precond2Extra P *ᵥ x) + star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
            rw [hPre2Decomp]
      _ = beta * (star x ⬝ᵥ (precond2Extra P *ᵥ x))
            + beta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by ring
  have hRightExpand :
      star x ⬝ᵥ (denseMatrix P *ᵥ x)
        = star x ⬝ᵥ (denseDataTerm P *ᵥ x)
            + star x ⬝ᵥ (precond1Matrix P *ᵥ x) := hDenseDecomp
  rw [hLeftExpand, hRightExpand]
  nlinarith

/-- Two-sided `A` vs `M₂` Loewner-style package from data-term bounds:
`β M₂ ⪯q A ⪯q c M₂`. -/
theorem dense_precond2_two_sided_loewner_from_data_bounds
    (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef)
    {beta c : Real}
    (hBetaLeOne : beta ≤ 1)
    (hCone : 1 ≤ c)
    (hDataLower : ∀ x : Fin r × Fin n → Real,
      beta * (star x ⬝ᵥ (precond2Extra P *ᵥ x))
        ≤ star x ⬝ᵥ (denseDataTerm P *ᵥ x))
    (hDataUpper : ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P *ᵥ x) ≤ c * (star x ⬝ᵥ (precond2Extra P *ᵥ x))) :
    QuadraticLe (beta • precond2Matrix P) (denseMatrix P) ∧
      QuadraticLe (denseMatrix P) (c • precond2Matrix P) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact dense_quadratic_ge_precond2_of_data_lower
      (P := P) (hLam := hLam) (hKpsd := hKpsd)
      (hBetaLeOne := hBetaLeOne)
      (hDataLower := hDataLower) x
  · intro x
    have h := dense_quadratic_le_precond2_of_data_upper
      (P := P) (hLam := hLam) (hKpsd := hKpsd)
      (hCone := hCone) (hDataUpper := hDataUpper) x
    simpa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using h

/-- Practical `A` vs `M₂` Loewner-style package:
`M₁ ⪯q A` always, and `A ⪯q c M₂` under a direct data-term upper bound. -/
theorem dense_precond2_loewner_certificate
    (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef)
    {c : Real} (hCone : 1 ≤ c)
    (hDataUpper : ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P *ᵥ x) ≤ c * (star x ⬝ᵥ (precond2Extra P *ᵥ x))) :
    QuadraticLe (precond1Matrix P) (denseMatrix P) ∧
    QuadraticLe (denseMatrix P) (c • precond2Matrix P) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact dense_quadratic_dominates_precond1 (P := P) x
  · intro x
    have h := dense_quadratic_le_precond2_of_data_upper
      (P := P) (hLam := hLam) (hKpsd := hKpsd)
      (hCone := hCone) (hDataUpper := hDataUpper) x
    simpa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using h

theorem quadraticLe_trans
    {m : Type*} [Fintype m]
    {A B C : Matrix m m Real}
    (hAB : QuadraticLe A B)
    (hBC : QuadraticLe B C) :
    QuadraticLe A C := by
  intro x
  exact le_trans (hAB x) (hBC x)

/-- Turn an upper comparison `M₂ ⪯q δ M₁` (`δ>0`) into the lower comparison
`(1/δ) M₂ ⪯q M₁`. -/
theorem precond2_lower_scaled_of_upper_compare
    (P : Problem n M r q)
    {delta : Real}
    (hDeltaPos : 0 < delta)
    (hM2toM1Upper : QuadraticLe (precond2Matrix P) (delta • precond1Matrix P)) :
    QuadraticLe (((1 / delta) : Real) • precond2Matrix P) (precond1Matrix P) := by
  intro x
  have hUpper :
      star x ⬝ᵥ (precond2Matrix P *ᵥ x)
        ≤ delta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)) := by
    simpa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using hM2toM1Upper x
  have hScaled :
      (1 / delta) * (star x ⬝ᵥ (precond2Matrix P *ᵥ x))
        ≤ (1 / delta) * (delta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x))) := by
    exact mul_le_mul_of_nonneg_left hUpper (by positivity)
  have hCancel :
      (1 / delta) * (delta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x)))
        = star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    field_simp [hDeltaPos.ne']
  calc
    star x ⬝ᵥ ((((1 / delta : Real) • precond2Matrix P) *ᵥ x))
        = (1 / delta) * (star x ⬝ᵥ (precond2Matrix P *ᵥ x)) := by
            simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    _ ≤ (1 / delta) * (delta * (star x ⬝ᵥ (precond1Matrix P *ᵥ x))) := hScaled
    _ = star x ⬝ᵥ (precond1Matrix P *ᵥ x) := hCancel

/-- Transfer a lower quadratic envelope from `M₁` to `M₂` via
`β M₂ ⪯q M₁ ⪯q A`. -/
theorem dense_quadratic_lower_precond2_of_precond1_lower_and_compare
    (P : Problem n M r q)
    {beta : Real}
    (hLower1 : QuadraticLe (precond1Matrix P) (denseMatrix P))
    (hM2toM1Lower : QuadraticLe (beta • precond2Matrix P) (precond1Matrix P)) :
    QuadraticLe (beta • precond2Matrix P) (denseMatrix P) := by
  exact quadraticLe_trans hM2toM1Lower hLower1

/-- Transfer an upper quadratic envelope from `M₂` to `M₁` via
`A ⪯q c M₂ ⪯q (cδ) M₁`. -/
theorem dense_quadratic_upper_precond1_of_precond2_upper_and_compare
    (P : Problem n M r q)
    {c delta : Real}
    (hCnonneg : 0 ≤ c)
    (hUpper2 : QuadraticLe (denseMatrix P) (c • precond2Matrix P))
    (hM2toM1Upper : QuadraticLe (precond2Matrix P) (delta • precond1Matrix P)) :
    QuadraticLe (denseMatrix P) ((c * delta) • precond1Matrix P) := by
  intro x
  have h1 := hUpper2 x
  have h2 := hM2toM1Upper x
  have h2scaled :
      c * (star x ⬝ᵥ (precond2Matrix P *ᵥ x))
        ≤ c * (star x ⬝ᵥ ((delta • precond1Matrix P) *ᵥ x)) := by
    exact mul_le_mul_of_nonneg_left h2 hCnonneg
  have hA :
      star x ⬝ᵥ (denseMatrix P *ᵥ x)
        ≤ c * (star x ⬝ᵥ ((delta • precond1Matrix P) *ᵥ x)) := by
    calc
      star x ⬝ᵥ (denseMatrix P *ᵥ x)
          ≤ star x ⬝ᵥ ((c • precond2Matrix P) *ᵥ x) := h1
      _ = c * (star x ⬝ᵥ (precond2Matrix P *ᵥ x)) := by
            simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ ≤ c * (star x ⬝ᵥ ((delta • precond1Matrix P) *ᵥ x)) := h2scaled
  calc
    star x ⬝ᵥ (denseMatrix P *ᵥ x)
        ≤ c * (star x ⬝ᵥ ((delta • precond1Matrix P) *ᵥ x)) := hA
    _ = star x ⬝ᵥ (((c * delta) • precond1Matrix P) *ᵥ x) := by
          simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Intrinsic automatic two-sided certificate on `A/M₁/M₂`:
with `δ = 1 + (trace(gramMatrix)+1)/λ`, one gets
`(1/δ) M₂ ⪯q A ⪯q ((trace(K)+1)δ) M₁` from q10-native assumptions only. -/
theorem dense_precond2_precond1_two_sided_auto_certificate
    (P : Problem n M r q)
    (hΩinj : Function.Injective P.Ω)
    (hLam : 0 ≤ P.lam) (hLamPos : 0 < P.lam)
    (hKpsd : P.K.PosSemidef) :
    let delta : Real := 1 + ((gramMatrix P).trace + 1) / P.lam
    QuadraticLe (((1 / delta : Real) • precond2Matrix P)) (denseMatrix P) ∧
      QuadraticLe (denseMatrix P) (((P.K.trace + 1) * delta) • precond1Matrix P) := by
  let delta : Real := 1 + ((gramMatrix P).trace + 1) / P.lam
  have hGramTraceNonneg : 0 ≤ (gramMatrix P).trace :=
    Matrix.PosSemidef.trace_nonneg (gramMatrix_posSemidef (P := P))
  have hNumPos : 0 < (gramMatrix P).trace + 1 := by nlinarith
  have hDeltaPos : 0 < delta := by
    have hFracPos : 0 < ((gramMatrix P).trace + 1) / P.lam :=
      div_pos hNumPos hLamPos
    nlinarith [delta, hFracPos]
  have hM2toM1Upper :
      QuadraticLe (precond2Matrix P) (delta • precond1Matrix P) := by
    simpa [delta] using precond2_quadratic_le_scaled_precond1_auto
      (P := P) (hLam := hLamPos) (hKpsd := hKpsd)
  have hM2toM1Lower :
      QuadraticLe (((1 / delta : Real) • precond2Matrix P)) (precond1Matrix P) :=
    precond2_lower_scaled_of_upper_compare
      (P := P) (hDeltaPos := hDeltaPos) (hM2toM1Upper := hM2toM1Upper)
  have hLower1 : QuadraticLe (precond1Matrix P) (denseMatrix P) := by
    intro x
    exact dense_quadratic_dominates_precond1 (P := P) x
  have hLower2 :
      QuadraticLe (((1 / delta : Real) • precond2Matrix P)) (denseMatrix P) :=
    dense_quadratic_lower_precond2_of_precond1_lower_and_compare
      (P := P) (hLower1 := hLower1) (hM2toM1Lower := hM2toM1Lower)
  have hDataUpper :
      ∀ x : Fin r × Fin n → Real,
        star x ⬝ᵥ (denseDataTerm P *ᵥ x)
          ≤ (P.K.trace + 1) * (star x ⬝ᵥ (precond2Extra P *ᵥ x)) := by
    intro x
    exact dense_data_upper_from_injective_and_kernel_psd
      (P := P) (hΩinj := hΩinj) (hKpsd := hKpsd) x
  have hTraceNonneg : 0 ≤ P.K.trace := Matrix.PosSemidef.trace_nonneg hKpsd
  have hCone : 1 ≤ (P.K.trace + 1 : Real) := by nlinarith
  have hUpper2 :
      QuadraticLe (denseMatrix P) (((P.K.trace + 1) : Real) • precond2Matrix P) := by
    exact (dense_precond2_loewner_certificate
      (P := P) (hLam := hLam) (hKpsd := hKpsd)
      (c := P.K.trace + 1) (hCone := hCone) (hDataUpper := hDataUpper)).2
  have hUpper1 :
      QuadraticLe (denseMatrix P) (((P.K.trace + 1) * delta) • precond1Matrix P) :=
    dense_quadratic_upper_precond1_of_precond2_upper_and_compare
      (P := P) (hCnonneg := by nlinarith [hTraceNonneg])
      (hUpper2 := hUpper2) (hM2toM1Upper := hM2toM1Upper)
  exact ⟨hLower2, hUpper1⟩

/-- Concrete `β M₂ ⪯q A ⪯q C₁ M₁` scales from the automatic upper envelope:
`β = 1 / (1 + (trace(gramMatrix)+1)/λ)`,
`C₁ = (trace(K)+1) * (1 + (trace(gramMatrix)+1)/λ)`. -/
theorem dense_precond2_precond1_two_sided_auto_scales
    (P : Problem n M r q)
    (hΩinj : Function.Injective P.Ω)
    (hLam : 0 ≤ P.lam) (hLamPos : 0 < P.lam)
    (hKpsd : P.K.PosSemidef) :
    QuadraticLe
      (((1 / (1 + ((gramMatrix P).trace + 1) / P.lam) : Real) • precond2Matrix P))
      (denseMatrix P) ∧
      QuadraticLe (denseMatrix P)
        ((((P.K.trace + 1) * (1 + ((gramMatrix P).trace + 1) / P.lam)) : Real)
          • precond1Matrix P) := by
  simpa using dense_precond2_precond1_two_sided_auto_certificate
    (P := P) (hΩinj := hΩinj) (hLam := hLam) (hLamPos := hLamPos) (hKpsd := hKpsd)


end
end Q10
end AutoProof
