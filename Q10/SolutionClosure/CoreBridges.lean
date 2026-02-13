import autoproof.Q10.TraceAndRates.LoewnerRates

set_option autoImplicit false

open scoped BigOperators Kronecker MatrixOrder
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Strict intrinsic chain with automatic upper scale and data-lower lower side:
from `β M₂ ⪯q A` (data-lower induced) and `β > 1/δ_auto`, derive
`A ⪯q C₁_auto M₁` and strict condition-number improvement `κ₂ < κ₁`. -/
theorem q10_solutiontxt_loewner_kappa_chain_auto_strict_from_data_lower
    (P : TexProblem n M r q)
    (beta : Real)
    (hLamNonneg : 0 ≤ P.lam)
    (hLamPos : 0 < P.lam)
    (hKpsd : P.K.PosSemidef)
    (hBetaPos : 0 < beta)
    (hBetaLeOne : beta ≤ 1)
    (hBetaLtTrace : beta < P.K.trace + 1)
    (hBetaGtAutoInverse :
      (1 / (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) < beta)
    (hDataLower :
      ∀ x : Fin r × Fin n → Real,
        beta * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x))
          ≤ star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x)) :
    let delta : Real := 1 + ((gramMatrix P.toProblem).trace + 1) / P.lam
    let C1 : Real := (P.K.trace + 1) * delta
    QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem) (C1 • precond1Matrix P.toProblem) ∧
      spectralKappa beta (P.K.trace + 1)
        < spectralKappa (1 : Real) ((P.K.trace + 1) * delta) := by
  let delta : Real := 1 + ((gramMatrix P.toProblem).trace + 1) / P.lam
  let C1 : Real := (P.K.trace + 1) * delta
  have hLower2 : QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) := by
    intro x
    exact dense_quadratic_ge_precond2_of_data_lower
      (P := P.toProblem) (hLam := hLamNonneg) (hKpsd := hKpsd)
      (hBetaLeOne := hBetaLeOne) (hDataLower := hDataLower) x
  have hUpper1 :
      QuadraticLe (denseMatrix P.toProblem) (C1 • precond1Matrix P.toProblem) := by
    simpa [delta, C1] using
      (dense_precond2_precond1_two_sided_auto_certificate
        (P := P.toProblem) (hΩinj := P.hOmegaInj)
        (hLam := hLamNonneg) (hLamPos := hLamPos) (hKpsd := hKpsd)).2
  have hTraceNonneg : 0 ≤ P.K.trace := Matrix.PosSemidef.trace_nonneg hKpsd
  have hTracePos : 0 < P.K.trace + 1 := by nlinarith
  have hGramTraceNonneg : 0 ≤ (gramMatrix P.toProblem).trace :=
    Matrix.PosSemidef.trace_nonneg (gramMatrix_posSemidef (P := P.toProblem))
  have hNumPos : 0 < (gramMatrix P.toProblem).trace + 1 := by nlinarith
  have hDeltaPos : 0 < delta := by
    have hFracPos : 0 < ((gramMatrix P.toProblem).trace + 1) / P.lam :=
      div_pos hNumPos hLamPos
    nlinarith [delta, hFracPos]
  have hBetaDelta : 1 < beta * delta := by
    have hMul : (1 / delta) * delta < beta * delta :=
      mul_lt_mul_of_pos_right hBetaGtAutoInverse hDeltaPos
    have hOne : (1 / delta) * delta = (1 : Real) := by
      field_simp [hDeltaPos.ne']
    nlinarith [hMul, hOne]
  have hKappaLt :
      spectralKappa beta (P.K.trace + 1)
        < spectralKappa (1 : Real) ((P.K.trace + 1) * delta) :=
    spectralKappa_lt_from_loewner_scales
      (hCpos := hTracePos) (hBetaPos := hBetaPos) (hBetaDelta := hBetaDelta)
  exact ⟨hLower2, hUpper1, hKappaLt⟩

end
end Q10
end AutoProof
