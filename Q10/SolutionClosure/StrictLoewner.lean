import autoproof.Q10.SolutionClosure.CoreBridges

set_option autoImplicit false

open scoped BigOperators Kronecker MatrixOrder
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Terminal intrinsic strict comparison closure:
from q10-native data-lower + scale condition `β > 1/δ_auto`, produce
`β M₂ ⪯q A ⪯q C₁_auto M₁`, strict `κ₂ < κ₁`, strict `ρ₂ < ρ₁`,
and model-rate tolerance witnesses without external algorithm-side assumptions. -/
theorem q10_solutiontxt_terminal_compare_auto_strict_from_data_lower
    (P : TexProblem n M r q)
    (beta err0 eps : Real)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hBetaPos : 0 < beta)
    (hBetaLeOne : beta ≤ 1)
    (hBetaLtTrace : beta < P.K.trace + 1)
    (hBetaGtAutoInverse :
      (1 / (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) < beta)
    (hDataLower :
      ∀ x : Fin r × Fin n → Real,
        beta * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x))
          ≤ star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x))
    (hErr0 : 0 < err0) (hEps : 0 < eps) :
    (QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem)
        (((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam))
          • precond1Matrix P.toProblem) ∧
      spectralKappa beta (P.K.trace + 1)
        < spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) ∧
      pcgRate (spectralKappa beta (P.K.trace + 1))
        < pcgRate (spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ∧
    (∃ k1 k2 : Nat,
      2 * (pcgRate (spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ^ k1
            * err0 ≤ eps ∧
      2 * (pcgRate (spectralKappa beta (P.K.trace + 1))) ^ k2 * err0 ≤ eps ∧
      k2 ≤ k1) := by
  let delta : Real := 1 + ((gramMatrix P.toProblem).trace + 1) / P.lam
  have hChain :
      QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem)
        (((P.K.trace + 1) * delta) • precond1Matrix P.toProblem) ∧
      spectralKappa beta (P.K.trace + 1)
        < spectralKappa (1 : Real) ((P.K.trace + 1) * delta) := by
    simpa [delta] using q10_solutiontxt_loewner_kappa_chain_auto_strict_from_data_lower
      (P := P) (beta := beta) (hLamNonneg := hLamNonneg) (hLamPos := hLamPos)
      (hKpsd := hKpsd) (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
      (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
      (hDataLower := hDataLower)
  have hTraceNonneg : 0 ≤ P.K.trace := Matrix.PosSemidef.trace_nonneg hKpsd
  have hNumPos : 0 < (gramMatrix P.toProblem).trace + 1 := by
    have hGramTraceNonneg : 0 ≤ (gramMatrix P.toProblem).trace :=
      Matrix.PosSemidef.trace_nonneg (gramMatrix_posSemidef (P := P.toProblem))
    nlinarith
  have hDeltaPos : 0 < delta := by
    have hFracPos : 0 < ((gramMatrix P.toProblem).trace + 1) / P.lam :=
      div_pos hNumPos hLamPos
    nlinarith [delta, hFracPos]
  have hDeltaGtOne : (1 : Real) < delta := by
    have hFracPos : 0 < ((gramMatrix P.toProblem).trace + 1) / P.lam :=
      div_pos hNumPos hLamPos
    nlinarith [delta, hFracPos]
  have hOneLtCd : (1 : Real) < (P.K.trace + 1) * delta := by
    nlinarith [hTraceNonneg, hDeltaGtOne]
  have hBetaDelta : 1 < beta * delta := by
    have hMul : (1 / delta) * delta < beta * delta :=
      mul_lt_mul_of_pos_right (by simpa [delta] using hBetaGtAutoInverse) hDeltaPos
    have hOne : (1 / delta) * delta = (1 : Real) := by
      field_simp [hDeltaPos.ne']
    nlinarith [hMul, hOne]
  have hRateStrict :
      pcgRate (spectralKappa beta (P.K.trace + 1))
        < pcgRate (spectralKappa (1 : Real) ((P.K.trace + 1) * delta)) :=
    pcgRate_strict_from_loewner_scales
      (hCpos := by nlinarith [hTraceNonneg])
      (hBetaPos := hBetaPos)
      (hBetaLtC := hBetaLtTrace)
      (hBetaDelta := hBetaDelta)
      (hOneLtCd := hOneLtCd)
  have hKappa1 :
      1 < spectralKappa (1 : Real) ((P.K.trace + 1) * delta) :=
    spectralKappa_gt_one_of_interval (show 0 < (1 : Real) by norm_num) hOneLtCd
  have hKappa2 :
      1 < spectralKappa beta (P.K.trace + 1) :=
    spectralKappa_gt_one_of_interval hBetaPos hBetaLtTrace
  let k1 : Nat := modelTolIter
    (spectralKappa (1 : Real) ((P.K.trace + 1) * delta)) err0 eps hKappa1 hErr0 hEps
  let k2 : Nat := modelTolIter
    (spectralKappa beta (P.K.trace + 1)) err0 eps hKappa2 hErr0 hEps
  have hk1 :
      2 * (pcgRate (spectralKappa (1 : Real) ((P.K.trace + 1) * delta))) ^ k1 * err0 ≤ eps := by
    simpa [k1] using modelTolIter_spec (hKappa := hKappa1) (hErr0 := hErr0) (hEps := hEps)
  have hk2 :
      2 * (pcgRate (spectralKappa beta (P.K.trace + 1))) ^ k2 * err0 ≤ eps := by
    simpa [k2] using modelTolIter_spec (hKappa := hKappa2) (hErr0 := hErr0) (hEps := hEps)
  have hkOrder : k2 ≤ k1 := by
    have hKappaOrder :
        spectralKappa beta (P.K.trace + 1)
          ≤ spectralKappa (1 : Real) ((P.K.trace + 1) * delta) :=
      le_of_lt hChain.2.2
    exact modelTolIter_le_of_kappa_le
      (hKappa1 := hKappa1) (hKappa2 := hKappa2)
      (hErr0 := hErr0) (hEps := hEps) hKappaOrder
  refine ⟨?_, ?_⟩
  · refine ⟨hChain.1, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [delta] using hChain.2.1
    · simpa [delta] using hChain.2.2
    · simpa [delta] using hRateStrict
  · refine ⟨k1, k2, ?_, hk2, hkOrder⟩
    simpa [delta] using hk1

end
end Q10
end AutoProof
