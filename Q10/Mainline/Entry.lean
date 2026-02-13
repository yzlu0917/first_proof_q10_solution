import autoproof.Q10.KernelOps.SystemEquiv
import autoproof.Q10.Preconditioners.ClosedForm
import autoproof.Q10.Loewner.MainChain
import autoproof.Q10.TraceAndRates.RateTheory.PreconditionedKrylovInterval

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- q10 mainline theorem for `q10.tex` integration.
It closes the chain from system equivalence, to computable preconditioner bridges,
strict Loewner/kappa/rate/modelTol comparison, residual certificates for
both preconditioners, and trace-model complexity certificates, including
model-tolerance indexed cost witnesses. -/
theorem q10_tex_mainline_theorem
    (P : TexProblem n M r q)
    (beta err0 eps : Real)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef)
    (hBetaPos : 0 < beta)
    (hBetaLeOne : beta ≤ 1)
    (hBetaLtTrace : beta < P.K.trace + 1)
    (hBetaGtAutoInverse :
      (1 / (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) < beta)
    (hDataLower :
      ∀ x : Fin r × Fin n → Real,
        beta * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x))
          ≤ star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x))
    (hErr0 : 0 < err0)
    (hEps : 0 < eps) :
    (∀ W B : Matrix (Fin n) (Fin r) Real,
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsVec P.K B
        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * B) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P.toProblem R).vec
        = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Matrix P.toProblem *ᵥ (precond2Apply P.toProblem R).vec = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Apply P.toProblem R
        = P.K⁻¹ * R * (gramMatrix P.toProblem + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹) ∧
    ((QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧
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
      k2 ≤ k1)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real,
      ∀ mu1 L1 err0z1 : Real,
        mu1 ≤ L1 →
        ((LinearMap.toMatrixAlgEquiv'
              (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))ᵀ
            = LinearMap.toMatrixAlgEquiv'
                (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem))) →
        (spectrum ℝ
            (LinearMap.toMatrixAlgEquiv'
              (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))
              ⊆ Set.Icc mu1 L1) →
        ‖WithLp.toLp 2 (precond1Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z1 →
        ∀ k : Nat,
          pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k
            ≤ precond1UndoBoundConst P.toProblem
                * (polyAbsBoundOnIcc mu1 L1
                    (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)
                  * err0z1)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real,
      ∀ mu2 L2 err0z2 : Real,
        mu2 ≤ L2 →
        ((LinearMap.toMatrixAlgEquiv'
              (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))ᵀ
            = LinearMap.toMatrixAlgEquiv'
                (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem))) →
        (spectrum ℝ
            (LinearMap.toMatrixAlgEquiv'
              (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))
              ⊆ Set.Icc mu2 L2) →
        ‖WithLp.toLp 2 (precond2Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z2 →
        ∀ k : Nat,
          pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k
            ≤ precond2UndoBoundConst P.toProblem
                * (polyAbsBoundOnIcc mu2 L2
                    (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)
                  * err0z2)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ iters : Nat,
      pcgTraceCostPrecond1 n r q
          (pcgRunTrace P.toProblem (precond1Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond1 iters n r q ∧
      pcgTraceCostPrecond2 n r q
          (pcgRunTrace P.toProblem (precond2Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond2 iters n r q) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k
        ≤ precond1UndoBoundConst P.toProblem
            * ‖(polyApplyLin (precondApplyALin P.toProblem (precond1ApplyLin P.toProblem))
                (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)
                (precond1Apply P.toProblem (pcgR0 P.toProblem x0))).vec‖) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k
        ≤ precond2UndoBoundConst P.toProblem
            * ‖(polyApplyLin (precondApplyALin P.toProblem (precond2ApplyLin P.toProblem))
                (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)
                (precond2Apply P.toProblem (pcgR0 P.toProblem x0))).vec‖) ∧
    (∃ k1 k2 : Nat,
      2 * (pcgRate (spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ^ k1
            * err0 ≤ eps ∧
      2 * (pcgRate (spectralKappa beta (P.K.trace + 1))) ^ k2 * err0 ≤ eps ∧
      (∀ x0 : Matrix (Fin n) (Fin r) Real,
        pcgTraceCostPrecond1 n r q
            (pcgRunTrace P.toProblem (precond1Apply P.toProblem) x0 k1).2
          = pcgSolveCostPrecond1 k1 n r q) ∧
      (∀ x0 : Matrix (Fin n) (Fin r) Real,
        pcgTraceCostPrecond2 n r q
            (pcgRunTrace P.toProblem (precond2Apply P.toProblem) x0 k2).2
          = pcgSolveCostPrecond2 k2 n r q) ∧
      k2 ≤ k1) := by
  have hTerminal :
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
    exact q10_mainline_terminal_compare_auto_strict_from_data_lower
      (P := P) (beta := beta) (err0 := err0) (eps := eps)
      (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
      (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
      (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
      (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B
    exact q10_mainline_system_equiv_matrixFree
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (hK := P.hK) (W := W) (B := B)
  · intro R
    exact (q10_mainline_preconditioner_action_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).1 R
  · intro R
    exact (q10_mainline_preconditioner_action_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).2 R
  · intro R
    exact (q10_mainline_precond2_closed_form_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos) (R := R)).2.2
  · exact hTerminal
  · intro x0 mu1 L1 err0z1 hMuLeL hSymm hEigRange hErr0z1 k
    exact pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope_of_denseSpectrum
      (P := P.toProblem)
      (Minv := precond1Apply P.toProblem)
      (MinvLin := precond1ApplyLin P.toProblem)
      (MinvInv := precond1Undo P.toProblem)
      (x0 := x0)
      (mu := mu1) (L := L1) (err0z := err0z1)
      (cInv := precond1UndoBoundConst P.toProblem)
      (hMuLeL := hMuLeL)
      (hMinv := by
        intro X
        simpa using (precond1ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond1Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hcInv := precond1UndoBoundConst_nonneg (P := P.toProblem))
      (hInvBound := precond1Undo_norm_le_boundConst (P := P.toProblem))
      (hSymm := hSymm) (hEigRange := hEigRange) (hErr0z := hErr0z1) k
  · intro x0 mu2 L2 err0z2 hMuLeL hSymm hEigRange hErr0z2 k
    exact pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope_of_denseSpectrum
      (P := P.toProblem)
      (Minv := precond2Apply P.toProblem)
      (MinvLin := precond2ApplyLin P.toProblem)
      (MinvInv := precond2Undo P.toProblem)
      (x0 := x0)
      (mu := mu2) (L := L2) (err0z := err0z2)
      (cInv := precond2UndoBoundConst P.toProblem)
      (hMuLeL := hMuLeL)
      (hMinv := by
        intro X
        simpa using (precond2ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond2Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hcInv := precond2UndoBoundConst_nonneg (P := P.toProblem))
      (hInvBound := precond2Undo_norm_le_boundConst (P := P.toProblem))
      (hSymm := hSymm) (hEigRange := hEigRange) (hErr0z := hErr0z2) k
  · intro x0 iters
    refine ⟨?_, ?_⟩
    · exact pcgRunTrace_costPrecond1_eq_model
        (P := P.toProblem) (x0 := x0) (iters := iters)
    · exact pcgRunTrace_costPrecond2_eq_model
        (P := P.toProblem) (x0 := x0) (iters := iters)
  · intro x0 k
    have hCore := pcgRun_precond_residual_norm_le_leftInverse_polyRec
      (P := P.toProblem)
      (Minv := precond1Apply P.toProblem)
      (MinvLin := precond1ApplyLin P.toProblem)
      (MinvInv := precond1Undo P.toProblem)
      (x0 := x0)
      (hMinv := by
        intro X
        simpa using (precond1ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond1Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hInvBound := precond1Undo_norm_le_boundConst (P := P.toProblem))
    simpa [pcgResidualNorm] using hCore k
  · intro x0 k
    have hCore := pcgRun_precond_residual_norm_le_leftInverse_polyRec
      (P := P.toProblem)
      (Minv := precond2Apply P.toProblem)
      (MinvLin := precond2ApplyLin P.toProblem)
      (MinvInv := precond2Undo P.toProblem)
      (x0 := x0)
      (hMinv := by
        intro X
        simpa using (precond2ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond2Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hInvBound := precond2Undo_norm_le_boundConst (P := P.toProblem))
    simpa [pcgResidualNorm] using hCore k
  · rcases hTerminal.2 with ⟨k1, k2, hk1, hk2, hkOrder⟩
    refine ⟨k1, k2, hk1, hk2, ?_, ?_, hkOrder⟩
    · intro x0
      exact pcgRunTrace_costPrecond1_eq_model
        (P := P.toProblem) (x0 := x0) (iters := k1)
    · intro x0
      exact pcgRunTrace_costPrecond2_eq_model
        (P := P.toProblem) (x0 := x0) (iters := k2)

end
end Q10
end AutoProof
