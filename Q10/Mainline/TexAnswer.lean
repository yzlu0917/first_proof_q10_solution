import autoproof.Q10.Mainline.Entry
import autoproof.Q10.Core.CostAndPSD

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- q10.tex problem-style integrated solver certificate (minimal assumptions):
PCG under SPD (`lam > 0`, `K` positive definite), matrix-free/RHS-on-observed
implementation without explicit `N`, explicit operation-cost formulas, and
PSD fallback branch via residual/normal-equation certificates. -/
theorem q10_tex_problem_style_solver_certificate
    (P : TexProblem n M r q)
    (vals : Fin q → Real)
    {d : Nat}
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef)
    (residualSolver : PSDResidualSpec P.toProblem)
    (normalEqSolver : PSDNormalEqSpec P.toProblem) :
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
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (precond2ApplyPlan P.toProblem R).1 = precond2Apply P.toProblem R ∧
      precond2ApplyTraceCost n r (precond2ApplyPlan P.toProblem R).2 = precond2ApplyCost n r) ∧
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
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ iters : Nat,
      pcgTraceCostPrecond1 n r q
          (pcgRunTrace P.toProblem (precond1Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond1 iters n r q ∧
      pcgTraceCostPrecond2 n r q
          (pcgRunTrace P.toProblem (precond2Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond2 iters n r q) ∧
    (rhsFromObservedRows P.K P.Ω vals (obsRowFromFactors F)
      = rhsFromObserved P.K P.Ω vals P.Z) ∧
    (sparseMatVecTraceCost n r
      (rhsFromObservedRowsPlan P.K P.Ω vals (obsRowFromFactors F)).2
        = rhsFromObservedCost n r q) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeObservedPlan P.K P.Ω (obsRowFromFactors F) P.lam W).2
          = applyMatrixFreeSparseCost n r q) ∧
    (matVecCost n r q = n * n * r + q * r) ∧
    (precond1SetupCost n = n * n * n) ∧
    (precond2SetupCost n r = n * n * n + r * r * r) ∧
    (precond1ApplyCost n r = n * n * r) ∧
    (precond2ApplyCost n r = n * n * r + n * r * r) ∧
    (rhsFromObservedCost n r q = n * n * r + q * r) ∧
    (applyMatrixFreeSparseCost n r q = 2 * (n * n * r) + q * r + q * r) ∧
    (applyMatrixFreeObservedOnlineCost n r q d
      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost d q r) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond1 iters n r q
        = n * n * n + n * n * r + iters * ((n * n * r + q * r) + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2 iters n r q
        = (n * n * n + r * r * r) + n * n * r
            + iters * ((n * n * r + q * r) + (n * n * r + n * r * r))) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      (residualSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (residualSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      (normalEqSolver.normalResidual x0 k = 0 →
        applyASparse P.toProblem
          (rhsMat P.toProblem - applyASparse P.toProblem (normalEqSolver.run x0 k)) = 0) ∧
      (normalEqSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (normalEqSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
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
  · intro R
    have hPlan := q10_mainline_precond2_closed_form_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos) (R := R)
    exact ⟨hPlan.1, hPlan.2.1⟩
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
  · intro x0 iters
    refine ⟨?_, ?_⟩
    · exact pcgRunTrace_costPrecond1_eq_model
        (P := P.toProblem) (x0 := x0) (iters := iters)
    · exact pcgRunTrace_costPrecond2_eq_model
        (P := P.toProblem) (x0 := x0) (iters := iters)
  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved
      (K := P.K) (Ω := P.Ω) (vals := vals) (Z := P.Z) (F := F) (hRows := hRows)
  · exact rhsFromObservedRowsPlan_cost_eq
      (K := P.K) (Ω := P.Ω) (vals := vals) (zObs := obsRowFromFactors F)
  · intro W
    exact applyMatrixFreeObserved_from_factors_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows) (lam := P.lam) (W := W)
  · intro W
    exact applyMatrixFreeObservedPlan_cost_eq
      (K := P.K) (Ω := P.Ω) (zObs := obsRowFromFactors F) (lam := P.lam) (W := W)
  · simp [matVecCost]
  · simp [precond1SetupCost]
  · simp [precond2SetupCost]
  · simp [precond1ApplyCost]
  · simp [precond2ApplyCost]
  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]
  · simp [applyMatrixFreeSparseCost, kernelMulCost, gatherKernelPredictSparseCost,
      scatterMulSparseCost]
  · rfl
  · intro iters
    simp [pcgSolveCostPrecond1, precond1SetupCost, kernelMulCost,
      matVecCost, precond1ApplyCost]
  · intro iters
    simp [pcgSolveCostPrecond2, precond2SetupCost, kernelMulCost,
      matVecCost, precond2ApplyCost]
  · intro x0 k
    exact q10_psd_solver_branch_residual_normalEq
      (P := P) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (residualSolver := residualSolver) (normalEqSolver := normalEqSolver) (x0 := x0) (k := k)

/-- Concrete-instantiated proof term of `q10_tex_problem_style_solver_certificate`:
the PSD fallback branch uses internal matrix-free concrete iterators
`residualCorrectionSpec` / `normalEqCorrectionSpec` (no external spec parameter). -/
abbrev q10_tex_problem_style_solver_certificate_concrete
    (P : TexProblem n M r q)
    (vals : Fin q → Real)
    {d : Nat}
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef) :=
    q10_tex_problem_style_solver_certificate
      (P := P) (vals := vals) (F := F) (hRows := hRows)
      (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (hLamPos := hLamPos) (hKpos := hKpos)
      (residualSolver := residualCorrectionSpec P.toProblem)
      (normalEqSolver := normalEqCorrectionSpec P.toProblem)

/-- Final q10.tex-style integrated certificate:
combines the main PCG chain, matrix-free/RHS construction without explicit `N`,
online observed-row generation from factors, and a PSD fallback branch
via residual/normal-equation model certificates. -/
theorem q10_tex_full_solution_certificate
    (P : TexProblem n M r q)
    (vals : Fin q → Real)
    {d : Nat}
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
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
    (hEps : 0 < eps)
    (residualSolver : PSDResidualSpec P.toProblem)
    (normalEqSolver : PSDNormalEqSpec P.toProblem) :
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
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (precond2ApplyPlan P.toProblem R).1 = precond2Apply P.toProblem R ∧
      precond2ApplyTraceCost n r (precond2ApplyPlan P.toProblem R).2 = precond2ApplyCost n r) ∧
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
      k2 ≤ k1) ∧
    (rhsFromObservedRows P.K P.Ω vals (obsRowFromFactors F)
      = rhsFromObserved P.K P.Ω vals P.Z) ∧
    (sparseMatVecTraceCost n r
      (rhsFromObservedRowsPlan P.K P.Ω vals (obsRowFromFactors F)).2
        = rhsFromObservedCost n r q) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeObservedPlan P.K P.Ω (obsRowFromFactors F) P.lam W).2
          = applyMatrixFreeSparseCost n r q) ∧
    (matVecCost n r q = n * n * r + q * r) ∧
    (precond1SetupCost n = n * n * n) ∧
    (precond2SetupCost n r = n * n * n + r * r * r) ∧
    (precond1ApplyCost n r = n * n * r) ∧
    (precond2ApplyCost n r = n * n * r + n * r * r) ∧
    (rhsFromObservedCost n r q = n * n * r + q * r) ∧
    (applyMatrixFreeSparseCost n r q = 2 * (n * n * r) + q * r + q * r) ∧
    (applyMatrixFreeObservedOnlineCost n r q d
      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost d q r) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond1 iters n r q
        = n * n * n + n * n * r + iters * ((n * n * r + q * r) + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2 iters n r q
        = (n * n * n + r * r * r) + n * n * r
            + iters * ((n * n * r + q * r) + (n * n * r + n * r * r))) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      (residualSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (residualSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      (normalEqSolver.normalResidual x0 k = 0 →
        applyASparse P.toProblem
          (rhsMat P.toProblem - applyASparse P.toProblem (normalEqSolver.run x0 k)) = 0) ∧
      (normalEqSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (normalEqSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) := by
  have hMain := q10_tex_mainline_theorem
      (P := P) (beta := beta) (err0 := err0) (eps := eps)
      (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (hLamPos := hLamPos) (hKpos := hKpos)
      (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
      (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
      (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)
  rcases hMain with ⟨hSys, hMain⟩
  rcases hMain with ⟨hPre1, hMain⟩
  rcases hMain with ⟨hPre2, hMain⟩
  rcases hMain with ⟨hClosed, hMain⟩
  rcases hMain with ⟨_hLoewnerRate, hMain⟩
  rcases hMain with ⟨_hResidualDense1, hMain⟩
  rcases hMain with ⟨_hResidualDense2, hMain⟩
  rcases hMain with ⟨_hCostAnyIters, hMain⟩
  rcases hMain with ⟨hResidualBridge1, hMain⟩
  rcases hMain with ⟨hResidualBridge2, hTolCost⟩
  refine ⟨hSys, hPre1, hPre2, hClosed, ?_, hResidualBridge1, hResidualBridge2,
    hTolCost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R
    have hPlan := q10_mainline_precond2_closed_form_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos) (R := R)
    exact ⟨hPlan.1, hPlan.2.1⟩
  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved
      (K := P.K) (Ω := P.Ω) (vals := vals) (Z := P.Z) (F := F) (hRows := hRows)
  · exact rhsFromObservedRowsPlan_cost_eq
      (K := P.K) (Ω := P.Ω) (vals := vals) (zObs := obsRowFromFactors F)
  · intro W
    exact applyMatrixFreeObserved_from_factors_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows) (lam := P.lam) (W := W)
  · intro W
    exact applyMatrixFreeObservedPlan_cost_eq
      (K := P.K) (Ω := P.Ω) (zObs := obsRowFromFactors F) (lam := P.lam) (W := W)
  · simp [matVecCost]
  · simp [precond1SetupCost]
  · simp [precond2SetupCost]
  · simp [precond1ApplyCost]
  · simp [precond2ApplyCost]
  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]
  · simp [applyMatrixFreeSparseCost, kernelMulCost, gatherKernelPredictSparseCost,
      scatterMulSparseCost]
  · rfl
  · intro iters
    simp [pcgSolveCostPrecond1, precond1SetupCost, kernelMulCost,
      matVecCost, precond1ApplyCost]
  · intro iters
    simp [pcgSolveCostPrecond2, precond2SetupCost, kernelMulCost,
      matVecCost, precond2ApplyCost]
  · intro x0 k
    exact q10_psd_solver_branch_residual_normalEq
      (P := P) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (residualSolver := residualSolver) (normalEqSolver := normalEqSolver) (x0 := x0) (k := k)

/-- "Perfect-fit" q10.tex certificate:
locks observed-data RHS semantics (`B = sparseMTTKRP Ω vals Z`), uses concrete PSD
fallback iterators, exposes bucketed/CSR matvec implementation and its cost identity,
adds factor-Gram setup-cost model for preconditioner #2, and provides the
human-readable sqrt-form tolerance-iteration witness. -/
theorem q10_tex_perfect_solution_certificate
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l)
    {dGram : Nat}
    (modeSizes : Fin dGram → Nat)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef) :
    (∀ W B : Matrix (Fin n) (Fin r) Real,
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsVec P.K B
        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * B) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P.toProblem R).vec = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Matrix P.toProblem *ᵥ (precond2Apply P.toProblem R).vec = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Apply P.toProblem R
        = P.K⁻¹ * R * (gramMatrix P.toProblem + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹) ∧
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
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ iters : Nat,
      pcgTraceCostPrecond1 n r q
          (pcgRunTrace P.toProblem (precond1Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond1 iters n r q ∧
      pcgTraceCostPrecond2 n r q
          (pcgRunTrace P.toProblem (precond2Apply P.toProblem) x0 iters).2
        = pcgSolveCostPrecond2 iters n r q) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z) ∧
    (rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z) ∧
    (n < q ∧ r < q ∧ q < N) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeBucketed P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeBucketedPlan P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W).2
          = applyMatrixFreeSparseCost n r q) ∧
    (gramMatrix P.toProblem = gramFromFactors (r := r) A) ∧
    (precond2SetupCostFromFactorGrams modeSizes n r
      = n * n * n + r * r * r + (∑ i : Fin dGram, modeSizes i * r * r) + dGram * r * r) ∧
    (∃ k : Nat, 2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ k) * err0 ≤ eps) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      ((residualCorrectionSpec P.toProblem).residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam ((residualCorrectionSpec P.toProblem).run x0 k).vec = rhsVec P.K P.B) ∧
      ((normalEqCorrectionSpec P.toProblem).normalResidual x0 k = 0 →
        applyASparse P.toProblem
          (rhsMat P.toProblem - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k)) = 0) ∧
      ((normalEqCorrectionSpec P.toProblem).residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam ((normalEqCorrectionSpec P.toProblem).run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) := by
  have hCore := q10_tex_problem_style_solver_certificate_concrete
    (P := P.toTexProblem) (vals := P.vals) (F := F) (hRows := hRows)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
    (hLamPos := hLamPos) (hKpos := hKpos)
  rcases hCore with ⟨hSys, hCore⟩
  rcases hCore with ⟨hPre1, hCore⟩
  rcases hCore with ⟨hPre2, hCore⟩
  rcases hCore with ⟨hClosed, hCore⟩
  rcases hCore with ⟨_hPlan2, hCore⟩
  rcases hCore with ⟨hRes1, hCore⟩
  rcases hCore with ⟨hRes2, hCore⟩
  rcases hCore with ⟨hCost, hCore⟩
  rcases hCore with ⟨_hRhsRowsEq, hCore⟩
  rcases hCore with ⟨_hRhsRowsCost, hCore⟩
  rcases hCore with ⟨_hObsEq, hCore⟩
  rcases hCore with ⟨_hObsCost, hCore⟩
  rcases hCore with ⟨_hMatVecCost, hCore⟩
  rcases hCore with ⟨_hPre1Setup, hCore⟩
  rcases hCore with ⟨_hPre2Setup, hCore⟩
  rcases hCore with ⟨_hPre1ApplyCost, hCore⟩
  rcases hCore with ⟨_hPre2ApplyCost, hCore⟩
  rcases hCore with ⟨_hRhsCost, hCore⟩
  rcases hCore with ⟨_hSparseCost, hCore⟩
  rcases hCore with ⟨_hOnlineCost, hCore⟩
  rcases hCore with ⟨_hPcgCost1, hCore⟩
  rcases hCore with ⟨_hPcgCost2, hPsdConcrete⟩
  refine ⟨hSys, hPre1, hPre2, hClosed, hRes1, hRes2, hCost, ?_, P.rhsVec_eq_rhsFromObserved,
    hScale, ?_, ?_, ?_, ?_, ?_, hPsdConcrete⟩
  · intro W
    calc
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
          ↔ applyDenseVec P.K P.Z P.Ω P.lam W.vec
              = rhsVec P.K (sparseMTTKRP P.Ω P.vals P.Z) := by
                simp [rhsVec, rhsFromObserved]
      _ ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z :=
            hSys W (sparseMTTKRP P.Ω P.vals P.Z)
  · intro W
    exact applyMatrixFreeCanonicalBucketed_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · intro W
    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · exact gramMatrix_eq_gramFromFactors_of_khatriRao
      (P := P.toProblem) (e := e) (A := A) (hZ := hZ)
  · exact precond2SetupCostFromFactorGrams_eq
      (modeSizes := modeSizes) (n := n) (r := r)
  · exact exists_iter_model_rate_le_tol_sqrt_form
      (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)

/-- q10.tex complete certificate under PSD assumptions:
global assumptions match the problem statement (`K` PSD), with a solver split:
`K` positive-definite branch recovers the full PCG-perfect theorem; otherwise
the PSD branch is certified by concrete residual/normal-equation contracts and no-`N` costs. -/
theorem q10_tex_complete_solution_certificate
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l)
    {dGram : Nat}
    (modeSizes : Fin dGram → Nat)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z) ∧
    (rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z) ∧
    (n < q ∧ r < q ∧ q < N) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeBucketed P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeBucketedPlan P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W).2
          = applyMatrixFreeSparseCost n r q) ∧
    (gramMatrix P.toProblem = gramFromFactors (r := r) A) ∧
    (precond2SetupCostFromFactorGrams modeSizes n r
      = n * n * n + r * r * r + (∑ i : Fin dGram, modeSizes i * r * r) + dGram * r * r) ∧
    (∃ k : Nat, 2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ k) * err0 ≤ eps) ∧
    (∀ k : Nat,
      (⌈Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)⌉₊ : Nat) ≤ k →
      2 * (pcgRate kappa) ^ k * err0 ≤ eps) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond1 iters n r q
        = n * n * n + n * n * r + iters * ((n * n * r + q * r) + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2 iters n r q
        = (n * n * n + r * r * r) + n * n * r
            + iters * ((n * n * r + q * r) + (n * n * r + n * r * r))) ∧
    (denseDirectSolveCost n r = n * n * n * r * r * r) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      (‖((residualCorrectionSpec P.toProblem).residual x0 k).vec‖ ≤ eps →
        ‖(rhsMat P.toProblem
            - applyASparse P.toProblem ((residualCorrectionSpec P.toProblem).run x0 k)).vec‖ ≤ eps) ∧
      (‖((normalEqCorrectionSpec P.toProblem).normalResidual x0 k).vec‖ ≤ eps →
        ‖(applyASparse P.toProblem
            (rhsMat P.toProblem - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k))).vec‖ ≤ eps) ∧
      (‖((normalEqCorrectionSpec P.toProblem).residual x0 k).vec‖ ≤ eps →
        ‖(rhsMat P.toProblem
            - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k)).vec‖ ≤ eps)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      ((residualCorrectionSpec P.toProblem).residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam ((residualCorrectionSpec P.toProblem).run x0 k).vec = rhsVec P.K P.B) ∧
      ((normalEqCorrectionSpec P.toProblem).normalResidual x0 k = 0 →
        applyASparse P.toProblem
          (rhsMat P.toProblem - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k)) = 0) ∧
      ((normalEqCorrectionSpec P.toProblem).residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam ((normalEqCorrectionSpec P.toProblem).run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) ∧
    (P.K.PosDef →
      (∀ R : Matrix (Fin n) (Fin r) Real,
        (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P.toProblem R).vec = R.vec) ∧
      (∀ R : Matrix (Fin n) (Fin r) Real,
        precond2Matrix P.toProblem *ᵥ (precond2Apply P.toProblem R).vec = R.vec) ∧
      (∀ R : Matrix (Fin n) (Fin r) Real,
        precond2Apply P.toProblem R
          = P.K⁻¹ * R * (gramMatrix P.toProblem + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹) ∧
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
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ iters : Nat,
        pcgTraceCostPrecond1 n r q
            (pcgRunTrace P.toProblem (precond1Apply P.toProblem) x0 iters).2
          = pcgSolveCostPrecond1 iters n r q ∧
        pcgTraceCostPrecond2 n r q
            (pcgRunTrace P.toProblem (precond2Apply P.toProblem) x0 iters).2
          = pcgSolveCostPrecond2 iters n r q)) := by
  refine ⟨?_, P.rhsVec_eq_rhsFromObserved, hScale, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W
    calc
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
          ↔ applyDenseVec P.K P.Z P.Ω P.lam W.vec
              = rhsVec P.K (sparseMTTKRP P.Ω P.vals P.Z) := by
                simp [rhsVec, rhsFromObserved]
      _ ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z :=
            q10_mainline_system_equiv_matrixFree
              (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (hK := P.hK)
              (W := W) (B := sparseMTTKRP P.Ω P.vals P.Z)
  · intro W
    exact applyMatrixFreeCanonicalBucketed_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · intro W
    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · exact gramMatrix_eq_gramFromFactors_of_khatriRao
      (P := P.toProblem) (e := e) (A := A) (hZ := hZ)
  · exact precond2SetupCostFromFactorGrams_eq
      (modeSizes := modeSizes) (n := n) (r := r)
  · exact exists_iter_model_rate_le_tol_sqrt_form
      (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
  · intro k hk
    exact model_rate_le_tol_of_ge_ceil_log_ratio
      (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
      (k := k) hk
  · intro iters
    simp [pcgSolveCostPrecond1, precond1SetupCost, kernelMulCost,
      matVecCost, precond1ApplyCost]
  · intro iters
    simp [pcgSolveCostPrecond2, precond2SetupCost, kernelMulCost,
      matVecCost, precond2ApplyCost]
  · exact denseDirectSolveCost_eq n r
  · intro x0 k
    exact q10_psd_solver_branch_residual_normalEq_concrete_tol
      (P := P.toTexProblem) (x0 := x0) (k := k) (epsTol := eps)
  · intro x0 k
    exact q10_psd_solver_branch_residual_normalEq_concrete
      (P := P.toTexProblem) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (x0 := x0) (k := k)
  · intro hKpos
    have hPerf := q10_tex_perfect_solution_certificate
      (P := P) (F := F) (hRows := hRows)
      (N := N) (hScale := hScale)
      (e := e) (A := A) (hZ := hZ)
      (modeSizes := modeSizes)
      (kappa := kappa) (err0 := err0) (eps := eps)
      (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
      (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
      (hKpos := hKpos)
    rcases hPerf with ⟨_hSys, hPerf⟩
    rcases hPerf with ⟨hPre1, hPerf⟩
    rcases hPerf with ⟨hPre2, hPerf⟩
    rcases hPerf with ⟨hClosed, hPerf⟩
    rcases hPerf with ⟨hRes1, hPerf⟩
    rcases hPerf with ⟨hRes2, hPerf⟩
    rcases hPerf with ⟨hCost, _hRest⟩
    exact ⟨hPre1, hPre2, hClosed, hRes1, hRes2, hCost⟩

/-- PSD-to-PCG closure via nugget shift:
for any `nu > 0`, `K + nu I` is SPD and the shifted problem inherits explicit
PCG residual/cost certificates and explicit iteration-count bounds. -/
theorem q10_tex_psd_to_shifted_pcg_certificate
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l)
    {dGram : Nat}
    (modeSizes : Fin dGram → Nat)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (nu : Real) (hNu : 0 < nu) :
    let Pnu := P.withKernelShift nu
    Pnu.K.PosDef ∧
    (∃ k : Nat, 2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ k) * err0 ≤ eps) ∧
    (∀ k : Nat,
      (⌈Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)⌉₊ : Nat) ≤ k →
      2 * (pcgRate kappa) ^ k * err0 ≤ eps) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond1 iters n r q
        = n * n * n + n * n * r + iters * ((n * n * r + q * r) + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2 iters n r q
        = (n * n * n + r * r * r) + n * n * r
            + iters * ((n * n * r + q * r) + (n * n * r + n * r * r))) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (Pnu.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ Pnu.K)) *ᵥ (precond1Apply Pnu.toProblem R).vec
        = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Matrix Pnu.toProblem *ᵥ (precond2Apply Pnu.toProblem R).vec = R.vec) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      pcgResidualNorm Pnu.toProblem (precond1Apply Pnu.toProblem) x0 k
        ≤ precond1UndoBoundConst Pnu.toProblem
            * ‖(polyApplyLin (precondApplyALin Pnu.toProblem (precond1ApplyLin Pnu.toProblem))
                (pcgPrecondResidualPolyRec Pnu.toProblem (precond1Apply Pnu.toProblem) x0 k)
                (precond1Apply Pnu.toProblem (pcgR0 Pnu.toProblem x0))).vec‖) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ k : Nat,
      pcgResidualNorm Pnu.toProblem (precond2Apply Pnu.toProblem) x0 k
        ≤ precond2UndoBoundConst Pnu.toProblem
            * ‖(polyApplyLin (precondApplyALin Pnu.toProblem (precond2ApplyLin Pnu.toProblem))
                (pcgPrecondResidualPolyRec Pnu.toProblem (precond2Apply Pnu.toProblem) x0 k)
                (precond2Apply Pnu.toProblem (pcgR0 Pnu.toProblem x0))).vec‖) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ iters : Nat,
      pcgTraceCostPrecond1 n r q
          (pcgRunTrace Pnu.toProblem (precond1Apply Pnu.toProblem) x0 iters).2
        = pcgSolveCostPrecond1 iters n r q ∧
      pcgTraceCostPrecond2 n r q
          (pcgRunTrace Pnu.toProblem (precond2Apply Pnu.toProblem) x0 iters).2
        = pcgSolveCostPrecond2 iters n r q) := by
  dsimp
  have hPos : (P.withKernelShift nu).K.PosDef :=
    TexObservedProblem.withKernelShift_posDef_of_posSemidef
      (P := P) hKpsd (hNu := hNu)
  have hCert := q10_tex_complete_solution_certificate
    (P := P.withKernelShift nu)
    (F := F)
    (hRows := by simpa using hRows)
    (N := N) (hScale := hScale)
    (e := e) (A := A)
    (hZ := by simpa using hZ)
    (modeSizes := modeSizes)
    (kappa := kappa) (err0 := err0) (eps := eps)
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := by simpa using hLamNonneg)
    (hKpsd := hPos.posSemidef)
    (hLamPos := by simpa using hLamPos)
  rcases hCert with ⟨_hSys, hCert⟩
  rcases hCert with ⟨_hRhsEq, hCert⟩
  rcases hCert with ⟨_hScaleOut, hCert⟩
  rcases hCert with ⟨_hBucketEq, hCert⟩
  rcases hCert with ⟨_hBucketCost, hCert⟩
  rcases hCert with ⟨_hGramEq, hCert⟩
  rcases hCert with ⟨_hSetupEq, hCert⟩
  rcases hCert with ⟨hIterExists, hCert⟩
  rcases hCert with ⟨hIterCeil, hCert⟩
  rcases hCert with ⟨hCost1, hCert⟩
  rcases hCert with ⟨hCost2, hCert⟩
  rcases hCert with ⟨_hDirectCost, hCert⟩
  rcases hCert with ⟨_hTolContract, hCert⟩
  rcases hCert with ⟨_hPsdBranch, hPCGImp⟩
  have hPCG := hPCGImp hPos
  rcases hPCG with ⟨hPre1, hPCG⟩
  rcases hPCG with ⟨hPre2, hPCG⟩
  rcases hPCG with ⟨_hClosed, hPCG⟩
  rcases hPCG with ⟨hRes1, hPCG⟩
  rcases hPCG with ⟨hRes2, hTrace⟩
  exact ⟨hPos, hIterExists, hIterCeil, hCost1, hCost2, hPre1, hPre2, hRes1, hRes2, hTrace⟩

/-- Closed-loop strengthened final certificate:
extends `q10_tex_complete_solution_certificate` with
1) fully-online observed-row PCG cost formulas,
2) a direct `kappa`-binding interface from interval spectral parameters, and
3) explicit PSD-to-shifted-PCG `eps`-attainability witnesses for every `nu > 0`. -/
theorem q10_tex_complete_solution_certificate_closed_loop_online
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l)
    {dGram : Nat}
    (modeSizes : Fin dGram → Nat)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (mu L : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hKappaLe : spectralKappa mu L ≤ kappa) :
    (∀ iters : Nat,
      pcgSolveCostPrecond1Online iters n r q dObs
        = n * n * n + n * n * r
            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2Online iters n r q dObs
        = (n * n * n + r * r * r) + n * n * r
            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + (n * n * r + n * r * r))) ∧
    modelTolIter (spectralKappa mu L) err0 eps
        (spectralKappa_gt_one_of_interval hMuPos hMuLtL) hErr0 hEps
      ≤ modelTolIter kappa err0 eps hKappa hErr0 hEps ∧
    (∀ nu : Real, 0 < nu →
      let Pnu := P.withKernelShift nu
      Pnu.K.PosDef ∧
      (∃ k : Nat, 2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ k) * err0 ≤ eps)) ∧
    (P.K.PosDef →
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 (k + 1)
            ≤ pcgRate kappa * pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k) →
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 0 ≤ 2 * err0z →
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0
          (modelTolIter kappa err0z eps hKappa hErr0z hEps) ≤ eps) ∧
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 (k + 1)
            ≤ pcgRate kappa * pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k) →
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 0 ≤ 2 * err0z →
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0
          (modelTolIter kappa err0z eps hKappa hErr0z hEps) ≤ eps)) ∧
    (P.K.PosDef →
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 (k + 1)
            ≤ pcgRate (spectralKappa mu L)
                * pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k) →
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 0 ≤ 2 * err0z →
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0
          (modelTolIter (spectralKappa mu L) err0z eps
            (spectralKappa_gt_one_of_interval hMuPos hMuLtL) hErr0z hEps) ≤ eps) ∧
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 (k + 1)
            ≤ pcgRate (spectralKappa mu L)
                * pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k) →
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 0 ≤ 2 * err0z →
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0
          (modelTolIter (spectralKappa mu L) err0z eps
            (spectralKappa_gt_one_of_interval hMuPos hMuLtL) hErr0z hEps) ≤ eps)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real,
      (‖((residualCorrectionSpec P.toProblem).residual x0 0).vec‖ ≤ 2 * err0 →
        (∀ k : Nat,
          ‖((residualCorrectionSpec P.toProblem).residual x0 (k + 1)).vec‖
            ≤ pcgRate kappa * ‖((residualCorrectionSpec P.toProblem).residual x0 k).vec‖) →
        ‖((normalEqCorrectionSpec P.toProblem).residual x0 0).vec‖ ≤ 2 * err0 →
        (∀ k : Nat,
          ‖((normalEqCorrectionSpec P.toProblem).residual x0 (k + 1)).vec‖
            ≤ pcgRate kappa * ‖((normalEqCorrectionSpec P.toProblem).residual x0 k).vec‖) →
        (∃ kRes : Nat,
          ‖((residualCorrectionSpec P.toProblem).residual x0 kRes).vec‖ ≤ eps) ∧
        (∃ kNormal : Nat,
          ‖((normalEqCorrectionSpec P.toProblem).residual x0 kNormal).vec‖ ≤ eps))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro iters
    simpa using pcgSolveCostPrecond1Online_eq iters n r q dObs
  · intro iters
    simpa using pcgSolveCostPrecond2Online_eq iters n r q dObs
  · exact modelTolIter_le_of_kappa_le
      (hKappa1 := hKappa)
      (hKappa2 := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
      (hErr0 := hErr0) (hEps := hEps) (hKappaOrder := hKappaLe)
  · intro nu hNu
    have hShift := q10_tex_psd_to_shifted_pcg_certificate
      (P := P) (F := F) (hRows := hRows)
      (N := N) (hScale := hScale)
      (e := e) (A := A) (hZ := hZ)
      (modeSizes := modeSizes)
      (kappa := kappa) (err0 := err0) (eps := eps)
      (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
      (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
      (nu := nu) (hNu := hNu)
    rcases hShift with ⟨hPos, hIterExists, _hRest⟩
    exact ⟨hPos, hIterExists⟩
  · intro _hKpos
    refine ⟨?_, ?_⟩
    · intro x0 err0z hErr0z hRec hInit
      exact pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise
        (P := P.toProblem)
        (Minv := precond1Apply P.toProblem)
        (x0 := x0)
        (kappa := kappa) (err0 := err0z) (eps := eps)
        (hKappa := hKappa) (hErr0 := hErr0z) (hEps := hEps)
        (hInit := hInit) (hRecurrence := hRec)
    · intro x0 err0z hErr0z hRec hInit
      exact pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise
        (P := P.toProblem)
        (Minv := precond2Apply P.toProblem)
        (x0 := x0)
        (kappa := kappa) (err0 := err0z) (eps := eps)
        (hKappa := hKappa) (hErr0 := hErr0z) (hEps := hEps)
        (hInit := hInit) (hRecurrence := hRec)
  · intro _hKpos
    refine ⟨?_, ?_⟩
    · intro x0 err0z hErr0z hRec hInit
      exact pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise
        (P := P.toProblem)
        (Minv := precond1Apply P.toProblem)
        (x0 := x0)
        (kappa := spectralKappa mu L) (err0 := err0z) (eps := eps)
        (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
        (hErr0 := hErr0z) (hEps := hEps)
        (hInit := hInit) (hRecurrence := hRec)
    · intro x0 err0z hErr0z hRec hInit
      exact pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise
        (P := P.toProblem)
        (Minv := precond2Apply P.toProblem)
        (x0 := x0)
        (kappa := spectralKappa mu L) (err0 := err0z) (eps := eps)
        (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
        (hErr0 := hErr0z) (hEps := hEps)
        (hInit := hInit) (hRecurrence := hRec)
  · intro x0 hInitRes hStepRes hInitNormal hStepNormal
    exact q10_psd_solver_branch_concrete_attains_tol_of_stepwise
      (P := P.toTexProblem)
      (x0 := x0)
      (rho := pcgRate kappa) (err0 := err0) (eps := eps)
      (hRhoNonneg := pcgRate_nonneg hKappa)
      (hRhoLtOne := pcgRate_lt_one hKappa)
      (hErr0 := hErr0) (hEps := hEps)
      (hInitRes := hInitRes) (hStepRes := hStepRes)
      (hInitNormal := hInitNormal) (hStepNormal := hStepNormal)

/-- Non-stepwise PCG tolerance closure for this problem:
if the canonical preconditioned residual-polynomial actions satisfy the
standard `2*(pcgRate kappa)^k*err0z` envelope, then model-index termination
follows without an explicit stepwise recurrence hypothesis. -/
theorem q10_tex_complete_solution_certificate_polyEnvelope_closure
    (P : TexObservedProblem n M r q)
    (kappa eps : Real)
    (hKappa : 1 < kappa)
    (hEps : 0 < eps)
    (hLamPos : 0 < P.lam) :
    (P.K.PosDef →
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          ‖(polyApplyLin (precondApplyALin P.toProblem (precond1ApplyLin P.toProblem))
              (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)
              (precond1Apply P.toProblem (pcgR0 P.toProblem x0))).vec‖
            ≤ 2 * (pcgRate kappa) ^ k * err0z) →
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0
          (modelTolIter kappa err0z eps hKappa hErr0z hEps)
            ≤ precond1UndoBoundConst P.toProblem * eps) ∧
      (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real, ∀ hErr0z : 0 < err0z,
        (∀ k : Nat,
          ‖(polyApplyLin (precondApplyALin P.toProblem (precond2ApplyLin P.toProblem))
              (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)
              (precond2Apply P.toProblem (pcgR0 P.toProblem x0))).vec‖
            ≤ 2 * (pcgRate kappa) ^ k * err0z) →
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0
          (modelTolIter kappa err0z eps hKappa hErr0z hEps)
            ≤ precond2UndoBoundConst P.toProblem * eps)) := by
  intro hKpos
  refine ⟨?_, ?_⟩
  · intro x0 err0z hErr0z hPolyBound
    exact pcgResidualNorm_le_cmul_tol_at_modelTolIter_of_precond_polyRec_envelope
      (P := P.toProblem)
      (Minv := precond1Apply P.toProblem)
      (MinvLin := precond1ApplyLin P.toProblem)
      (MinvInv := precond1Undo P.toProblem)
      (x0 := x0)
      (kappa := kappa) (err0z := err0z) (eps := eps)
      (c := precond1UndoBoundConst P.toProblem)
      (hMinv := by
        intro X
        simpa using (precond1ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond1Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hc := precond1UndoBoundConst_nonneg (P := P.toProblem))
      (hKappa := hKappa) (hErr0z := hErr0z) (hEps := hEps)
      (hInvBound := precond1Undo_norm_le_boundConst (P := P.toProblem))
      (hPolyBound := hPolyBound)
  · intro x0 err0z hErr0z hPolyBound
    exact pcgResidualNorm_le_cmul_tol_at_modelTolIter_of_precond_polyRec_envelope
      (P := P.toProblem)
      (Minv := precond2Apply P.toProblem)
      (MinvLin := precond2ApplyLin P.toProblem)
      (MinvInv := precond2Undo P.toProblem)
      (x0 := x0)
      (kappa := kappa) (err0z := err0z) (eps := eps)
      (c := precond2UndoBoundConst P.toProblem)
      (hMinv := by
        intro X
        simpa using (precond2ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond2Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hc := precond2UndoBoundConst_nonneg (P := P.toProblem))
      (hKappa := hKappa) (hErr0z := hErr0z) (hEps := hEps)
      (hInvBound := precond2Undo_norm_le_boundConst (P := P.toProblem))
      (hPolyBound := hPolyBound)

/-- Spectral-interval binding certificate for this concrete system:
the interval parameters `mu, L` are attached directly to the preconditioned
operators of this problem instance (both preconditioners), eliminating a free
standalone `kappa` at this interface. -/
theorem q10_tex_pcg_spectral_interval_binding_certificate
    (P : TexObservedProblem n M r q)
    (mu L : Real)
    (hMuLeL : mu ≤ L)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef)
    (hSymm1 :
      (LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))ᵀ
        = LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))
    (hEigRange1 :
      spectrum ℝ
          (LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))
        ⊆ Set.Icc mu L)
    (hSymm2 :
      (LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))ᵀ
        = LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))
    (hEigRange2 :
      spectrum ℝ
          (LinearMap.toMatrixAlgEquiv'
            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))
        ⊆ Set.Icc mu L) :
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,
      ‖WithLp.toLp 2 (precond1Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →
      ∀ k : Nat,
        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k
          ≤ precond1UndoBoundConst P.toProblem
              * (polyAbsBoundOnIcc mu L
                  (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)
                * err0z)) ∧
    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,
      ‖WithLp.toLp 2 (precond2Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →
      ∀ k : Nat,
        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k
          ≤ precond2UndoBoundConst P.toProblem
              * (polyAbsBoundOnIcc mu L
                  (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)
                * err0z)) := by
  refine ⟨?_, ?_⟩
  · intro x0 err0z hErr0z k
    exact pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope_of_denseSpectrum
      (P := P.toProblem)
      (Minv := precond1Apply P.toProblem)
      (MinvLin := precond1ApplyLin P.toProblem)
      (MinvInv := precond1Undo P.toProblem)
      (x0 := x0)
      (mu := mu) (L := L) (err0z := err0z)
      (cInv := precond1UndoBoundConst P.toProblem)
      (hMuLeL := hMuLeL)
      (hMinv := by
        intro X
        simpa using (precond1ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond1Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hcInv := precond1UndoBoundConst_nonneg (P := P.toProblem))
      (hInvBound := precond1Undo_norm_le_boundConst (P := P.toProblem))
      (hSymm := hSymm1) (hEigRange := hEigRange1) (hErr0z := hErr0z) k
  · intro x0 err0z hErr0z k
    exact pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope_of_denseSpectrum
      (P := P.toProblem)
      (Minv := precond2Apply P.toProblem)
      (MinvLin := precond2ApplyLin P.toProblem)
      (MinvInv := precond2Undo P.toProblem)
      (x0 := x0)
      (mu := mu) (L := L) (err0z := err0z)
      (cInv := precond2UndoBoundConst P.toProblem)
      (hMuLeL := hMuLeL)
      (hMinv := by
        intro X
        simpa using (precond2ApplyLin_apply (P := P.toProblem) (R := X)).symm)
      (hLeftInv := precond2Undo_leftInverse_of_posDef
        (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos))
      (hcInv := precond2UndoBoundConst_nonneg (P := P.toProblem))
      (hInvBound := precond2Undo_norm_le_boundConst (P := P.toProblem))
      (hSymm := hSymm2) (hEigRange := hEigRange2) (hErr0z := hErr0z) k

/-- Optional strong branch for preconditioner-2 quality:
under `hDataLower`-style structural assumptions, expose strict Loewner/kappa/rate
comparison and resulting iteration witnesses directly at the observed-problem level. -/
theorem q10_tex_precond2_choice_strong_branch_observed
    (P : TexObservedProblem n M r q)
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
  have hMain := q10_tex_mainline_theorem
    (P := P.toTexProblem)
    (beta := beta) (err0 := err0) (eps := eps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
    (hLamPos := hLamPos) (hKpos := hKpos)
    (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
    (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
    (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)
  rcases hMain with ⟨_hSys, hMain⟩
  rcases hMain with ⟨_hPre1, hMain⟩
  rcases hMain with ⟨_hPre2, hMain⟩
  rcases hMain with ⟨_hClosed, hMain⟩
  exact hMain.1

/-- Canonical one-factor index equivalence used to eliminate external `e/A/hZ`
inputs from the default theorem interface. -/
def canonicalSingleFactorEquiv (M : Nat) :
    Fin M ≃ ((u : Unit) → Fin M) where
  toFun := fun j _ => j
  invFun := fun f => f ()
  left_inv := by
    intro j
    rfl
  right_inv := by
    intro f
    funext u
    cases u
    rfl

/-- Canonical one-factor family: the unique factor matrix is exactly `Z`. -/
def canonicalSingleFactors
    {M r : Nat}
    (Z : Matrix (Fin M) (Fin r) Real) :
    (u : Unit) → Matrix (Fin M) (Fin r) Real :=
  fun _ => Z

/-- Minimal-input wrapper of `q10_tex_complete_solution_certificate`:
`e/A/hZ/modeSizes` are internally instantiated by canonical witnesses. -/
abbrev q10_tex_complete_solution_certificate_minimal_input
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (ι := Unit)
    (κ := fun _ : Unit => Fin M)
    (e := canonicalSingleFactorEquiv M)
    (A := canonicalSingleFactors (M := M) (r := r) P.Z)
    (hZ := by
      intro j l
      simp [canonicalSingleFactors, canonicalSingleFactorEquiv])
    (dGram := 0)
    (modeSizes := Fin.elim0)
    (kappa := kappa) (err0 := err0) (eps := eps)
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Minimal-input wrapper of `q10_tex_complete_solution_certificate_closed_loop_online`:
`e/A/hZ/modeSizes` are internally instantiated by canonical witnesses. -/
abbrev q10_tex_complete_solution_certificate_closed_loop_online_minimal_input
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (mu L : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hKappaLe : spectralKappa mu L ≤ kappa) :=
  q10_tex_complete_solution_certificate_closed_loop_online
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (ι := Unit)
    (κ := fun _ : Unit => Fin M)
    (e := canonicalSingleFactorEquiv M)
    (A := canonicalSingleFactors (M := M) (r := r) P.Z)
    (hZ := by
      intro j l
      simp [canonicalSingleFactors, canonicalSingleFactorEquiv])
    (dGram := 0)
    (modeSizes := Fin.elim0)
    (kappa := kappa) (err0 := err0) (eps := eps)
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (mu := mu) (L := L) (hMuPos := hMuPos) (hMuLtL := hMuLtL) (hKappaLe := hKappaLe)

/-- Minimal-input wrapper of `q10_tex_psd_to_shifted_pcg_certificate`:
`e/A/hZ/modeSizes` are internally instantiated by canonical witnesses. -/
abbrev q10_tex_psd_to_shifted_pcg_certificate_minimal_input
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (nu : Real)
    (hNu : 0 < nu) :=
  q10_tex_psd_to_shifted_pcg_certificate
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (ι := Unit)
    (κ := fun _ : Unit => Fin M)
    (e := canonicalSingleFactorEquiv M)
    (A := canonicalSingleFactors (M := M) (r := r) P.Z)
    (hZ := by
      intro j l
      simp [canonicalSingleFactors, canonicalSingleFactorEquiv])
    (dGram := 0)
    (modeSizes := Fin.elim0)
    (kappa := kappa) (err0 := err0) (eps := eps)
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (nu := nu) (hNu := hNu)

/-- Spectral-indexed minimal-input wrapper of
`q10_tex_complete_solution_certificate`: fixes `kappa = spectralKappa mu L`
instead of taking an unconstrained external `kappa` input. -/
abbrev q10_tex_complete_solution_certificate_minimal_input_spectralIndexed
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_minimal_input
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (kappa := spectralKappa mu L) (err0 := err0) (eps := eps)
    (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Spectral-indexed minimal-input wrapper of
`q10_tex_complete_solution_certificate_closed_loop_online`:
`kappa` is fixed to `spectralKappa mu L`. -/
abbrev q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_closed_loop_online_minimal_input
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (kappa := spectralKappa mu L) (err0 := err0) (eps := eps)
    (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (mu := mu) (L := L) (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hKappaLe := le_rfl)

/-- Spectral-indexed minimal-input wrapper of
`q10_tex_psd_to_shifted_pcg_certificate`: `kappa = spectralKappa mu L`. -/
abbrev q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (N : Nat)
    (hScale : n < q ∧ r < q ∧ q < N)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (nu : Real)
    (hNu : 0 < nu) :=
  q10_tex_psd_to_shifted_pcg_certificate_minimal_input
    (P := P) (F := F) (hRows := hRows)
    (N := N) (hScale := hScale)
    (kappa := spectralKappa mu L) (err0 := err0) (eps := eps)
    (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (nu := nu) (hNu := hNu)

/-- Spectral-indexed wrapper of non-stepwise poly-envelope tolerance closure:
`kappa` is fixed to `spectralKappa mu L`. -/
abbrev q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed
    (P : TexObservedProblem n M r q)
    (mu L eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hEps : 0 < eps)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_polyEnvelope_closure
    (P := P) (kappa := spectralKappa mu L) (eps := eps)
    (hKappa := spectralKappa_gt_one_of_interval hMuPos hMuLtL)
    (hEps := hEps) (hLamPos := hLamPos)

/-- Ambient-size-fixed wrapper:
binds the scale symbol to the concrete model size `N = n * M`. -/
abbrev q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (hScale : n < q ∧ r < q ∧ q < n * M)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_minimal_input_spectralIndexed
    (P := P) (F := F) (hRows := hRows)
    (N := n * M) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Ambient-size-fixed wrapper of online closed-loop spectral-indexed theorem:
binds `N = n * M` directly in the interface. -/
abbrev q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (hScale : n < q ∧ r < q ∧ q < n * M)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed
    (P := P) (F := F) (hRows := hRows)
    (N := n * M) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Ambient-size-fixed wrapper of shifted-PCG spectral-indexed theorem:
binds `N = n * M` directly in the interface. -/
abbrev q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)
    (hScale : n < q ∧ r < q ∧ q < n * M)
    (mu L err0 eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (nu : Real)
    (hNu : 0 < nu) :=
  q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed
    (P := P) (F := F) (hRows := hRows)
    (N := n * M) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (nu := nu) (hNu := hNu)

/-- Fully closed final q10.tex certificate:
combines the complete PSD-level theorem with online-PCG cost closure,
interval-to-`kappa` iteration binding, and PSD-to-shifted-PCG `eps` witnesses. -/
abbrev q10_tex_complete_solution_certificate_fully_closed :=
  And.intro
    (@q10_tex_complete_solution_certificate_minimal_input)
    (@q10_tex_complete_solution_certificate_closed_loop_online_minimal_input)

/-- Full d-way fully closed final q10.tex certificate (non-minimal API):
keeps explicit factor/gram witnesses in the theorem interface and packages
the complete PSD-level theorem, the online closed-loop theorem, and the
explicit shifted-PCG closure theorem. -/
abbrev q10_tex_complete_solution_certificate_fully_closed_full_dway :=
  And.intro
    (@q10_tex_complete_solution_certificate)
    (And.intro
      (@q10_tex_complete_solution_certificate_closed_loop_online)
      (@q10_tex_psd_to_shifted_pcg_certificate))

/-- Minimal-input spectral-indexed final package (default-facing):
`kappa` is not a free parameter; it is fixed as `spectralKappa mu L`.
This package also includes a non-stepwise poly-envelope tolerance closure
and the shifted-PCG PSD branch. -/
abbrev q10_tex_complete_solution_certificate_fully_closed_minimal_spectral :=
  And.intro
    (@q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN)
    (And.intro
      (@q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN)
      (And.intro
        (@q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN)
        (And.intro
          (@q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed)
          (And.intro
            (@q10_tex_pcg_spectral_interval_binding_certificate)
            (And.intro
              (@q10_tex_precond2_choice_strong_branch_observed)
              (@applyMatrixFreeSparseCost_eq_two_mul_matVecCost))))))

end
end Q10
end AutoProof
