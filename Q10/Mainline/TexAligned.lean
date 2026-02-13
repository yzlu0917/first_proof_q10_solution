import autoproof.Q10.Mainline.TexAnswer

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- `q10.tex` Step 1 (system equation):
Dense Kronecker/selection system is equivalent to the matrix-free sparse action. -/
theorem q10_tex_step1_system_equivalence
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W B : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = rhsVec K B
      ↔ applyMatrixFreeSparse K Z Ω lam W = K * B := by
  exact q10_mainline_system_equiv_matrixFree
    (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK) (W := W) (B := B)

/-- `q10.tex` Step 2 (RHS from observed entries):
`B = TZ` is locked by observed sparse MTTKRP, so RHS is `rhsFromObserved`. -/
theorem q10_tex_step2_rhs_from_observations
    (P : TexObservedProblem n M r q) :
    rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z := by
  exact P.rhsVec_eq_rhsFromObserved

/-- `q10.tex` Step 3 (matrix-vector pipeline identities):
Step-B gather, Step-C scatter, and sparse matrix-free implementation are
exactly the dense pipeline rewritten over `q` observed entries. -/
theorem q10_tex_step3_matrix_vector_pipeline
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (W : Matrix (Fin n) (Fin r) Real) :
    gatherKernelPredictSparse K Z Ω W = gather Ω (K * W * Zᵀ) ∧
    scatterMulSparse Ω Z (gatherKernelPredictSparse K Z Ω W)
      = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z ∧
    applyMatrixFreeSparse K Z Ω lam W = applyMatrixFree K Z Ω lam W := by
  refine ⟨?_, ?_, ?_⟩
  · exact gatherKernelPredictSparse_eq_gather (K := K) (Z := Z) (Ω := Ω) (W := W)
  · calc
      scatterMulSparse Ω Z (gatherKernelPredictSparse K Z Ω W)
          = scatterMulSparse Ω Z (gather Ω (K * W * Zᵀ)) := by
              simp [gatherKernelPredictSparse_eq_gather]
      _ = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z :=
            scatterMulSparse_eq_scatter_mul
              (Ω := Ω) (Z := Z) (u := gather Ω (K * W * Zᵀ))
  · exact applyMatrixFreeSparse_eq_applyMatrixFree
      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)

/-- `q10.tex` Step 4 (CSR/bucket implementation and cost):
bucketed matrix-free matvec is algebraically identical to sparse matvec,
and its trace cost equals the sparse model cost. -/
theorem q10_tex_step4_bucketed_matvec_and_cost
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) :
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeBucketed K Z Ω (canonicalObsBuckets Ω) lam W
        = applyMatrixFreeSparse K Z Ω lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeBucketedPlan K Z Ω (canonicalObsBuckets Ω) lam W).2
          = applyMatrixFreeSparseCost n r q) := by
  refine ⟨?_, ?_⟩
  · intro W
    exact applyMatrixFreeCanonicalBucketed_eq_sparse
      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)
  · intro W
    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq
      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)

/-- `q10.tex` Step 5 (online observed-row generation):
if observed rows are generated on-the-fly from factors, both RHS and matvec
match the explicit-`Z` sparse formulas. -/
theorem q10_tex_step5_online_rows_equivalence
    (P : TexProblem n M r q)
    (vals : Fin q → Real)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F) :
    rhsFromObservedRows P.K P.Ω vals (obsRowFromFactors F)
      = rhsFromObserved P.K P.Ω vals P.Z ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) := by
  refine ⟨?_, ?_⟩
  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved
      (K := P.K) (Ω := P.Ω) (vals := vals) (Z := P.Z) (F := F) (hRows := hRows)
  · intro W
    exact applyMatrixFreeObserved_from_factors_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows)
      (lam := P.lam) (W := W)

/-- `q10.tex` Step 6 (preconditioner correctness and closed form):
under SPD assumptions required by PCG inverse actions, both preconditioners
are correct and preconditioner-2 has an explicit closed form. -/
theorem q10_tex_step6_preconditioners
    (P : TexProblem n M r q)
    (hLamPos : 0 < P.lam)
    (hKpos : P.K.PosDef) :
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P.toProblem R).vec
        = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Matrix P.toProblem *ᵥ (precond2Apply P.toProblem R).vec = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Apply P.toProblem R
        = P.K⁻¹ * R * (gramMatrix P.toProblem + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R
    exact (q10_mainline_preconditioner_action_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).1 R
  · intro R
    exact (q10_mainline_preconditioner_action_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).2 R
  · intro R
    exact (q10_mainline_precond2_closed_form_bridge
      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos) (R := R)).2.2

/-- `q10.tex` Step 7 (PCG residual certificate from spectral interval):
for this concrete problem and each preconditioner, dense-spectrum bounds
on the preconditioned operator imply residual-norm bounds. -/
theorem q10_tex_step7_pcg_residual_from_spectrum
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
  exact q10_tex_pcg_spectral_interval_binding_certificate
    (P := P) (mu := mu) (L := L)
    (hMuLeL := hMuLeL)
    (hLamPos := hLamPos) (hKpos := hKpos)
    (hSymm1 := hSymm1) (hEigRange1 := hEigRange1)
    (hSymm2 := hSymm2) (hEigRange2 := hEigRange2)

/-- `q10.tex` Step 8 (complexity formulas, offline + online):
all cost models are explicit and `N`-free; sparse-vs-dominant cost bridge is
also certified. -/
theorem q10_tex_step8_complexity_formulas
    (n r q dObs : Nat) :
    (matVecCost n r q = n * n * r + q * r) ∧
    (rhsFromObservedCost n r q = n * n * r + q * r) ∧
    (applyMatrixFreeSparseCost n r q = 2 * (n * n * r) + q * r + q * r) ∧
    (applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q) ∧
    (applyMatrixFreeObservedOnlineCost n r q dObs
      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost dObs q r) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond1Online iters n r q dObs
        = n * n * n + n * n * r
            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + n * n * r)) ∧
    (∀ iters : Nat,
      pcgSolveCostPrecond2Online iters n r q dObs
        = (n * n * n + r * r * r) + n * n * r
            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + (n * n * r + n * r * r))) ∧
    (denseDirectSolveCost n r = n * n * n * r * r * r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [matVecCost]
  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]
  · simp [applyMatrixFreeSparseCost, kernelMulCost, gatherKernelPredictSparseCost,
      scatterMulSparseCost]
  · exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q
  · rfl
  · intro iters
    simpa using pcgSolveCostPrecond1Online_eq iters n r q dObs
  · intro iters
    simpa using pcgSolveCostPrecond2Online_eq iters n r q dObs
  · exact denseDirectSolveCost_eq n r

/-- `q10.tex` Step 9 (PSD closure):
for PSD kernels, adding any nugget `nu > 0` yields SPD (`K + nu I`) and opens
PCG certificates on the shifted system. -/
theorem q10_tex_step9_psd_to_shift_core
    (P : TexObservedProblem n M r q)
    (hKpsd : P.K.PosSemidef)
    (nu : Real)
    (hNu : 0 < nu) :
    (P.withKernelShift nu).K.PosDef := by
  exact TexObservedProblem.withKernelShift_posDef_of_posSemidef
    (P := P) hKpsd (hNu := hNu)

/-- Human-readable `q10.tex` alignment overview (core, no hidden wrappers):
this theorem groups the paper-facing statements most readers want to inspect
first: system equivalence, observed RHS locking, sparse/CSR/online matvec,
and complexity formulas. -/
theorem q10_tex_human_aligned_overview
    (P : TexObservedProblem n M r q)
    {dObs : Nat}
    (F : ObsFactorProvider dObs q r)
    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F) :
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z) ∧
    (rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeBucketed P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      sparseMatVecTraceCost n r
        (applyMatrixFreeBucketedPlan P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W).2
          = applyMatrixFreeSparseCost n r q) ∧
    (rhsFromObservedRows P.K P.Ω P.vals (obsRowFromFactors F)
      = rhsFromObserved P.K P.Ω P.vals P.Z) ∧
    (∀ W : Matrix (Fin n) (Fin r) Real,
      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W
        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧
    (matVecCost n r q = n * n * r + q * r) ∧
    (rhsFromObservedCost n r q = n * n * r + q * r) ∧
    (applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q) ∧
    (applyMatrixFreeObservedOnlineCost n r q dObs
      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost dObs q r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W
    calc
      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z
          ↔ applyDenseVec P.K P.Z P.Ω P.lam W.vec
              = rhsVec P.K (sparseMTTKRP P.Ω P.vals P.Z) := by
                simp [rhsVec, rhsFromObserved]
      _ ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z :=
            q10_mainline_system_equiv_matrixFree
              (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
              (hK := P.hK) (W := W) (B := sparseMTTKRP P.Ω P.vals P.Z)
  · exact P.rhsVec_eq_rhsFromObserved
  · intro W
    exact applyMatrixFreeCanonicalBucketed_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · intro W
    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)
  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved
      (K := P.K) (Ω := P.Ω) (vals := P.vals) (Z := P.Z) (F := F) (hRows := hRows)
  · intro W
    exact applyMatrixFreeObserved_from_factors_eq_sparse
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows)
      (lam := P.lam) (W := W)
  · simp [matVecCost]
  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]
  · exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q
  · rfl

/-- `q10.tex` Step 10 (default-package component #1):
minimal-input spectral-indexed ambient-`N` complete certificate. -/
def q10_tex_step10_default_core
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
  q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Step 10 display form (same content as Step 10 core, but written in the
same explicit parameter style as Step 9 for human reading). -/
def q10_tex_step10_default_core_display
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
  q10_tex_step10_default_core
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- `q10.tex` Step 11 (default-package component #2):
closed-loop online spectral-indexed ambient-`N` certificate. -/
def q10_tex_step11_default_online_closure
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
  q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- Step 11 display form (same content as Step 11 online closure,
written with explicit human-readable parameters). -/
def q10_tex_step11_default_online_closure_display
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
  q10_tex_step11_default_online_closure
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)

/-- `q10.tex` Step 12 (default-package component #3):
PSD-to-shifted-PCG spectral-indexed ambient-`N` closure. -/
def q10_tex_step12_default_shifted_pcg
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
  q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (nu := nu) (hNu := hNu)

/-- Step 12 display form (same content as Step 12 shifted-PCG closure,
written with explicit human-readable parameters). -/
def q10_tex_step12_default_shifted_pcg_display
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
  q10_tex_step12_default_shifted_pcg
    (P := P) (F := F) (hRows := hRows) (hScale := hScale)
    (mu := mu) (L := L) (err0 := err0) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hErr0 := hErr0) (hEps := hEps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (nu := nu) (hNu := hNu)

/-- `q10.tex` Step 13 (default-package component #4):
non-stepwise polynomial-envelope tolerance closure. -/
def q10_tex_step13_default_poly_envelope
    (P : TexObservedProblem n M r q)
    (mu L eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hEps : 0 < eps)
    (hLamPos : 0 < P.lam) :=
  q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed
    (P := P) (mu := mu) (L := L) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hEps := hEps) (hLamPos := hLamPos)

/-- Step 13 display form (same content as Step 13 poly-envelope closure,
written with explicit human-readable parameters). -/
def q10_tex_step13_default_poly_envelope_display
    (P : TexObservedProblem n M r q)
    (mu L eps : Real)
    (hMuPos : 0 < mu)
    (hMuLtL : mu < L)
    (hEps : 0 < eps)
    (hLamPos : 0 < P.lam) :=
  q10_tex_step13_default_poly_envelope
    (P := P) (mu := mu) (L := L) (eps := eps)
    (hMuPos := hMuPos) (hMuLtL := hMuLtL)
    (hEps := hEps) (hLamPos := hLamPos)

/-- `q10.tex` Step 14 (default-package component #5):
spectral-interval binding to concrete preconditioned operators. -/
theorem q10_tex_step14_default_spectral_binding
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
  exact q10_tex_pcg_spectral_interval_binding_certificate
    (P := P) (mu := mu) (L := L)
    (hMuLeL := hMuLeL)
    (hLamPos := hLamPos) (hKpos := hKpos)
    (hSymm1 := hSymm1) (hEigRange1 := hEigRange1)
    (hSymm2 := hSymm2) (hEigRange2 := hEigRange2)

/-- `q10.tex` Step 15 (default-package component #6, optional strong branch):
strict Loewner/kappa/rate comparison for preconditioner-2 under data-lower assumptions. -/
theorem q10_tex_step15_default_strong_precond2_branch
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
  exact q10_tex_precond2_choice_strong_branch_observed
    (P := P)
    (beta := beta) (err0 := err0) (eps := eps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
    (hLamPos := hLamPos) (hKpos := hKpos)
    (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
    (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
    (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)

/-- `q10.tex` Step 16 (default-package component #7):
cost-model bridge between explicit sparse matvec and dominant matvec cost,
written in an explicit parameterized form. -/
theorem q10_tex_step16_default_cost_bridge
    (n r q : Nat) :
    applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q := by
  exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q

/-- `q10.tex` Step 17 (full default package, all components together):
this exports the exact default final package object (same as `q10_tex_final_answer`). -/
def q10_tex_step17_full_default_package :=
  @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- Step 17 display form (same final package as Step 17 core,
written as an explicit alias for human-first reading order). -/
def q10_tex_step17_full_default_package_display := q10_tex_step17_full_default_package

/-- Human-readable full answer alias:
keeps tex-order readability while including every component of the default final package. -/
abbrev q10_tex_human_aligned_full_answer := @q10_tex_step17_full_default_package

/-- Human-readable default export (full):
use this object as the entrypoint when reading `q10.tex` and Lean side-by-side. -/
abbrev q10_tex_human_aligned_default := @q10_tex_human_aligned_full_answer

end
end Q10
end AutoProof
