import autoproof.Q10.Core.Preconditioners.BaseDefs
import autoproof.Q10.Core.Preconditioners.LoewnerBridge
import autoproof.Q10.Core.Preconditioners.SpectralBounds

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Dominant flop model for one matrix-free application of `A`. -/
def matVecCost (n r q : Nat) : Nat := n * n * r + q * r

/-- Operation trace for one sparse matrix-free multiply implementation. -/
structure SparseMatVecTrace where
  kernelMulCount : Nat
  gatherDotCount : Nat
  scatterAxpyCount : Nat

/-- Convert a trace to dominant flop count (`kernel`: `n²r`, `dot/axpy`: `r`). -/
def sparseMatVecTraceCost (n r : Nat) (tr : SparseMatVecTrace) : Nat :=
  tr.kernelMulCount * (n * n * r) + tr.gatherDotCount * r + tr.scatterAxpyCount * r

theorem sum_rows_card_eq_q
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω) :
    (∑ i : Fin n, (B.rows i).card) = q := by
  classical
  calc
    ∑ i : Fin n, (B.rows i).card
        = ∑ i : Fin n, ∑ t ∈ (B.rows i), (1 : Nat) := by
            simp
    _ = ∑ i : Fin n, ∑ t : Fin q, (if (Ω t).2 = i then (1 : Nat) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hRows :
              B.rows i = Finset.univ.filter (fun t : Fin q => (Ω t).2 = i) := by
            ext t
            simpa [B.mem_rows_iff i t]
          rw [hRows]
          simpa using
            (Finset.sum_filter (s := Finset.univ)
              (p := fun t : Fin q => (Ω t).2 = i)
              (f := fun _ : Fin q => (1 : Nat)))
    _ = ∑ t : Fin q, ∑ i : Fin n, (if (Ω t).2 = i then (1 : Nat) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ t : Fin q, (1 : Nat) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simpa using
            (Fintype.sum_ite_eq (i := (Ω t).2) (f := fun _ : Fin n => (1 : Nat)))
    _ = q := by
          simp

/-- Bucketed Step-C dominant cost: total bucket sizes times vector length `r`. -/
def scatterMulBucketedCost
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (r : Nat) : Nat :=
  (∑ i : Fin n, (B.rows i).card) * r

theorem scatterMulBucketedCost_eq_sparse
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω) :
    scatterMulBucketedCost Ω B r = q * r := by
  simp [scatterMulBucketedCost, sum_rows_card_eq_q (Ω := Ω) (B := B)]

/-- Program-level bucketed Step-C plan plus operation trace (CSR-like accumulation path). -/
def scatterMulBucketedPlan
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    Matrix (Fin n) (Fin r) Real × SparseMatVecTrace :=
  (scatterMulBucketed Ω B Z u,
    { kernelMulCount := 0, gatherDotCount := 0
      scatterAxpyCount := ∑ i : Fin n, (B.rows i).card })

theorem scatterMulBucketedPlan_out
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    (scatterMulBucketedPlan Ω B Z u).1 = scatterMulBucketed Ω B Z u := rfl

theorem scatterMulBucketedPlan_cost_eq_sparse
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    sparseMatVecTraceCost n r (scatterMulBucketedPlan Ω B Z u).2 = q * r := by
  simp [scatterMulBucketedPlan, sparseMatVecTraceCost,
    sum_rows_card_eq_q (Ω := Ω) (B := B)]

/-- Cost of sparse Step-B (`q` observed row-dot products, length `r`). -/
def gatherKernelPredictSparseCost (q r : Nat) : Nat := q * r

/-- Cost of sparse Step-C (`q` row updates of length `r`). -/
def scatterMulSparseCost (q r : Nat) : Nat := q * r

theorem scatterMulBucketedCost_eq_scatterMulSparseCost
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω) :
    scatterMulBucketedCost Ω B r = scatterMulSparseCost q r := by
  simp [scatterMulBucketedCost_eq_sparse, scatterMulSparseCost]

theorem scatterMulBucketedPlan_cost_eq_scatterMulSparseCost
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    sparseMatVecTraceCost n r (scatterMulBucketedPlan Ω B Z u).2
      = scatterMulSparseCost q r := by
  simp [scatterMulBucketedPlan_cost_eq_sparse, scatterMulSparseCost]

theorem bucketed_scatter_correct_and_cost
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    scatterMulBucketed Ω B Z u = scatterMulSparse Ω Z u ∧
    sparseMatVecTraceCost n r (scatterMulBucketedPlan Ω B Z u).2
      = scatterMulSparseCost q r := by
  refine ⟨scatterMulBucketed_eq_scatterMulSparse (Ω := Ω) (B := B) (Z := Z) (u := u), ?_⟩
  exact scatterMulBucketedPlan_cost_eq_scatterMulSparseCost
    (Ω := Ω) (B := B) (Z := Z) (u := u)

theorem canonical_bucketed_scatter_correct_and_cost
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    scatterMulBucketed Ω (canonicalObsBuckets Ω) Z u = scatterMulSparse Ω Z u ∧
    sparseMatVecTraceCost n r
      (scatterMulBucketedPlan Ω (canonicalObsBuckets Ω) Z u).2
        = scatterMulSparseCost q r := by
  exact bucketed_scatter_correct_and_cost
    (Ω := Ω) (B := canonicalObsBuckets Ω) (Z := Z) (u := u)

/-- Dominant flop model for one `K`-times-matrix product (`n × n` by `n × r`). -/
def kernelMulCost (n r : Nat) : Nat := n * n * r

/-- Explicit sparse matvec cost (two `K`-multiplies + Step-B + Step-C). -/
def applyMatrixFreeSparseCost (n r q : Nat) : Nat :=
  2 * kernelMulCost n r + gatherKernelPredictSparseCost q r + scatterMulSparseCost q r

/-- Cost-model bridge: explicit sparse matvec cost is exactly `2 * matVecCost`. -/
theorem applyMatrixFreeSparseCost_eq_two_mul_matVecCost (n r q : Nat) :
    applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q := by
  simp [applyMatrixFreeSparseCost, matVecCost, kernelMulCost,
    gatherKernelPredictSparseCost, scatterMulSparseCost]
  ring

/-- Big-O bridge in inequality form: explicit sparse matvec cost is within a
constant factor of dominant `matVecCost`. -/
theorem applyMatrixFreeSparseCost_le_two_mul_matVecCost (n r q : Nat) :
    applyMatrixFreeSparseCost n r q ≤ 2 * matVecCost n r q := by
  simpa [applyMatrixFreeSparseCost_eq_two_mul_matVecCost (n := n) (r := r) (q := q)]

/-- Extra online row-generation cost when observed rows are produced from `d` factors
(`q` rows, each row takes `d*r` Hadamard multiplications). -/
def obsRowFromFactorsGenerationCost (d q r : Nat) : Nat := q * d * r

/-- End-to-end matvec model cost with online observed-row generation from factors. -/
def applyMatrixFreeObservedOnlineCost (n r q d : Nat) : Nat :=
  applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost d q r

/-- RHS-from-observed sparse cost (sparse MTTKRP + one `K`-multiply). -/
def rhsFromObservedCost (n r q : Nat) : Nat :=
  kernelMulCost n r + gatherKernelPredictSparseCost q r

/-- Sparse outer-loop work model: one RHS build + `iters` sparse matvecs. -/
def sparseSolveCost (iters n r q : Nat) : Nat :=
  rhsFromObservedCost n r q + iters * applyMatrixFreeSparseCost n r q

/-- Program-level sparse matvec plan: output plus operation trace. -/
def applyMatrixFreeSparsePlan
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real × SparseMatVecTrace :=
  (applyMatrixFreeSparse K Z Ω lam W,
    { kernelMulCount := 2, gatherDotCount := q, scatterAxpyCount := q })

theorem applyMatrixFreeSparsePlan_out
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    (applyMatrixFreeSparsePlan K Z Ω lam W).1 = applyMatrixFreeSparse K Z Ω lam W := rfl

theorem applyMatrixFreeSparsePlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    sparseMatVecTraceCost n r (applyMatrixFreeSparsePlan K Z Ω lam W).2
      = applyMatrixFreeSparseCost n r q := by
  simp [applyMatrixFreeSparsePlan, sparseMatVecTraceCost, applyMatrixFreeSparseCost,
    kernelMulCost, gatherKernelPredictSparseCost, scatterMulSparseCost]

/-- Program-level bucketed/CSR sparse matvec plan. -/
def applyMatrixFreeBucketedPlan
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real × SparseMatVecTrace :=
  (applyMatrixFreeBucketed K Z Ω B lam W,
    { kernelMulCount := 2, gatherDotCount := q
      scatterAxpyCount := ∑ i : Fin n, (B.rows i).card })

theorem applyMatrixFreeBucketedPlan_out
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    (applyMatrixFreeBucketedPlan K Z Ω B lam W).1 = applyMatrixFreeBucketed K Z Ω B lam W := rfl

theorem applyMatrixFreeBucketedPlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    sparseMatVecTraceCost n r (applyMatrixFreeBucketedPlan K Z Ω B lam W).2
      = applyMatrixFreeSparseCost n r q := by
  simp [applyMatrixFreeBucketedPlan, sparseMatVecTraceCost, applyMatrixFreeSparseCost,
    kernelMulCost, gatherKernelPredictSparseCost, scatterMulSparseCost,
    sum_rows_card_eq_q (Ω := Ω) (B := B)]

theorem applyMatrixFreeCanonicalBucketedPlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    sparseMatVecTraceCost n r
      (applyMatrixFreeBucketedPlan K Z Ω (canonicalObsBuckets Ω) lam W).2
        = applyMatrixFreeSparseCost n r q := by
  exact applyMatrixFreeBucketedPlan_cost_eq
    (K := K) (Z := Z) (Ω := Ω) (B := canonicalObsBuckets Ω) (lam := lam) (W := W)

/-- Program-level sparse matvec plan using on-demand observed rows `zObs`
(no explicit `Z` storage path from `solution.txt`). -/
def applyMatrixFreeObservedPlan
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real × SparseMatVecTrace :=
  (applyMatrixFreeObserved K Ω zObs lam W,
    { kernelMulCount := 2, gatherDotCount := q, scatterAxpyCount := q })

theorem applyMatrixFreeObservedPlan_out
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    (applyMatrixFreeObservedPlan K Ω zObs lam W).1 = applyMatrixFreeObserved K Ω zObs lam W := rfl

theorem applyMatrixFreeObservedPlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    sparseMatVecTraceCost n r (applyMatrixFreeObservedPlan K Ω zObs lam W).2
      = applyMatrixFreeSparseCost n r q := by
  simp [applyMatrixFreeObservedPlan, sparseMatVecTraceCost, applyMatrixFreeSparseCost,
    kernelMulCost, gatherKernelPredictSparseCost, scatterMulSparseCost]

/-- Program-level RHS plan from observed data plus operation trace. -/
def rhsFromObservedPlan
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) :
    (Fin r × Fin n → Real) × SparseMatVecTrace :=
  (rhsFromObserved K Ω vals Z,
    { kernelMulCount := 1, gatherDotCount := 0, scatterAxpyCount := q })

theorem rhsFromObservedPlan_out
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) :
    (rhsFromObservedPlan K Ω vals Z).1 = rhsFromObserved K Ω vals Z := rfl

theorem rhsFromObservedPlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) :
    sparseMatVecTraceCost n r (rhsFromObservedPlan K Ω vals Z).2
      = rhsFromObservedCost n r q := by
  simp [rhsFromObservedPlan, sparseMatVecTraceCost, rhsFromObservedCost,
    kernelMulCost, gatherKernelPredictSparseCost]

/-- Program-level RHS plan from observed data using on-demand observed rows `zObs`. -/
def rhsFromObservedRowsPlan
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (zObs : ObsRowProvider q r) :
    (Fin r × Fin n → Real) × SparseMatVecTrace :=
  (rhsFromObservedRows K Ω vals zObs,
    { kernelMulCount := 1, gatherDotCount := 0, scatterAxpyCount := q })

theorem rhsFromObservedRowsPlan_out
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (zObs : ObsRowProvider q r) :
    (rhsFromObservedRowsPlan K Ω vals zObs).1 = rhsFromObservedRows K Ω vals zObs := rfl

theorem rhsFromObservedRowsPlan_cost_eq
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (zObs : ObsRowProvider q r) :
    sparseMatVecTraceCost n r (rhsFromObservedRowsPlan K Ω vals zObs).2
      = rhsFromObservedCost n r q := by
  simp [rhsFromObservedRowsPlan, sparseMatVecTraceCost, rhsFromObservedCost,
    kernelMulCost, gatherKernelPredictSparseCost]

/-- Aggregate sparse-solve trace: RHS build + `iters` sparse matvecs. -/
def sparseSolveTrace (iters q : Nat) : SparseMatVecTrace :=
  { kernelMulCount := 1 + 2 * iters
    gatherDotCount := iters * q
    scatterAxpyCount := q + iters * q }

theorem sparseSolveTrace_cost_eq
    (iters n r q : Nat) :
    sparseMatVecTraceCost n r (sparseSolveTrace iters q) = sparseSolveCost iters n r q := by
  simp [sparseSolveTrace, sparseMatVecTraceCost, sparseSolveCost, rhsFromObservedCost,
    applyMatrixFreeSparseCost, kernelMulCost, gatherKernelPredictSparseCost,
    scatterMulSparseCost]
  ring

/-- Abstract residual-contract interface for the PSD branch:
`residual x0 k = b - A x_k` with `A` evaluated through sparse matrix-free operator. -/
structure PSDResidualSpec (P : Problem n M r q) where
  run : Matrix (Fin n) (Fin r) Real → Nat → Matrix (Fin n) (Fin r) Real
  residual : Matrix (Fin n) (Fin r) Real → Nat → Matrix (Fin n) (Fin r) Real
  residual_spec :
    ∀ (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat),
      residual x0 k = rhsMat P - applyASparse P (run x0 k)

/-- Concrete matrix-free residual-correction fallback iteration
(step size `1/(k+1)`), used as an internal PSD branch witness. -/
def residualCorrectionRun (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) : Nat → Matrix (Fin n) (Fin r) Real
  | 0 => x0
  | k + 1 =>
      let xk := residualCorrectionRun P x0 k
      let rk := rhsMat P - applyASparse P xk
      xk + ((1 : Real) / (Nat.succ k : Real)) • rk

/-- Residual map for `residualCorrectionRun`. -/
def residualCorrectionResidual (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat) : Matrix (Fin n) (Fin r) Real :=
  rhsMat P - applyASparse P (residualCorrectionRun P x0 k)

/-- Internal concrete residual-correction instance of `PSDResidualSpec`. -/
def residualCorrectionSpec (P : Problem n M r q) : PSDResidualSpec P where
  run := fun x0 k => residualCorrectionRun P x0 k
  residual := fun x0 k => residualCorrectionResidual P x0 k
  residual_spec := by
    intro x0 k
    rfl

theorem PSDResidualSpec.stop_correct_matrix (P : Problem n M r q)
    (S : PSDResidualSpec P)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat)
    (hStop : S.residual x0 k = 0) :
    applyASparse P (S.run x0 k) = rhsMat P := by
  have hRes := S.residual_spec x0 k
  rw [hRes] at hStop
  exact (sub_eq_zero.mp hStop).symm

theorem PSDResidualSpec.stop_correct_dense (P : Problem n M r q)
    (S : PSDResidualSpec P)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat)
    (hStop : S.residual x0 k = 0) :
    applyDenseVec P.K P.Z P.Ω P.lam (S.run x0 k).vec = rhsVec P.K P.B := by
  have hMat : applyASparse P (S.run x0 k) = rhsMat P :=
    PSDResidualSpec.stop_correct_matrix (P := P) (S := S) (x0 := x0) (k := k) hStop
  have hMF : applyMatrixFreeSparse P.K P.Z P.Ω P.lam (S.run x0 k) = P.K * P.B := by
    simpa [applyASparse, rhsMat] using hMat
  exact (q10_system_equiv_matrixFreeSparse
    (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (hK := P.hK)
    (W := S.run x0 k) (B := P.B)).mpr hMF

/-- Abstract normal-equation-residual contract interface for PSD branch:
tracks both residual and normal-equation residual. -/
structure PSDNormalEqSpec (P : Problem n M r q) where
  run : Matrix (Fin n) (Fin r) Real → Nat → Matrix (Fin n) (Fin r) Real
  residual : Matrix (Fin n) (Fin r) Real → Nat → Matrix (Fin n) (Fin r) Real
  normalResidual : Matrix (Fin n) (Fin r) Real → Nat → Matrix (Fin n) (Fin r) Real
  residual_spec :
    ∀ (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat),
      residual x0 k = rhsMat P - applyASparse P (run x0 k)
  normalResidual_spec :
    ∀ (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat),
      normalResidual x0 k = applyASparse P (residual x0 k)

/-- Concrete normal-equation residual-correction fallback iteration,
used as an internal PSD branch witness. -/
def normalEqCorrectionRun (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) : Nat → Matrix (Fin n) (Fin r) Real
  | 0 => x0
  | k + 1 =>
      let xk := normalEqCorrectionRun P x0 k
      let rk := rhsMat P - applyASparse P xk
      xk + ((1 : Real) / (Nat.succ k : Real)) • (applyASparse P rk)

/-- Residual map for `normalEqCorrectionRun`. -/
def normalEqCorrectionResidual (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat) : Matrix (Fin n) (Fin r) Real :=
  rhsMat P - applyASparse P (normalEqCorrectionRun P x0 k)

/-- Normal-equation residual map for `normalEqCorrectionRun`. -/
def normalEqCorrectionNormalResidual (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat) : Matrix (Fin n) (Fin r) Real :=
  applyASparse P (normalEqCorrectionResidual P x0 k)

/-- Internal concrete normal-equation residual-correction instance of `PSDNormalEqSpec`. -/
def normalEqCorrectionSpec (P : Problem n M r q) : PSDNormalEqSpec P where
  run := fun x0 k => normalEqCorrectionRun P x0 k
  residual := fun x0 k => normalEqCorrectionResidual P x0 k
  normalResidual := fun x0 k => normalEqCorrectionNormalResidual P x0 k
  residual_spec := by
    intro x0 k
    rfl
  normalResidual_spec := by
    intro x0 k
    rfl

theorem PSDNormalEqSpec.stop_correct_normalEq (P : Problem n M r q)
    (S : PSDNormalEqSpec P)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat)
    (hStop : S.normalResidual x0 k = 0) :
    applyASparse P (rhsMat P - applyASparse P (S.run x0 k)) = 0 := by
  rw [S.normalResidual_spec x0 k, S.residual_spec x0 k] at hStop
  exact hStop

theorem PSDNormalEqSpec.stop_correct_dense_of_zero_residual (P : Problem n M r q)
    (S : PSDNormalEqSpec P)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat)
    (hStop : S.residual x0 k = 0) :
    applyDenseVec P.K P.Z P.Ω P.lam (S.run x0 k).vec = rhsVec P.K P.B := by
  have hRes := S.residual_spec x0 k
  rw [hStop] at hRes
  have hMat : applyASparse P (S.run x0 k) = rhsMat P := by
    exact (sub_eq_zero.mp hRes.symm).symm
  have hMF : applyMatrixFreeSparse P.K P.Z P.Ω P.lam (S.run x0 k) = P.K * P.B := by
    simpa [applyASparse, rhsMat] using hMat
  exact (q10_system_equiv_matrixFreeSparse
    (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (hK := P.hK)
    (W := S.run x0 k) (B := P.B)).mpr hMF

/-- PSD residual-correction dominant per-iteration cost model
(one matrix-free `A` apply). -/
def residualCorrectionIterCost (n r q : Nat) : Nat := matVecCost n r q

/-- PSD residual-correction total model cost. -/
def residualCorrectionSolveCost (iters n r q : Nat) : Nat :=
  rhsFromObservedCost n r q + iters * residualCorrectionIterCost n r q

/-- PSD normal-equation correction dominant per-iteration cost model
(two matrix-free applies). -/
def normalEqCorrectionIterCost (n r q : Nat) : Nat := 2 * matVecCost n r q

/-- PSD normal-equation correction total model cost. -/
def normalEqCorrectionSolveCost (iters n r q : Nat) : Nat :=
  rhsFromObservedCost n r q + iters * normalEqCorrectionIterCost n r q

theorem residualCorrectionSolveCost_eq_model (iters n r q : Nat) :
    residualCorrectionSolveCost iters n r q = rhsFromObservedCost n r q + iters * matVecCost n r q := by
  simp [residualCorrectionSolveCost, residualCorrectionIterCost]

theorem normalEqCorrectionSolveCost_eq_model (iters n r q : Nat) :
    normalEqCorrectionSolveCost iters n r q = rhsFromObservedCost n r q + iters * (2 * matVecCost n r q) := by
  simp [normalEqCorrectionSolveCost, normalEqCorrectionIterCost]

/-- PSD solver branch certificate in `q10.tex` style:
PSD semantics + residual-contract/normal-equation-contract stop-correctness
contracts + no-`N` cost models. -/
theorem q10_psd_solver_branch_residual_normalEq
    (P : TexProblem n M r q)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (residualSolver : PSDResidualSpec P.toProblem)
    (normalEqSolver : PSDNormalEqSpec P.toProblem)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) :
    (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
    (denseMatrix P.toProblem).PosSemidef ∧
    (residualSolver.residual x0 k = 0 →
      applyDenseVec P.K P.Z P.Ω P.lam (residualSolver.run x0 k).vec = rhsVec P.K P.B) ∧
    (normalEqSolver.normalResidual x0 k = 0 →
      applyASparse P.toProblem (rhsMat P.toProblem - applyASparse P.toProblem (normalEqSolver.run x0 k)) = 0) ∧
    (normalEqSolver.residual x0 k = 0 →
      applyDenseVec P.K P.Z P.Ω P.lam (normalEqSolver.run x0 k).vec = rhsVec P.K P.B) ∧
    residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
    normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q) := by
  refine ⟨P.selection_subidentity, denseMatrix_posSemidef (P := P.toProblem) hLamNonneg hKpsd,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro hStop
    exact PSDResidualSpec.stop_correct_dense
      (P := P.toProblem) (S := residualSolver) (x0 := x0) (k := k) hStop
  · intro hStop
    exact PSDNormalEqSpec.stop_correct_normalEq
      (P := P.toProblem) (S := normalEqSolver) (x0 := x0) (k := k) hStop
  · intro hStop
    exact PSDNormalEqSpec.stop_correct_dense_of_zero_residual
      (P := P.toProblem) (S := normalEqSolver) (x0 := x0) (k := k) hStop
  · exact residualCorrectionSolveCost_eq_model k n r q
  · exact normalEqCorrectionSolveCost_eq_model k n r q

/-- PSD branch certificate instantiated with internal concrete fallback iterators
(no external solver parameter required). -/
theorem q10_psd_solver_branch_residual_normalEq_concrete
    (P : TexProblem n M r q)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) :
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
    normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q) := by
  exact q10_psd_solver_branch_residual_normalEq
    (P := P) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
    (residualSolver := residualCorrectionSpec P.toProblem)
    (normalEqSolver := normalEqCorrectionSpec P.toProblem)
    (x0 := x0) (k := k)

/-- PSD branch residual-tolerance certificates (matrix-free concrete iterators):
if reported residual (or normal residual) norm is within `epsTol`, then the
corresponding algebraic residual expression is within the same tolerance. -/
theorem q10_psd_solver_branch_residual_normalEq_concrete_tol
    (P : TexProblem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) (epsTol : Real) :
    (‖((residualCorrectionSpec P.toProblem).residual x0 k).vec‖ ≤ epsTol →
      ‖(rhsMat P.toProblem
          - applyASparse P.toProblem ((residualCorrectionSpec P.toProblem).run x0 k)).vec‖ ≤ epsTol) ∧
    (‖((normalEqCorrectionSpec P.toProblem).normalResidual x0 k).vec‖ ≤ epsTol →
      ‖(applyASparse P.toProblem
          (rhsMat P.toProblem - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k))).vec‖ ≤ epsTol) ∧
    (‖((normalEqCorrectionSpec P.toProblem).residual x0 k).vec‖ ≤ epsTol →
      ‖(rhsMat P.toProblem
          - applyASparse P.toProblem ((normalEqCorrectionSpec P.toProblem).run x0 k)).vec‖ ≤ epsTol) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hTol
    simpa [residualCorrectionSpec, residualCorrectionResidual] using hTol
  · intro hTol
    simpa [normalEqCorrectionSpec, normalEqCorrectionNormalResidual, normalEqCorrectionResidual] using hTol
  · intro hTol
    simpa [normalEqCorrectionSpec, normalEqCorrectionResidual] using hTol

/-- Concrete PSD fallback attainability (residual-correction and normal-equation variants):
under standard stepwise `rho`-contraction assumptions, each concrete
residual sequence reaches any tolerance `eps > 0` at a finite iterate. -/
theorem q10_psd_solver_branch_concrete_attains_tol_of_stepwise
    (P : TexProblem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {rho err0 eps : Real}
    (hRhoNonneg : 0 ≤ rho)
    (hRhoLtOne : rho < 1)
    (hErr0 : 0 < err0)
    (hEps : 0 < eps)
    (hInitRes :
      ‖((residualCorrectionSpec P.toProblem).residual x0 0).vec‖ ≤ 2 * err0)
    (hStepRes :
      ∀ k : Nat,
        ‖((residualCorrectionSpec P.toProblem).residual x0 (k + 1)).vec‖
          ≤ rho * ‖((residualCorrectionSpec P.toProblem).residual x0 k).vec‖)
    (hInitNormal :
      ‖((normalEqCorrectionSpec P.toProblem).residual x0 0).vec‖ ≤ 2 * err0)
    (hStepNormal :
      ∀ k : Nat,
        ‖((normalEqCorrectionSpec P.toProblem).residual x0 (k + 1)).vec‖
          ≤ rho * ‖((normalEqCorrectionSpec P.toProblem).residual x0 k).vec‖) :
    (∃ kRes : Nat,
      ‖((residualCorrectionSpec P.toProblem).residual x0 kRes).vec‖ ≤ eps) ∧
    (∃ kNormal : Nat,
      ‖((normalEqCorrectionSpec P.toProblem).residual x0 kNormal).vec‖ ≤ eps) := by
  let rseq : Nat → Real :=
    fun k => ‖((residualCorrectionSpec P.toProblem).residual x0 k).vec‖
  let nseq : Nat → Real :=
    fun k => ‖((normalEqCorrectionSpec P.toProblem).residual x0 k).vec‖
  have hReach :
      ∀ seq : Nat → Real,
        (∀ k : Nat, seq (k + 1) ≤ rho * seq k) →
        seq 0 ≤ 2 * err0 →
        ∃ k : Nat, seq k ≤ eps := by
    intro seq hStep hInit
    have hGeom : ∀ k : Nat, seq k ≤ rho ^ k * seq 0 := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          calc
            seq (k + 1) ≤ rho * seq k := hStep k
            _ ≤ rho * (rho ^ k * seq 0) := by
                  exact mul_le_mul_of_nonneg_left ih hRhoNonneg
            _ = rho ^ (k + 1) * seq 0 := by ring
    have hBound : ∀ k : Nat, seq k ≤ 2 * rho ^ k * err0 := by
      intro k
      have hPowNonneg : 0 ≤ rho ^ k := by
        exact pow_nonneg hRhoNonneg k
      have hInitScaled : rho ^ k * seq 0 ≤ rho ^ k * (2 * err0) := by
        exact mul_le_mul_of_nonneg_left hInit hPowNonneg
      calc
        seq k ≤ rho ^ k * seq 0 := hGeom k
        _ ≤ rho ^ k * (2 * err0) := hInitScaled
        _ = 2 * rho ^ k * err0 := by ring
    have hTwoErr0Pos : 0 < 2 * err0 := by nlinarith
    have hDelta : 0 < eps / (2 * err0) := div_pos hEps hTwoErr0Pos
    rcases exists_pow_lt_of_lt_one hDelta hRhoLtOne with ⟨k, hkPow⟩
    have hScaled : (2 * err0) * rho ^ k ≤ (2 * err0) * (eps / (2 * err0)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hkPow) (le_of_lt hTwoErr0Pos)
    have hTol : 2 * rho ^ k * err0 ≤ eps := by
      calc
        2 * rho ^ k * err0 = (2 * err0) * rho ^ k := by ring
        _ ≤ (2 * err0) * (eps / (2 * err0)) := hScaled
        _ = eps := by field_simp [ne_of_gt hTwoErr0Pos]
    exact ⟨k, le_trans (hBound k) hTol⟩
  have hRes :
      ∃ kRes : Nat, rseq kRes ≤ eps :=
    hReach rseq (by intro k; simpa [rseq] using hStepRes k) (by simpa [rseq] using hInitRes)
  have hNormal :
      ∃ kNormal : Nat, nseq kNormal ≤ eps :=
    hReach nseq (by intro k; simpa [nseq] using hStepNormal k) (by simpa [nseq] using hInitNormal)
  refine ⟨?_, ?_⟩
  · rcases hRes with ⟨kRes, hkRes⟩
    exact ⟨kRes, by simpa [rseq] using hkRes⟩
  · rcases hNormal with ⟨kNormal, hkNormal⟩
    exact ⟨kNormal, by simpa [nseq] using hkNormal⟩

/-- Injective-observation contraction certificate used in strict Loewner refinements:
for `TexProblem`, `S Sᵀ ⪯q I` in quadratic form. -/
theorem q10_selection_projector_contractive
    (P : TexProblem n M r q) :
    QuadraticLe ((selectionMatrix P.Ω) * (selectionMatrix P.Ω)ᵀ)
      (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) := by
  exact selection_projector_quadratic_le_one_of_injective (Ω := P.Ω) P.hOmegaInj

/-- Closure of the two remaining strict gaps from `solution.txt`:
`A` vs `M₂` Loewner-style inequalities are made explicit, and the pure-PSD
solver branch is closed via residual/normal-equation stop-correctness + no-`N`
cost models. -/
theorem q10_remaining_gap_closure
    (P : TexProblem n M r q)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    {c : Real} (hCone : 1 ≤ c)
    (hDataUpper : ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x)
        ≤ c * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x)))
    (residualSolver : PSDResidualSpec P.toProblem)
    (normalEqSolver : PSDNormalEqSpec P.toProblem)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) :
    (QuadraticLe (precond1Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem) (c • precond2Matrix P.toProblem)) ∧
    ((selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      (residualSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (residualSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      (normalEqSolver.normalResidual x0 k = 0 →
        applyASparse P.toProblem (rhsMat P.toProblem - applyASparse P.toProblem (normalEqSolver.run x0 k)) = 0) ∧
      (normalEqSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (normalEqSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) := by
  refine ⟨?_, ?_⟩
  · exact dense_precond2_loewner_certificate
      (P := P.toProblem) (hLam := hLamNonneg) (hKpsd := hKpsd)
      (hCone := hCone) (hDataUpper := hDataUpper)
  · exact q10_psd_solver_branch_residual_normalEq
      (P := P) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
      (residualSolver := residualSolver) (normalEqSolver := normalEqSolver) (x0 := x0) (k := k)

/-- Concrete version of `q10_remaining_gap_closure` with no extra kernel-structure assumption:
the data-term upper bound is discharged from injective `Ω` plus PSD `K`,
using the automatic bound `KᵀK ⪯ (trace K + 1) K`. -/
theorem q10_remaining_gap_closure_concrete
    (P : TexProblem n M r q)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (residualSolver : PSDResidualSpec P.toProblem)
    (normalEqSolver : PSDNormalEqSpec P.toProblem)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) :
    (QuadraticLe (precond1Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem)
        (((P.K.trace + 1) : Real) • precond2Matrix P.toProblem)) ∧
    ((selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) ∧
      (denseMatrix P.toProblem).PosSemidef ∧
      (residualSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (residualSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      (normalEqSolver.normalResidual x0 k = 0 →
        applyASparse P.toProblem (rhsMat P.toProblem - applyASparse P.toProblem (normalEqSolver.run x0 k)) = 0) ∧
      (normalEqSolver.residual x0 k = 0 →
        applyDenseVec P.K P.Z P.Ω P.lam (normalEqSolver.run x0 k).vec = rhsVec P.K P.B) ∧
      residualCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * matVecCost n r q ∧
      normalEqCorrectionSolveCost k n r q = rhsFromObservedCost n r q + k * (2 * matVecCost n r q)) := by
  have hTraceNonneg : 0 ≤ P.K.trace := Matrix.PosSemidef.trace_nonneg hKpsd
  have hCone : 1 ≤ (P.K.trace + 1 : Real) := by nlinarith
  refine q10_remaining_gap_closure
    (P := P) (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)
    (hCone := hCone) (hDataUpper := ?_)
    (residualSolver := residualSolver) (normalEqSolver := normalEqSolver) (x0 := x0) (k := k)
  intro x
  exact dense_data_upper_from_injective_and_kernel_psd
    (P := P.toProblem) (hΩinj := P.hOmegaInj) (hKpsd := hKpsd) x



end
end Q10
end AutoProof
