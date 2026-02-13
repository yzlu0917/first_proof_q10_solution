import autoproof.Q10.Core.Operators.ObservedOps
import autoproof.Q10.Core.KrylovAlgorithm.DefsAndPoly
import autoproof.Q10.Core.KrylovAlgorithm.PreconditionedPoly
import autoproof.Q10.Core.Preconditioners.BaseDefs
import autoproof.Q10.Core.CostAndPSD

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Executable PCG operation trace: counts matvec/preconditioner applications. -/
structure PCGTrace where
  matVecCount : Nat
  precondApplyCount : Nat

/-- Recursive PCG runner paired with an operation trace. -/
def pcgRunTrace (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real) : Nat → (PCGState n r × PCGTrace)
  | 0 => (pcgInit P Minv x0, { matVecCount := 0, precondApplyCount := 0 })
  | k + 1 =>
      let prev := pcgRunTrace P Minv x0 k
      let st := prev.1
      let tr := prev.2
      (pcgStep P Minv st, { matVecCount := tr.matVecCount + 1, precondApplyCount := tr.precondApplyCount + 1 })

theorem pcgRunTrace_state_eq_pcgRun (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    (pcgRunTrace P Minv x0 iters).1 = pcgRun P Minv x0 iters := by
  induction iters with
  | zero =>
      simp [pcgRunTrace, pcgRun]
  | succ k ih =>
      simp [pcgRunTrace, pcgRun, ih]

theorem pcgRunTrace_matVecCount_eq (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    (pcgRunTrace P Minv x0 iters).2.matVecCount = iters := by
  induction iters with
  | zero =>
      simp [pcgRunTrace]
  | succ k ih =>
      simp [pcgRunTrace, ih]

theorem pcgRunTrace_precondApplyCount_eq (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    (pcgRunTrace P Minv x0 iters).2.precondApplyCount = iters := by
  induction iters with
  | zero =>
      simp [pcgRunTrace]
  | succ k ih =>
      simp [pcgRunTrace, ih]

/-- Dominant flop model for one PCG iteration (one matvec + one preconditioner apply). -/
def pcgIterCost (n r q : Nat) : Nat := matVecCost n r q + kernelMulCost n r

/-- Preconditioner #1 setup cost model (`K`-factorization, e.g. Cholesky). -/
def precond1SetupCost (n : Nat) : Nat := n * n * n

/-- Preconditioner #1 apply cost model (`O(n^2 r)`). -/
def precond1ApplyCost (n r : Nat) : Nat := n * n * r

/-- Preconditioner #2 setup cost model (`K` and `G` eigendecompositions). -/
def precond2SetupCost (n r : Nat) : Nat := n * n * n + r * r * r

/-- Cost to build factor-Gram Hadamard chain
`ZᵀZ = ⊙ᵢ (AᵢᵀAᵢ)` without explicit `Z : M × r`:
per mode: `modeSizes i * r^2`, plus `d` Hadamard merges. -/
def gramFromFactorsCost
    {d : Nat}
    (modeSizes : Fin d → Nat) (r : Nat) : Nat :=
  (∑ i : Fin d, modeSizes i * r * r) + d * r * r

/-- Preconditioner #2 setup with factor-Gram path:
`K` eig/factorization + small `r×r` eig/factorization + factor-Gram assembly. -/
def precond2SetupCostFromFactorGrams
    {d : Nat}
    (modeSizes : Fin d → Nat) (n r : Nat) : Nat :=
  n * n * n + r * r * r + gramFromFactorsCost modeSizes r

theorem precond2SetupCostFromFactorGrams_eq
    {d : Nat}
    (modeSizes : Fin d → Nat) (n r : Nat) :
    precond2SetupCostFromFactorGrams modeSizes n r
      = n * n * n + r * r * r + (∑ i : Fin d, modeSizes i * r * r) + d * r * r := by
  simp [precond2SetupCostFromFactorGrams, gramFromFactorsCost, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

/-- Preconditioner #2 apply cost model (`UᵀR`, right-multiply `V`, diagonal solve, back-transform). -/
def precond2ApplyCost (n r : Nat) : Nat := n * n * r + n * r * r

/-- Trace for one explicit preconditioner-#2 application plan. -/
structure Precond2ApplyTrace where
  kernelSolveCount : Nat
  rowGramSolveCount : Nat

/-- Cost accounting for a preconditioner-#2 application trace. -/
def precond2ApplyTraceCost (n r : Nat) (tr : Precond2ApplyTrace) : Nat :=
  tr.kernelSolveCount * (n * n * r) + tr.rowGramSolveCount * (r * r)

/-- Program-level plan for applying preconditioner #2 in closed form
`K⁻¹ * R * (ZᵀZ + λI)⁻¹`, with a small operation trace. -/
def precond2ApplyPlan (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real × Precond2ApplyTrace :=
  (P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹,
    { kernelSolveCount := 1, rowGramSolveCount := n })

theorem precond2ApplyPlan_out_closed_form (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) :
    (precond2ApplyPlan P R).1
      = P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹ := rfl

theorem precond2ApplyPlan_out_eq_precond2Apply (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    (precond2ApplyPlan P R).1 = precond2Apply P R := by
  rw [precond2ApplyPlan_out_closed_form]
  exact (precond2_apply_closed_form (P := P) hLam hKpos R).symm

theorem precond2ApplyPlan_cost_eq_model (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2ApplyTraceCost n r (precond2ApplyPlan P R).2 = precond2ApplyCost n r := by
  simp [precond2ApplyPlan, precond2ApplyTraceCost, precond2ApplyCost, Nat.mul_assoc]

theorem precond2ApplyPlan_bridge (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    (precond2ApplyPlan P R).1 = precond2Apply P R ∧
    precond2ApplyTraceCost n r (precond2ApplyPlan P R).2 = precond2ApplyCost n r ∧
    precond2Apply P R
      = P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹ := by
  refine ⟨precond2ApplyPlan_out_eq_precond2Apply (P := P) hLam hKpos R, ?_, ?_⟩
  · exact precond2ApplyPlan_cost_eq_model (P := P) R
  · exact precond2_apply_closed_form (P := P) hLam hKpos R

/-- Dominant total cost for `iters` PCG steps, including RHS setup. -/
def pcgTotalCost (iters n r q : Nat) : Nat :=
  kernelMulCost n r + iters * pcgIterCost n r q

/-- Total cost model when using preconditioner #1 in PCG. -/
def pcgSolveCostPrecond1 (iters n r q : Nat) : Nat :=
  precond1SetupCost n + kernelMulCost n r + iters * (matVecCost n r q + precond1ApplyCost n r)

/-- Total cost model when using preconditioner #2 in PCG. -/
def pcgSolveCostPrecond2 (iters n r q : Nat) : Nat :=
  precond2SetupCost n r + kernelMulCost n r + iters * (matVecCost n r q + precond2ApplyCost n r)

/-- Total cost model for fully online observed-row PCG with preconditioner #1:
per iteration uses `applyMatrixFreeObservedOnlineCost` instead of `matVecCost`. -/
def pcgSolveCostPrecond1Online (iters n r q d : Nat) : Nat :=
  precond1SetupCost n + kernelMulCost n r
    + iters * (applyMatrixFreeObservedOnlineCost n r q d + precond1ApplyCost n r)

/-- Total cost model for fully online observed-row PCG with preconditioner #2:
per iteration uses `applyMatrixFreeObservedOnlineCost` instead of `matVecCost`. -/
def pcgSolveCostPrecond2Online (iters n r q d : Nat) : Nat :=
  precond2SetupCost n r + kernelMulCost n r
    + iters * (applyMatrixFreeObservedOnlineCost n r q d + precond2ApplyCost n r)

theorem pcgSolveCostPrecond1Online_eq
    (iters n r q d : Nat) :
    pcgSolveCostPrecond1Online iters n r q d
      = n * n * n + n * n * r
          + iters * (applyMatrixFreeObservedOnlineCost n r q d + n * n * r) := by
  simp [pcgSolveCostPrecond1Online, precond1SetupCost, kernelMulCost, precond1ApplyCost]

theorem pcgSolveCostPrecond2Online_eq
    (iters n r q d : Nat) :
    pcgSolveCostPrecond2Online iters n r q d
      = (n * n * n + r * r * r) + n * n * r
          + iters * (applyMatrixFreeObservedOnlineCost n r q d + (n * n * r + n * r * r)) := by
  simp [pcgSolveCostPrecond2Online, precond2SetupCost, kernelMulCost, precond2ApplyCost]

/-- Dense direct-solver baseline for the `nr × nr` linear system:
`O((nr)^3) = O(n^3 r^3)`. -/
def denseDirectSolveCost (n r : Nat) : Nat :=
  n * n * n * r * r * r

theorem denseDirectSolveCost_eq (n r : Nat) :
    denseDirectSolveCost n r = n * n * n * r * r * r := rfl

/-- PCG trace-cost accounting under preconditioner #1. -/
def pcgTraceCostPrecond1 (n r q : Nat) (tr : PCGTrace) : Nat :=
  precond1SetupCost n + kernelMulCost n r
    + tr.matVecCount * matVecCost n r q
    + tr.precondApplyCount * precond1ApplyCost n r

/-- PCG trace-cost accounting under preconditioner #2. -/
def pcgTraceCostPrecond2 (n r q : Nat) (tr : PCGTrace) : Nat :=
  precond2SetupCost n r + kernelMulCost n r
    + tr.matVecCount * matVecCost n r q
    + tr.precondApplyCount * precond2ApplyCost n r

theorem pcgRunTrace_costPrecond1_eq_model (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    pcgTraceCostPrecond1 n r q (pcgRunTrace P (precond1Apply P) x0 iters).2
      = pcgSolveCostPrecond1 iters n r q := by
  have hMat : (pcgRunTrace P (precond1Apply P) x0 iters).2.matVecCount = iters :=
    pcgRunTrace_matVecCount_eq (P := P) (Minv := precond1Apply P) (x0 := x0) (iters := iters)
  have hPre : (pcgRunTrace P (precond1Apply P) x0 iters).2.precondApplyCount = iters :=
    pcgRunTrace_precondApplyCount_eq (P := P) (Minv := precond1Apply P) (x0 := x0) (iters := iters)
  simp [pcgTraceCostPrecond1, pcgSolveCostPrecond1, hMat, hPre, Nat.mul_add,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem pcgRunTrace_costPrecond2_eq_model (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    pcgTraceCostPrecond2 n r q (pcgRunTrace P (precond2Apply P) x0 iters).2
      = pcgSolveCostPrecond2 iters n r q := by
  have hMat : (pcgRunTrace P (precond2Apply P) x0 iters).2.matVecCount = iters :=
    pcgRunTrace_matVecCount_eq (P := P) (Minv := precond2Apply P) (x0 := x0) (iters := iters)
  have hPre : (pcgRunTrace P (precond2Apply P) x0 iters).2.precondApplyCount = iters :=
    pcgRunTrace_precondApplyCount_eq (P := P) (Minv := precond2Apply P) (x0 := x0) (iters := iters)
  simp [pcgTraceCostPrecond2, pcgSolveCostPrecond2, hMat, hPre, Nat.mul_add,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem pcgRunTrace_costPrecond2_eq_model_via_plan (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat)
    (Rsample : Matrix (Fin n) (Fin r) Real) :
    pcgTraceCostPrecond2 n r q (pcgRunTrace P (precond2Apply P) x0 iters).2
      = precond2SetupCost n r + kernelMulCost n r
          + iters * (matVecCost n r q + precond2ApplyTraceCost n r (precond2ApplyPlan P Rsample).2) := by
  calc
    pcgTraceCostPrecond2 n r q (pcgRunTrace P (precond2Apply P) x0 iters).2
        = pcgSolveCostPrecond2 iters n r q :=
          pcgRunTrace_costPrecond2_eq_model (P := P) (x0 := x0) (iters := iters)
    _ = precond2SetupCost n r + kernelMulCost n r
          + iters * (matVecCost n r q + precond2ApplyCost n r) := rfl
    _ = precond2SetupCost n r + kernelMulCost n r
          + iters * (matVecCost n r q + precond2ApplyTraceCost n r (precond2ApplyPlan P Rsample).2) := by
          rw [precond2ApplyPlan_cost_eq_model (P := P) (R := Rsample)]


end
end Q10
end AutoProof
