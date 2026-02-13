import autoproof.Q10.Core.Operators.ObservedOps

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Input data of a single q10 mode-`k` linear subproblem. -/
structure Problem (n M r q : Nat) where
  K : Matrix (Fin n) (Fin n) Real
  Z : Matrix (Fin M) (Fin r) Real
  Ω : Fin q → Fin M × Fin n
  lam : Real
  B : Matrix (Fin n) (Fin r) Real
  hK : Kᵀ = K

/-- `q10.tex` problem object with selector semantics baked in:
`Ω` is injective, equivalent to `SᵀS = I_q` for `S = selectionMatrix Ω`. -/
structure TexProblem (n M r q : Nat) extends Problem n M r q where
  hOmegaInj : Function.Injective Ω

/-- `q10.tex` object with observed-value semantics wired in:
`B` is not free; it is fixed by observed sparse MTTKRP `sparseMTTKRP Ω vals Z`. -/
structure TexObservedProblem (n M r q : Nat) extends TexProblem n M r q where
  vals : Fin q → Real
  hBobs : B = sparseMTTKRP Ω vals Z

/-- Kernel-shifted q10 object (`K + νI`) for PSD→SPD regularization. -/
def TexObservedProblem.withKernelShift
    (P : TexObservedProblem n M r q) (nu : Real) :
    TexObservedProblem n M r q where
  K := P.K + nu • (1 : Matrix (Fin n) (Fin n) Real)
  Z := P.Z
  Ω := P.Ω
  lam := P.lam
  B := P.B
  hK := by
    calc
      (P.K + nu • (1 : Matrix (Fin n) (Fin n) Real))ᵀ
          = P.Kᵀ + (nu • (1 : Matrix (Fin n) (Fin n) Real))ᵀ := by
              simp
      _ = P.K + nu • (1 : Matrix (Fin n) (Fin n) Real) := by
            simp [P.hK]
  hOmegaInj := P.hOmegaInj
  vals := P.vals
  hBobs := P.hBobs

@[simp] theorem TexObservedProblem.withKernelShift_Z
    (P : TexObservedProblem n M r q) (nu : Real) :
    (P.withKernelShift nu).Z = P.Z := rfl

@[simp] theorem TexObservedProblem.withKernelShift_Ω
    (P : TexObservedProblem n M r q) (nu : Real) :
    (P.withKernelShift nu).Ω = P.Ω := rfl

@[simp] theorem TexObservedProblem.withKernelShift_vals
    (P : TexObservedProblem n M r q) (nu : Real) :
    (P.withKernelShift nu).vals = P.vals := rfl

@[simp] theorem TexObservedProblem.withKernelShift_lam
    (P : TexObservedProblem n M r q) (nu : Real) :
    (P.withKernelShift nu).lam = P.lam := rfl

@[simp] theorem TexObservedProblem.withKernelShift_B
    (P : TexObservedProblem n M r q) (nu : Real) :
    (P.withKernelShift nu).B = P.B := rfl

theorem TexProblem.selection_subidentity (P : TexProblem n M r q) :
    (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real) := by
  exact selectionMatrix_transpose_mul_self_eq_one_of_injective (Ω := P.Ω) P.hOmegaInj

theorem TexProblem.selection_subidentity_iff (P : TexProblem n M r q) :
    (selectionMatrix P.Ω)ᵀ * selectionMatrix P.Ω = (1 : Matrix (Fin q) (Fin q) Real)
      ↔ Function.Injective P.Ω := by
  exact selectionMatrix_transpose_mul_self_eq_one_iff_injective (Ω := P.Ω)

theorem rhsVec_eq_rhsFromObserved_of_eq_sparseMTTKRP
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (B : Matrix (Fin n) (Fin r) Real)
    (hB : B = sparseMTTKRP Ω vals Z) :
    rhsVec K B = rhsFromObserved K Ω vals Z := by
  subst hB
  simp [rhsVec, rhsFromObserved]

theorem TexObservedProblem.rhsVec_eq_rhsFromObserved
    (P : TexObservedProblem n M r q) :
    rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z := by
  exact rhsVec_eq_rhsFromObserved_of_eq_sparseMTTKRP
    (K := P.K) (Ω := P.Ω) (vals := P.vals) (Z := P.Z) (B := P.B) (hB := P.hBobs)

/-- Dense system matrix `A` from q10. -/
def denseMatrix (P : Problem n M r q) : Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  ((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K))
    + P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)

theorem denseMatrix_transpose (P : Problem n M r q) :
    (denseMatrix P)ᵀ = denseMatrix P := by
  unfold denseMatrix
  have hKronT :
      (((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)ᵀ
        = ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) := by
    calc
      (((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)ᵀ)
          = ((1 : Matrix (Fin r) (Fin r) Real)ᵀ ⊗ₖ P.Kᵀ) := by
              simpa using
                (Matrix.kroneckerMap_transpose
                  (f := fun x y : Real => x * y)
                  (A := (1 : Matrix (Fin r) (Fin r) Real))
                  (B := P.K)).symm
      _ = ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K) := by
            simp [P.hK]
  simp [Matrix.mul_assoc, hKronT]

/-- Convert a vectorized unknown back to matrix form (`vec` inverse). -/
def unvec (x : Fin r × Fin n → Real) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i j => x (j, i)

@[simp]
theorem vec_unvec (x : Fin r × Fin n → Real) : (unvec x).vec = x := by
  ext ij
  rcases ij with ⟨j, i⟩
  rfl

theorem isHermitian_smul_real {m : Type} {A : Matrix m m Real}
    (hA : A.IsHermitian) (a : Real) :
    (a • A).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_smul]
  simpa using congrArg (fun M => a • M) hA.eq

theorem posDef_smul_real {m : Type} [Fintype m] {A : Matrix m m Real}
    (hA : A.PosDef) {a : Real} (ha : 0 < a) :
    (a • A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_smul_real hA.1 a) ?_
  intro x hx
  have hAx : 0 < star x ⬝ᵥ (A *ᵥ x) := hA.dotProduct_mulVec_pos hx
  have hmul : star x ⬝ᵥ ((a • A) *ᵥ x) = a * (star x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp [smul_eq_mul]
  rw [hmul]
  exact mul_pos ha hAx

theorem one_posDef_fin : (1 : Matrix (Fin r) (Fin r) Real).PosDef := by
  have hdiag : (1 : Matrix (Fin r) (Fin r) Real) = Matrix.diagonal (fun _ => (1 : Real)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [hdiag]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  norm_num

/-- PSD kernel becomes SPD after a positive nugget shift. -/
theorem kernel_shift_posDef_of_posSemidef
    (K : Matrix (Fin n) (Fin n) Real)
    (hKpsd : K.PosSemidef)
    {nu : Real} (hNu : 0 < nu) :
    (K + nu • (1 : Matrix (Fin n) (Fin n) Real)).PosDef := by
  have hIdPos : (1 : Matrix (Fin n) (Fin n) Real).PosDef := one_posDef_fin (r := n)
  have hNuIdPos : (nu • (1 : Matrix (Fin n) (Fin n) Real)).PosDef :=
    posDef_smul_real hIdPos hNu
  exact Matrix.PosDef.posSemidef_add hKpsd hNuIdPos

theorem TexObservedProblem.withKernelShift_posDef_of_posSemidef
    (P : TexObservedProblem n M r q)
    (hKpsd : P.K.PosSemidef)
    {nu : Real} (hNu : 0 < nu) :
    (P.withKernelShift nu).K.PosDef := by
  simpa [TexObservedProblem.withKernelShift] using
    kernel_shift_posDef_of_posSemidef (K := P.K) hKpsd (hNu := hNu)

theorem denseMatrix_posDef (P : Problem n M r q)
    (hlam : 0 < P.lam) (hKpos : P.K.PosDef) :
    (denseMatrix P).PosDef := by
  have hData : (((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K))).PosSemidef := by
    let B : Matrix (Fin q) (Fin r × Fin n) Real := (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K)
    have hB : Bᵀ * B = ((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K)) := by
      simp [B, Matrix.mul_assoc]
    rw [← hB]
    simpa [conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self B
  have hKronPos : (((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)).PosDef := by
    exact Matrix.PosDef.kronecker one_posDef_fin hKpos
  have hRegPos : (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)).PosDef :=
    posDef_smul_real hKronPos hlam
  unfold denseMatrix
  exact hRegPos.posSemidef_add hData

theorem denseMatrix_posSemidef (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef) :
    (denseMatrix P).PosSemidef := by
  have hData : (((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K))).PosSemidef := by
    let B : Matrix (Fin q) (Fin r × Fin n) Real := (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K)
    have hB : Bᵀ * B = ((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K)) := by
      simp [B, Matrix.mul_assoc]
    rw [← hB]
    simpa [conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self B
  have hKron : (((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)).PosSemidef := by
    exact ((one_posDef_fin (r := r)).posSemidef).kronecker hKpsd
  have hReg : (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)).PosSemidef :=
    hKron.smul hLam
  unfold denseMatrix
  exact hData.add hReg

theorem denseMatrix_not_posDef_of_kernel_nullvec
    (P : Problem n M r q)
    (hr : 0 < r)
    {v : Fin n → Real}
    (hv : v ≠ 0)
    (hKv : P.K *ᵥ v = 0) :
    ¬ (denseMatrix P).PosDef := by
  intro hPos
  rcases dense_operator_has_nontrivial_kernel_of_kernel_nullvec
      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (hK := P.hK)
      (hr := hr) (hv := hv) (hKv := hKv) with ⟨x, hxne, hAx0⟩
  have hPosx : 0 < star x ⬝ᵥ (denseMatrix P *ᵥ x) := hPos.dotProduct_mulVec_pos hxne
  have hmul : denseMatrix P *ᵥ x = 0 := by
    simpa [applyDenseVec, denseMatrix] using hAx0
  have : 0 < (0 : Real) := by
    simpa [hmul] using hPosx
  linarith

theorem denseMatrix_isUnit (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    IsUnit (denseMatrix P) :=
  (denseMatrix_posDef (P := P) hLam hKpos).isUnit

theorem denseMatrix_det_isUnit (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    IsUnit (denseMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det (denseMatrix P)).mp
    (denseMatrix_isUnit (P := P) hLam hKpos)

theorem denseMatrix_mulVec_injective (P : Problem n M r q)
    (hInv : IsUnit (denseMatrix P).det) :
    Function.Injective (fun x : Fin r × Fin n → Real => denseMatrix P *ᵥ x) := by
  intro x y hxy
  have hleft := congrArg (fun v => (denseMatrix P)⁻¹ *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (A := denseMatrix P) hInv, Matrix.one_mulVec]
    using hleft

theorem dense_equation_unique_vec (P : Problem n M r q)
    (hInv : IsUnit (denseMatrix P).det)
    {x y : Fin r × Fin n → Real}
    (hx : denseMatrix P *ᵥ x = rhsVec P.K P.B)
    (hy : denseMatrix P *ᵥ y = rhsVec P.K P.B) :
    x = y := by
  exact denseMatrix_mulVec_injective (P := P) hInv (hx.trans hy.symm)

theorem dense_equation_unique (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    {W₁ W₂ : Matrix (Fin n) (Fin r) Real}
    (hW₁ : applyDenseVec P.K P.Z P.Ω P.lam W₁.vec = rhsVec P.K P.B)
    (hW₂ : applyDenseVec P.K P.Z P.Ω P.lam W₂.vec = rhsVec P.K P.B) :
    W₁ = W₂ := by
  have hInv : IsUnit (denseMatrix P).det := denseMatrix_det_isUnit (P := P) hLam hKpos
  have hvec : W₁.vec = W₂.vec := dense_equation_unique_vec (P := P) (hInv := hInv)
    (by simpa [applyDenseVec, denseMatrix] using hW₁)
    (by simpa [applyDenseVec, denseMatrix] using hW₂)
  exact (Matrix.vec_inj).1 hvec

/-- Dense residual in vectorized coordinates. -/
def denseResidual (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) : Fin r × Fin n → Real :=
  applyDenseVec P.K P.Z P.Ω P.lam W.vec - rhsVec P.K P.B

/-- Matrix-free residual in matrix coordinates. -/
def matrixFreeResidual (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real :=
  applyMatrixFree P.K P.Z P.Ω P.lam W - P.K * P.B

/-- Sparse matrix-free residual using explicit `q`-indexed formulas. -/
def matrixFreeResidualSparse (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real :=
  applyMatrixFreeSparse P.K P.Z P.Ω P.lam W - P.K * P.B

theorem matrixFreeResidualSparse_eq_matrixFreeResidual
    (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    matrixFreeResidualSparse P W = matrixFreeResidual P W := by
  simp [matrixFreeResidualSparse, matrixFreeResidual, applyMatrixFreeSparse_eq_applyMatrixFree]

/-- Residual zero condition is equivalent in dense and matrix-free representations. -/
theorem denseResidual_eq_zero_iff_matrixFreeResidual_eq_zero
    (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    denseResidual P W = 0 ↔ matrixFreeResidual P W = 0 := by
  unfold denseResidual matrixFreeResidual
  rw [sub_eq_zero, sub_eq_zero]
  simpa [P.hK] using
    (q10_system_equiv_matrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
      (hK := P.hK) (W := W) (B := P.B))

/-- Matrix-form right-hand side of q10. -/
def rhsMat (P : Problem n M r q) : Matrix (Fin n) (Fin r) Real :=
  P.K * P.B

/-- Matrix-form operator of q10 (matrix-free implementation). -/
def applyA (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real :=
  applyMatrixFree P.K P.Z P.Ω P.lam W

/-- Matrix-form operator of q10 via explicit sparse formulas. -/
def applyASparse (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    Matrix (Fin n) (Fin r) Real :=
  applyMatrixFreeSparse P.K P.Z P.Ω P.lam W

theorem applyASparse_eq_applyA (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    applyASparse P W = applyA P W := by
  exact applyMatrixFreeSparse_eq_applyMatrixFree
    (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)

theorem applyA_vec (P : Problem n M r q) (W : Matrix (Fin n) (Fin r) Real) :
    (applyA P W).vec = denseMatrix P *ᵥ W.vec := by
  rw [show (applyA P W).vec = applyDenseVec P.K P.Z P.Ω P.lam W.vec by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := W)).symm]
  rfl


end
end Q10
end AutoProof
