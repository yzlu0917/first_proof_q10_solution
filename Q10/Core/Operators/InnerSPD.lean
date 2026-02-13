import autoproof.Q10.Core.Operators.ProblemModel

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Frobenius inner product between two `n × r` matrices. -/
def frobInner (X Y : Matrix (Fin n) (Fin r) Real) : Real :=
  X.vec ⬝ᵥ Y.vec

theorem frobInner_zero_right (X : Matrix (Fin n) (Fin r) Real) :
    frobInner X 0 = 0 := by
  unfold frobInner
  simp

theorem frobInner_zero_left (Y : Matrix (Fin n) (Fin r) Real) :
    frobInner (0 : Matrix (Fin n) (Fin r) Real) Y = 0 := by
  unfold frobInner
  calc
    (0 : Matrix (Fin n) (Fin r) Real).vec ⬝ᵥ Y.vec
        = Y.vec ⬝ᵥ (0 : Matrix (Fin n) (Fin r) Real).vec := by
            simpa using dotProduct_comm ((0 : Matrix (Fin n) (Fin r) Real).vec) Y.vec
    _ = 0 := by simpa using (dotProduct_zero (v := Y.vec))

theorem frobInner_comm (X Y : Matrix (Fin n) (Fin r) Real) :
    frobInner X Y = frobInner Y X := by
  unfold frobInner
  simpa using dotProduct_comm X.vec Y.vec

theorem frobInner_add_left (X₁ X₂ Y : Matrix (Fin n) (Fin r) Real) :
    frobInner (X₁ + X₂) Y = frobInner X₁ Y + frobInner X₂ Y := by
  unfold frobInner
  simp [Matrix.vec_add, dotProduct_add]

theorem frobInner_add_right (X Y₁ Y₂ : Matrix (Fin n) (Fin r) Real) :
    frobInner X (Y₁ + Y₂) = frobInner X Y₁ + frobInner X Y₂ := by
  unfold frobInner
  simp [Matrix.vec_add, dotProduct_add]

theorem frobInner_sub_left (X₁ X₂ Y : Matrix (Fin n) (Fin r) Real) :
    frobInner (X₁ - X₂) Y = frobInner X₁ Y - frobInner X₂ Y := by
  unfold frobInner
  simp [Matrix.vec_sub, dotProduct_sub]

theorem frobInner_sub_right (X Y₁ Y₂ : Matrix (Fin n) (Fin r) Real) :
    frobInner X (Y₁ - Y₂) = frobInner X Y₁ - frobInner X Y₂ := by
  unfold frobInner
  simp [Matrix.vec_sub, dotProduct_sub]

theorem frobInner_smul_left (a : Real) (X Y : Matrix (Fin n) (Fin r) Real) :
    frobInner (a • X) Y = a * frobInner X Y := by
  unfold frobInner
  simp [Matrix.vec_smul, dotProduct_smul, mul_comm]

theorem frobInner_smul_right (a : Real) (X Y : Matrix (Fin n) (Fin r) Real) :
    frobInner X (a • Y) = a * frobInner X Y := by
  unfold frobInner
  simp [Matrix.vec_smul, dotProduct_smul, mul_comm]

theorem frobInner_applyA_comm (P : Problem n M r q)
    (X Y : Matrix (Fin n) (Fin r) Real) :
    frobInner X (applyA P Y) = frobInner Y (applyA P X) := by
  have hSwap :
      X.vec ⬝ᵥ ((denseMatrix P) *ᵥ Y.vec)
        = Y.vec ⬝ᵥ (((denseMatrix P)ᵀ) *ᵥ X.vec) := by
    calc
      X.vec ⬝ᵥ ((denseMatrix P) *ᵥ Y.vec)
          = Matrix.vecMul X.vec (denseMatrix P) ⬝ᵥ Y.vec := by
              simpa using Matrix.dotProduct_mulVec X.vec (denseMatrix P) Y.vec
      _ = (((denseMatrix P)ᵀ) *ᵥ X.vec) ⬝ᵥ Y.vec := by
            simpa using congrArg (fun v => v ⬝ᵥ Y.vec)
              (Matrix.vecMul_transpose (A := (denseMatrix P)ᵀ) (x := X.vec))
      _ = Y.vec ⬝ᵥ (((denseMatrix P)ᵀ) *ᵥ X.vec) := by
            simpa using dotProduct_comm (((denseMatrix P)ᵀ) *ᵥ X.vec) Y.vec
  unfold frobInner
  calc
    X.vec ⬝ᵥ (applyA P Y).vec
        = X.vec ⬝ᵥ ((denseMatrix P) *ᵥ Y.vec) := by simp [applyA_vec]
    _ = Y.vec ⬝ᵥ (((denseMatrix P)ᵀ) *ᵥ X.vec) := hSwap
    _ = Y.vec ⬝ᵥ ((denseMatrix P) *ᵥ X.vec) := by simp [denseMatrix_transpose]
    _ = Y.vec ⬝ᵥ (applyA P X).vec := by simp [applyA_vec]

theorem quadratic_minimizer_linear_term
    {d n a : Real} (hd : 0 < d) :
    ((n / d) ^ 2 * d - 2 * n * (n / d)) ≤ (a ^ 2 * d - 2 * n * a) := by
  have hsq : 0 ≤ d * (a - n / d) ^ 2 :=
    mul_nonneg (le_of_lt hd) (sq_nonneg (a - n / d))
  have hId :
      d * (a - n / d) ^ 2
        = (a ^ 2 * d - 2 * n * a)
          - (((n / d) ^ 2 * d - 2 * n * (n / d))) := by
    field_simp [hd.ne']
    ring
  nlinarith [hsq, hId]

/-- Operator-level SPD statement on matrix variables with Frobenius inner product. -/
def operatorSPD (P : Problem n M r q) : Prop :=
  ∀ X : Matrix (Fin n) (Fin r) Real, X ≠ 0 → 0 < frobInner X (applyA P X)

theorem operatorSPD_of_denseMatrix_posDef (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef) :
    operatorSPD P := by
  intro X hX
  have hXv : X.vec ≠ 0 := by
    intro h0
    exact hX (Matrix.vec_eq_zero_iff.mp h0)
  have hEq : (applyA P X).vec = denseMatrix P *ᵥ X.vec := by
    rw [show (applyA P X).vec = applyDenseVec P.K P.Z P.Ω P.lam X.vec by
      simpa [applyA] using
        (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
          (hK := P.hK) (W := X)).symm]
    rfl
  have hDot : 0 < star X.vec ⬝ᵥ (denseMatrix P *ᵥ X.vec) := hPos.dotProduct_mulVec_pos hXv
  unfold frobInner
  simpa [hEq] using hDot

theorem applyA_add (P : Problem n M r q)
    (W₁ W₂ : Matrix (Fin n) (Fin r) Real) :
    applyA P (W₁ + W₂) = applyA P W₁ + applyA P W₂ := by
  have h12 : (applyA P (W₁ + W₂)).vec = applyDenseVec P.K P.Z P.Ω P.lam (W₁ + W₂).vec := by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := W₁ + W₂)).symm
  have h1 : (applyA P W₁).vec = applyDenseVec P.K P.Z P.Ω P.lam W₁.vec := by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := W₁)).symm
  have h2 : (applyA P W₂).vec = applyDenseVec P.K P.Z P.Ω P.lam W₂.vec := by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := W₂)).symm
  apply (Matrix.vec_inj).1
  calc
    (applyA P (W₁ + W₂)).vec
        = applyDenseVec P.K P.Z P.Ω P.lam (W₁ + W₂).vec := h12
    _ = applyDenseVec P.K P.Z P.Ω P.lam (W₁.vec + W₂.vec) := by simp [Matrix.vec_add]
    _ = applyDenseVec P.K P.Z P.Ω P.lam W₁.vec + applyDenseVec P.K P.Z P.Ω P.lam W₂.vec := by
          unfold applyDenseVec
          simp [Matrix.mulVec_add]
    _ = (applyA P W₁).vec + (applyA P W₂).vec := by rw [← h1, ← h2]

theorem applyA_smul (P : Problem n M r q)
    (a : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyA P (a • W) = a • applyA P W := by
  have hAW : (applyA P W).vec = applyDenseVec P.K P.Z P.Ω P.lam W.vec := by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := W)).symm
  have hAS : (applyA P (a • W)).vec = applyDenseVec P.K P.Z P.Ω P.lam (a • W).vec := by
    simpa [applyA] using
      (applyDenseVec_eq_vec_applyMatrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
        (hK := P.hK) (W := a • W)).symm
  apply (Matrix.vec_inj).1
  calc
    (applyA P (a • W)).vec
        = applyDenseVec P.K P.Z P.Ω P.lam (a • W).vec := hAS
    _ = applyDenseVec P.K P.Z P.Ω P.lam (a • W.vec) := by simp [Matrix.vec_smul]
    _ = a • applyDenseVec P.K P.Z P.Ω P.lam W.vec := by
          unfold applyDenseVec
          simp [Matrix.mulVec_smul]
    _ = (a • applyA P W).vec := by
          simpa [Matrix.vec_smul] using (congrArg (a • ·) hAW).symm

theorem applyA_sub_smul (P : Problem n M r q)
    (e p : Matrix (Fin n) (Fin r) Real) (t : Real) :
    applyA P (e - t • p) = applyA P e - t • applyA P p := by
  calc
    applyA P (e - t • p)
        = applyA P (e + (-t) • p) := by simp [sub_eq_add_neg]
    _ = applyA P e + applyA P ((-t) • p) := by
          simpa using applyA_add (P := P) e ((-t) • p)
    _ = applyA P e + (-t) • applyA P p := by
          rw [applyA_smul (P := P) (-t) p]
    _ = applyA P e - t • applyA P p := by
          simp [sub_eq_add_neg]

theorem energy_along_search_expand (P : Problem n M r q)
    (e p : Matrix (Fin n) (Fin r) Real) (t : Real) :
    frobInner (e - t • p) (applyA P (e - t • p))
      = frobInner e (applyA P e)
          - t * frobInner e (applyA P p)
          - t * frobInner p (applyA P e)
          + t ^ 2 * frobInner p (applyA P p) := by
  rw [applyA_sub_smul (P := P) e p t]
  calc
    frobInner (e - t • p) (applyA P e - t • applyA P p)
        = frobInner e (applyA P e - t • applyA P p)
            - frobInner (t • p) (applyA P e - t • applyA P p) := by
              simpa using
                (frobInner_sub_left e (t • p) (applyA P e - t • applyA P p))
    _ = (frobInner e (applyA P e) - frobInner e (t • applyA P p))
          - (frobInner (t • p) (applyA P e) - frobInner (t • p) (t • applyA P p)) := by
            simp [frobInner_sub_right]
    _ = (frobInner e (applyA P e) - t * frobInner e (applyA P p))
          - (t * frobInner p (applyA P e) - t * (t * frobInner p (applyA P p))) := by
            simp [frobInner_smul_left, frobInner_smul_right, mul_assoc]
    _ = frobInner e (applyA P e)
          - t * frobInner e (applyA P p)
          - t * frobInner p (applyA P e)
          + t ^ 2 * frobInner p (applyA P p) := by
            ring

theorem energy_along_search_expand_symm (P : Problem n M r q)
    (e p : Matrix (Fin n) (Fin r) Real) (t : Real) :
    frobInner (e - t • p) (applyA P (e - t • p))
      = frobInner e (applyA P e)
          - 2 * t * frobInner e (applyA P p)
          + t ^ 2 * frobInner p (applyA P p) := by
  calc
    frobInner (e - t • p) (applyA P (e - t • p))
        = frobInner e (applyA P e)
            - t * frobInner e (applyA P p)
            - t * frobInner p (applyA P e)
            + t ^ 2 * frobInner p (applyA P p) :=
          energy_along_search_expand (P := P) e p t
    _ = frobInner e (applyA P e)
          - t * frobInner e (applyA P p)
          - t * frobInner e (applyA P p)
          + t ^ 2 * frobInner p (applyA P p) := by
            rw [frobInner_applyA_comm (P := P) p e]
    _ = frobInner e (applyA P e)
          - 2 * t * frobInner e (applyA P p)
          + t ^ 2 * frobInner p (applyA P p) := by ring


end
end Q10
end AutoProof
