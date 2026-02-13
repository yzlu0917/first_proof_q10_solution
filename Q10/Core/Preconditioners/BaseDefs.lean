import autoproof.Q10.Core.KrylovAlgorithm.DefsAndPoly

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Preconditioner #1 from method: `M = λ(I ⊗ K)` in matrix form. -/
noncomputable def precond1Apply (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  (1 / P.lam) • (P.K⁻¹ * R)

/-- Linear-map realization of `precond1Apply`. -/
noncomputable def precond1ApplyLin (P : Problem n M r q) :
    Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real where
  toFun := precond1Apply P
  map_add' := by
    intro X Y
    simp [precond1Apply, Matrix.mul_add, smul_add]
  map_smul' := by
    intro a X
    simp [precond1Apply, Matrix.mul_smul, smul_smul, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem precond1ApplyLin_apply (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond1ApplyLin P R = precond1Apply P R := rfl

theorem precond1_correct (P : Problem n M r q)
    (hlam : P.lam ≠ 0) (hKinv : IsUnit P.K.det)
    (R : Matrix (Fin n) (Fin r) Real) :
    (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P R).vec = R.vec := by
  unfold precond1Apply
  rw [Matrix.smul_mulVec, Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.mul_smul, Matrix.vec_smul]
  simp [hlam]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv (A := P.K) hKinv, Matrix.one_mul]

theorem precond1_correct_of_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P R).vec = R.vec := by
  exact precond1_correct (P := P) (hlam := ne_of_gt hLam)
    (hKinv := (Matrix.isUnit_iff_isUnit_det P.K).mp hKpos.isUnit) R

/-- Gram matrix used in stronger preconditioner #2. -/
def gramMatrix (P : Problem n M r q) : Matrix (Fin r) (Fin r) Real :=
  P.Zᵀ * P.Z

theorem gramMatrix_posSemidef (P : Problem n M r q) :
    (gramMatrix P).PosSemidef := by
  simpa [gramMatrix, conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self P.Z

/-- If `Z` is represented as a Khatri-Rao row product after row reindexing by `e`,
then `gramMatrix P` equals the product-of-Grams formula over factors. -/
theorem gramMatrix_eq_gramFromFactors_of_khatriRao
    (P : Problem n M r q)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l) :
    gramMatrix P = gramFromFactors (r := r) A := by
  let ZKR : Matrix ((i : ι) → κ i) (Fin r) Real := khatriRaoPi (r := r) A
  have hZre : P.Z = reindexRows (r := r) e ZKR := by
    ext j l
    simp [reindexRows, ZKR, khatriRaoPi, hZ]
  calc
    gramMatrix P = P.Zᵀ * P.Z := rfl
    _ = (reindexRows (r := r) e ZKR)ᵀ * reindexRows (r := r) e ZKR := by
          simpa [hZre]
    _ = ZKRᵀ * ZKR := reindexRows_gram (r := r) (e := e) (Z := ZKR)
    _ = gramFromFactors (r := r) A := khatriRaoPi_gram (r := r) (A := A)

theorem regGram_posDef (P : Problem n M r q) (hLam : 0 < P.lam) :
    (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real)).PosDef := by
  exact (posDef_smul_real one_posDef_fin hLam).posSemidef_add (gramMatrix_posSemidef (P := P))

/-- Preconditioner #2 matrix (Kronecker-structured approximation). -/
def precond2Matrix (P : Problem n M r q) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real)) ⊗ₖ P.K

/-- Khatri-Rao Gram bridge for preconditioner #2:
when `Z` is generated from factor rows, `precond2Matrix` can be assembled from
small factor Gram matrices without explicit `M × r` materialization. -/
theorem precond2Matrix_eq_from_factor_grams
    (P : Problem n M r q)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (e : Fin M ≃ ((i : ι) → κ i))
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (hZ : ∀ j : Fin M, ∀ l : Fin r, P.Z j l = ∏ i, A i ((e j) i) l) :
    precond2Matrix P
      = (gramFromFactors (r := r) A + P.lam • (1 : Matrix (Fin r) (Fin r) Real)) ⊗ₖ P.K := by
  unfold precond2Matrix
  simp [gramMatrix_eq_gramFromFactors_of_khatriRao (P := P) (e := e) (A := A) (hZ := hZ)]

theorem precond2Matrix_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    (precond2Matrix P).PosDef := by
  unfold precond2Matrix
  exact Matrix.PosDef.kronecker (regGram_posDef (P := P) hLam) hKpos

/-- Exact inverse action for preconditioner #2 model matrix. -/
noncomputable def precond2Apply (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  unvec ((precond2Matrix P)⁻¹ *ᵥ R.vec)

/-- Linear-map realization of `precond2Apply`. -/
noncomputable def precond2ApplyLin (P : Problem n M r q) :
    Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real where
  toFun := precond2Apply P
  map_add' := by
    intro X Y
    apply (Matrix.vec_inj).1
    simp [precond2Apply, Matrix.mulVec_add, Matrix.vec_add, vec_unvec]
  map_smul' := by
    intro a X
    apply (Matrix.vec_inj).1
    simp [precond2Apply, Matrix.mulVec_smul, Matrix.vec_smul, vec_unvec]

@[simp] theorem precond2ApplyLin_apply (P : Problem n M r q)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2ApplyLin P R = precond2Apply P R := rfl

theorem precond2_dense_correct (P : Problem n M r q)
    (hInv : IsUnit (precond2Matrix P).det)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec := by
  unfold precond2Apply
  rw [vec_unvec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (A := precond2Matrix P) hInv,
    Matrix.one_mulVec]

theorem precond2_correct_of_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec := by
  exact precond2_dense_correct (P := P)
    (hInv := (Matrix.isUnit_iff_isUnit_det (precond2Matrix P)).mp
      (precond2Matrix_posDef (P := P) hLam hKpos).isUnit) R

theorem regGram_transpose (P : Problem n M r q) :
    (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))ᵀ
      = gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real) := by
  unfold gramMatrix
  simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul]

theorem precond2_apply_closed_form_spec (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2Matrix P *ᵥ
      ((P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹).vec)
      = R.vec := by
  let G : Matrix (Fin r) (Fin r) Real := gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real)
  have hKinv : IsUnit P.K.det := (Matrix.isUnit_iff_isUnit_det P.K).mp hKpos.isUnit
  have hGpos : G.PosDef := by
    simpa [G] using regGram_posDef (P := P) hLam
  have hGinv : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hGsymm : Gᵀ = G := by
    simpa [G] using regGram_transpose (P := P)
  unfold precond2Matrix
  change ((G ⊗ₖ P.K) *ᵥ (P.K⁻¹ * R * G⁻¹).vec) = R.vec
  rw [Matrix.kronecker_mulVec_vec, hGsymm]
  calc
    (P.K * (P.K⁻¹ * R * G⁻¹) * G).vec
        = ((P.K * P.K⁻¹) * R * (G⁻¹ * G)).vec := by
            simp [Matrix.mul_assoc]
    _ = (((1 : Matrix (Fin n) (Fin n) Real) * R) * (1 : Matrix (Fin r) (Fin r) Real)).vec := by
          simp [Matrix.mul_nonsing_inv (A := P.K) hKinv, Matrix.nonsing_inv_mul (A := G) hGinv]
    _ = R.vec := by simp [Matrix.mul_assoc]

theorem precond2Matrix_mulVec_injective (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    Function.Injective (fun x : Fin r × Fin n → Real => precond2Matrix P *ᵥ x) := by
  have hInv : IsUnit (precond2Matrix P).det := (Matrix.isUnit_iff_isUnit_det (precond2Matrix P)).mp
    (precond2Matrix_posDef (P := P) hLam hKpos).isUnit
  intro x y hxy
  have hleft := congrArg (fun v => (precond2Matrix P)⁻¹ *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (A := precond2Matrix P) hInv, Matrix.one_mulVec]
    using hleft

theorem precond2_apply_closed_form (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    precond2Apply P R
      = P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹ := by
  apply (Matrix.vec_inj).1
  have h1 : precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec :=
    precond2_correct_of_posDef (P := P) hLam hKpos R
  have h2 : precond2Matrix P *ᵥ
      ((P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹).vec)
        = R.vec :=
    precond2_apply_closed_form_spec (P := P) hLam hKpos R
  have hEq :
      precond2Matrix P *ᵥ (precond2Apply P R).vec
        = precond2Matrix P *ᵥ
          ((P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹).vec) := by
    calc
      precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec := h1
      _ = precond2Matrix P *ᵥ
          ((P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹).vec) := h2.symm
  exact precond2Matrix_mulVec_injective (P := P) hLam hKpos hEq

/-- Left-inverse reconstruction operator for preconditioner #1:
`M₁ * vec(X)` in matrix coordinates. -/
def precond1Undo (P : Problem n M r q)
    (X : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  unvec ((P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ X.vec)

/-- Left-inverse reconstruction operator for preconditioner #2:
`M₂ * vec(X)` in matrix coordinates. -/
def precond2Undo (P : Problem n M r q)
    (X : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  unvec (precond2Matrix P *ᵥ X.vec)

theorem precond1Undo_leftInverse_of_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    ∀ X : Matrix (Fin n) (Fin r) Real, precond1Undo P (precond1Apply P X) = X := by
  intro X
  apply (Matrix.vec_inj).1
  unfold precond1Undo
  simpa [vec_unvec] using
    precond1_correct_of_posDef (P := P) hLam hKpos X

theorem precond2Undo_leftInverse_of_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    ∀ X : Matrix (Fin n) (Fin r) Real, precond2Undo P (precond2Apply P X) = X := by
  intro X
  apply (Matrix.vec_inj).1
  unfold precond2Undo
  simpa [vec_unvec] using precond2_correct_of_posDef (P := P) hLam hKpos X

theorem precond1Undo_norm_le_of_bound (P : Problem n M r q)
    (c : Real)
    (hbound : ∀ v : Fin r × Fin n → Real,
      ‖(P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ v‖ ≤ c * ‖v‖)
    (X : Matrix (Fin n) (Fin r) Real) :
    ‖(precond1Undo P X).vec‖ ≤ c * ‖X.vec‖ := by
  unfold precond1Undo
  simpa [vec_unvec] using hbound X.vec

theorem precond2Undo_norm_le_of_bound (P : Problem n M r q)
    (c : Real)
    (hbound : ∀ v : Fin r × Fin n → Real, ‖precond2Matrix P *ᵥ v‖ ≤ c * ‖v‖)
    (X : Matrix (Fin n) (Fin r) Real) :
    ‖(precond2Undo P X).vec‖ ≤ c * ‖X.vec‖ := by
  unfold precond2Undo
  simpa [vec_unvec] using hbound X.vec

/-- Sup-norm matrix-vector bound via a global entrywise-absolute sum:
for finite index type `ι`, `‖A v‖∞ ≤ (∑ᵢ∑ⱼ |Aᵢⱼ|) ‖v‖∞`. -/
theorem matrix_mulVec_norm_le_sum_abs_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Real) (v : ι → Real) :
    ‖A *ᵥ v‖ ≤ (∑ i, ∑ j, |A i j|) * ‖v‖ := by
  let C : Real := (∑ i, ∑ j, |A i j|)
  have hcoord : ∀ i : ι, ‖(A *ᵥ v) i‖ ≤ C * ‖v‖ := by
    intro i
    have hcoordRow : ‖(A *ᵥ v) i‖ ≤ (∑ j, |A i j|) * ‖v‖ := by
      calc
        ‖(A *ᵥ v) i‖ = |∑ j, A i j * v j| := by
          simp [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
        _ ≤ ∑ j, |A i j * v j| := by
          simpa using (Finset.abs_sum_le_sum_abs (fun j => A i j * v j) Finset.univ)
        _ = ∑ j, (|A i j| * |v j|) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [abs_mul]
        _ ≤ ∑ j, (|A i j| * ‖v‖) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hvj : |v j| ≤ ‖v‖ := by
            have hvn : ‖v j‖₊ ≤ Finset.univ.sup (fun b => ‖v b‖₊) := by
              exact Finset.le_sup (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖₊) (by simp)
            have hv : ‖v j‖ ≤ ‖v‖ := by
              rw [Pi.norm_def]
              exact_mod_cast hvn
            simpa [Real.norm_eq_abs] using hv
          exact mul_le_mul_of_nonneg_left hvj (abs_nonneg (A i j))
        _ = (∑ j, |A i j|) * ‖v‖ := by
          simpa [Finset.sum_mul]
    have hle : (∑ j, |A i j|) ≤ C := by
      unfold C
      have hnonneg : ∀ i' ∈ (Finset.univ : Finset ι), 0 ≤ ∑ j, |A i' j| := by
        intro i' hi'
        exact Finset.sum_nonneg (by intro j hj; exact abs_nonneg (A i' j))
      have hiuniv : i ∈ (Finset.univ : Finset ι) := by simp
      simpa using Finset.single_le_sum hnonneg hiuniv
    exact le_trans hcoordRow (mul_le_mul_of_nonneg_right hle (norm_nonneg v))
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun b => ‖(A *ᵥ v) b‖₊) ≤ ⟨C * ‖v‖, by positivity⟩ := by
    refine Finset.sup_le ?_
    intro i hi
    exact_mod_cast hcoord i
  exact_mod_cast hnn

/-- Canonical sup-norm bound constant for `precond1Undo`. -/
def precond1UndoBoundConst (P : Problem n M r q) : Real :=
  ∑ i, ∑ j, |(P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) i j|

/-- Canonical sup-norm bound constant for `precond2Undo`. -/
def precond2UndoBoundConst (P : Problem n M r q) : Real :=
  ∑ i, ∑ j, |(precond2Matrix P) i j|

theorem precond1UndoBoundConst_nonneg (P : Problem n M r q) :
    0 ≤ precond1UndoBoundConst P := by
  unfold precond1UndoBoundConst
  exact Finset.sum_nonneg (by intro i hi; exact Finset.sum_nonneg (by intro j hj; positivity))

theorem precond2UndoBoundConst_nonneg (P : Problem n M r q) :
    0 ≤ precond2UndoBoundConst P := by
  unfold precond2UndoBoundConst
  exact Finset.sum_nonneg (by intro i hi; exact Finset.sum_nonneg (by intro j hj; positivity))

/-- Automatic sup-norm bound for `precond1Undo` using `precond1UndoBoundConst`. -/
theorem precond1Undo_norm_le_boundConst (P : Problem n M r q)
    (X : Matrix (Fin n) (Fin r) Real) :
    ‖(precond1Undo P X).vec‖ ≤ precond1UndoBoundConst P * ‖X.vec‖ := by
  apply precond1Undo_norm_le_of_bound (P := P) (c := precond1UndoBoundConst P)
  intro v
  simpa [precond1UndoBoundConst] using
    matrix_mulVec_norm_le_sum_abs_entries
      (A := P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) (v := v)

/-- Automatic sup-norm bound for `precond2Undo` using `precond2UndoBoundConst`. -/
theorem precond2Undo_norm_le_boundConst (P : Problem n M r q)
    (X : Matrix (Fin n) (Fin r) Real) :
    ‖(precond2Undo P X).vec‖ ≤ precond2UndoBoundConst P * ‖X.vec‖ := by
  apply precond2Undo_norm_le_of_bound (P := P) (c := precond2UndoBoundConst P)
  intro v
  simpa [precond2UndoBoundConst] using
    matrix_mulVec_norm_le_sum_abs_entries
      (A := precond2Matrix P) (v := v)

theorem precond1_apply_ne_zero_of_nonzero (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    {R : Matrix (Fin n) (Fin r) Real} (hR : R ≠ 0) :
    precond1Apply P R ≠ 0 := by
  intro hz
  have hzv : (precond1Apply P R).vec = 0 := Matrix.vec_eq_zero_iff.mpr hz
  have hEq : (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P R).vec = R.vec := by
    exact precond1_correct_of_posDef (P := P) hLam hKpos R
  have hRvec : R.vec = 0 := by
    calc
      R.vec = (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P R).vec := by
        simpa using hEq.symm
      _ = (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ 0 := by simp [hzv]
      _ = 0 := by simp
  exact hR (Matrix.vec_eq_zero_iff.mp hRvec)

theorem precond2_apply_ne_zero_of_nonzero (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    {R : Matrix (Fin n) (Fin r) Real} (hR : R ≠ 0) :
    precond2Apply P R ≠ 0 := by
  intro hz
  have hzv : (precond2Apply P R).vec = 0 := Matrix.vec_eq_zero_iff.mpr hz
  have hEq : precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec := by
    exact precond2_correct_of_posDef (P := P) hLam hKpos R
  have hRvec : R.vec = 0 := by
    calc
      R.vec = precond2Matrix P *ᵥ (precond2Apply P R).vec := by simpa using hEq.symm
      _ = precond2Matrix P *ᵥ 0 := by simp [hzv]
      _ = 0 := by simp
  exact hR (Matrix.vec_eq_zero_iff.mp hRvec)

theorem precond1_frobInner_pos_of_nonzero (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    {R : Matrix (Fin n) (Fin r) Real} (hR : R ≠ 0) :
    0 < frobInner R (precond1Apply P R) := by
  let M : Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
    P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)
  have hKronPos : (((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)).PosDef := by
    exact Matrix.PosDef.kronecker one_posDef_fin hKpos
  have hMpos : M.PosDef := by
    simpa [M] using posDef_smul_real hKronPos hLam
  have hEq : M *ᵥ (precond1Apply P R).vec = R.vec := by
    simpa [M] using precond1_correct_of_posDef (P := P) hLam hKpos R
  have hz : precond1Apply P R ≠ 0 :=
    precond1_apply_ne_zero_of_nonzero (P := P) hLam hKpos hR
  have hzv : (precond1Apply P R).vec ≠ 0 := by
    intro hzv0
    exact hz (Matrix.vec_eq_zero_iff.mp hzv0)
  have hQuad : 0 < star (precond1Apply P R).vec ⬝ᵥ (M *ᵥ (precond1Apply P R).vec) :=
    hMpos.dotProduct_mulVec_pos hzv
  unfold frobInner
  calc
    R.vec ⬝ᵥ (precond1Apply P R).vec
        = (M *ᵥ (precond1Apply P R).vec) ⬝ᵥ (precond1Apply P R).vec := by
            simpa [hEq]
    _ = star (precond1Apply P R).vec ⬝ᵥ (M *ᵥ (precond1Apply P R).vec) := by
          simpa using (dotProduct_comm (M *ᵥ (precond1Apply P R).vec) (precond1Apply P R).vec)
    _ > 0 := hQuad

theorem precond2_frobInner_pos_of_nonzero (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    {R : Matrix (Fin n) (Fin r) Real} (hR : R ≠ 0) :
    0 < frobInner R (precond2Apply P R) := by
  let M : Matrix (Fin r × Fin n) (Fin r × Fin n) Real := precond2Matrix P
  have hMpos : M.PosDef := by
    simpa [M] using precond2Matrix_posDef (P := P) hLam hKpos
  have hEq : M *ᵥ (precond2Apply P R).vec = R.vec := by
    simpa [M] using precond2_correct_of_posDef (P := P) hLam hKpos R
  have hz : precond2Apply P R ≠ 0 :=
    precond2_apply_ne_zero_of_nonzero (P := P) hLam hKpos hR
  have hzv : (precond2Apply P R).vec ≠ 0 := by
    intro hzv0
    exact hz (Matrix.vec_eq_zero_iff.mp hzv0)
  have hQuad : 0 < star (precond2Apply P R).vec ⬝ᵥ (M *ᵥ (precond2Apply P R).vec) :=
    hMpos.dotProduct_mulVec_pos hzv
  unfold frobInner
  calc
    R.vec ⬝ᵥ (precond2Apply P R).vec
        = (M *ᵥ (precond2Apply P R).vec) ⬝ᵥ (precond2Apply P R).vec := by
            simpa [hEq]
    _ = star (precond2Apply P R).vec ⬝ᵥ (M *ᵥ (precond2Apply P R).vec) := by
          simpa using (dotProduct_comm (M *ᵥ (precond2Apply P R).vec) (precond2Apply P R).vec)
    _ > 0 := hQuad

theorem pcgBeta_den_pos_of_precond1_state (P : Problem n M r q)
    (st : PCGState n r)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hz : st.z = precond1Apply P st.r)
    (hr : st.r ≠ 0) :
    0 < frobInner st.r st.z := by
  rw [hz]
  exact precond1_frobInner_pos_of_nonzero (P := P) hLam hKpos hr

theorem pcgBeta_den_pos_of_precond2_state (P : Problem n M r q)
    (st : PCGState n r)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hz : st.z = precond2Apply P st.r)
    (hr : st.r ≠ 0) :
    0 < frobInner st.r st.z := by
  rw [hz]
  exact precond2_frobInner_pos_of_nonzero (P := P) hLam hKpos hr

theorem pcgBeta_den_ne_zero_of_precond1_state (P : Problem n M r q)
    (st : PCGState n r)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hz : st.z = precond1Apply P st.r)
    (hr : st.r ≠ 0) :
    frobInner st.r st.z ≠ 0 :=
  ne_of_gt (pcgBeta_den_pos_of_precond1_state (P := P) (st := st) hLam hKpos hz hr)

theorem pcgBeta_den_ne_zero_of_precond2_state (P : Problem n M r q)
    (st : PCGState n r)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hz : st.z = precond2Apply P st.r)
    (hr : st.r ≠ 0) :
    frobInner st.r st.z ≠ 0 :=
  ne_of_gt (pcgBeta_den_pos_of_precond2_state (P := P) (st := st) hLam hKpos hz hr)

theorem pcgInit_beta_den_pos_precond1 (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hR0 : (pcgInit P (precond1Apply P) x0).r ≠ 0) :
    0 < frobInner (pcgInit P (precond1Apply P) x0).r (pcgInit P (precond1Apply P) x0).z := by
  have hz :
      (pcgInit P (precond1Apply P) x0).z =
        precond1Apply P ((pcgInit P (precond1Apply P) x0).r) := by
    simp [pcgInit]
  exact pcgBeta_den_pos_of_precond1_state (P := P)
    (st := pcgInit P (precond1Apply P) x0) hLam hKpos hz hR0

theorem pcgInit_beta_den_pos_precond2 (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hR0 : (pcgInit P (precond2Apply P) x0).r ≠ 0) :
    0 < frobInner (pcgInit P (precond2Apply P) x0).r (pcgInit P (precond2Apply P) x0).z := by
  have hz :
      (pcgInit P (precond2Apply P) x0).z =
        precond2Apply P ((pcgInit P (precond2Apply P) x0).r) := by
    simp [pcgInit]
  exact pcgBeta_den_pos_of_precond2_state (P := P)
    (st := pcgInit P (precond2Apply P) x0) hLam hKpos hz hR0

theorem pcgInit_alpha_den_pos_precond1 (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hR0 : (pcgInit P (precond1Apply P) x0).r ≠ 0) :
    0 < frobInner (pcgInit P (precond1Apply P) x0).p
      (pcgAp P (pcgInit P (precond1Apply P) x0)) := by
  let st0 : PCGState n r := pcgInit P (precond1Apply P) x0
  have hSPD : operatorSPD P := operatorSPD_of_denseMatrix_posDef (P := P)
    (denseMatrix_posDef (P := P) hLam hKpos)
  have hr0 : st0.r ≠ 0 := by simpa [st0] using hR0
  have hz0 : st0.z ≠ 0 := by
    have hzmain : precond1Apply P st0.r ≠ 0 :=
      precond1_apply_ne_zero_of_nonzero (P := P) hLam hKpos hr0
    simpa [st0, pcgInit] using hzmain
  have hp0 : st0.p ≠ 0 := by
    simpa [st0, pcgInit] using hz0
  have hDen : 0 < frobInner st0.p (pcgAp P st0) :=
    pcgAlpha_den_pos_of_operatorSPD (P := P) (st := st0) hSPD hp0
  simpa [st0] using hDen

theorem pcgInit_alpha_den_pos_precond2 (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef)
    (hR0 : (pcgInit P (precond2Apply P) x0).r ≠ 0) :
    0 < frobInner (pcgInit P (precond2Apply P) x0).p
      (pcgAp P (pcgInit P (precond2Apply P) x0)) := by
  let st0 : PCGState n r := pcgInit P (precond2Apply P) x0
  have hSPD : operatorSPD P := operatorSPD_of_denseMatrix_posDef (P := P)
    (denseMatrix_posDef (P := P) hLam hKpos)
  have hr0 : st0.r ≠ 0 := by simpa [st0] using hR0
  have hz0 : st0.z ≠ 0 := by
    have hzmain : precond2Apply P st0.r ≠ 0 :=
      precond2_apply_ne_zero_of_nonzero (P := P) hLam hKpos hr0
    simpa [st0, pcgInit] using hzmain
  have hp0 : st0.p ≠ 0 := by
    simpa [st0, pcgInit] using hz0
  have hDen : 0 < frobInner st0.p (pcgAp P st0) :=
    pcgAlpha_den_pos_of_operatorSPD (P := P) (st := st0) hSPD hp0
  simpa [st0] using hDen

/-- Ambient unfolding size `N = n * M`. -/
def ambientSize (n M : Nat) : Nat := n * M

/-- Data-fit part of the dense q10 operator:
`(Z ⊗ K)ᵀ S Sᵀ (Z ⊗ K)`. -/
def denseDataTerm (P : Problem n M r q) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  ((P.Z ⊗ₖ P.K)ᵀ * selectionMatrix P.Ω * (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K))

/-- Default q10 preconditioner: `I_r ⊗ K`. -/
def defaultPreconditioner (P : Problem n M r q) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  (1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K

/-- Preconditioner #1 model matrix: `λ (I_r ⊗ K)`. -/
def precond1Matrix (P : Problem n M r q) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  P.lam • defaultPreconditioner P

/-- Extra PSD term captured by preconditioner #2 beyond preconditioner #1. -/
def precond2Extra (P : Problem n M r q) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
  gramMatrix P ⊗ₖ P.K


end
end Q10
end AutoProof
