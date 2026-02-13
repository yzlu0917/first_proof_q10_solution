import autoproof.Q10.Core.Preconditioners.BaseDefs

set_option autoImplicit false

open scoped BigOperators Kronecker MatrixOrder
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Quadratic-form Loewner preorder used in this file:
`A ⪯q B` iff `xᵀAx ≤ xᵀBx` for all vectors `x`. -/
def QuadraticLe {m : Type*} [Fintype m]
    (A B : Matrix m m Real) : Prop :=
  ∀ x : m → Real, star x ⬝ᵥ (A *ᵥ x) ≤ star x ⬝ᵥ (B *ᵥ x)

section MatrixOrderBridge

open scoped MatrixOrder

theorem quadraticLe_of_matrixLe
    {m : Type*} [Fintype m]
    (A B : Matrix m m Real)
    (hAB : A ≤ B) :
    QuadraticLe A B := by
  intro x
  have hPSD : (B - A).PosSemidef := (Matrix.le_iff).1 hAB
  have hNonneg : 0 ≤ star x ⬝ᵥ ((B - A) *ᵥ x) :=
    hPSD.dotProduct_mulVec_nonneg x
  have hExpand :
      star x ⬝ᵥ ((B - A) *ᵥ x)
        = star x ⬝ᵥ (B *ᵥ x) - star x ⬝ᵥ (A *ᵥ x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  linarith [hNonneg, hExpand]

theorem eigenvalue_le_trace_of_posSemidef
    (K : Matrix (Fin n) (Fin n) Real)
    (hK : K.PosSemidef) (i : Fin n) :
    hK.1.eigenvalues i ≤ K.trace := by
  classical
  have htrace : K.trace = ∑ j : Fin n, hK.1.eigenvalues j :=
    hK.1.trace_eq_sum_eigenvalues
  rw [htrace]
  have hle : hK.1.eigenvalues i ≤ ∑ j : Fin n, hK.1.eigenvalues j := by
    exact Finset.single_le_sum (fun j _ => hK.eigenvalues_nonneg j) (Finset.mem_univ i)
  simpa using hle

theorem spectrum_elem_le_trace_of_posSemidef
    (K : Matrix (Fin n) (Fin n) Real)
    (hK : K.PosSemidef)
    {x : Real} (hx : x ∈ spectrum Real K) :
    x ≤ K.trace := by
  classical
  have hxImage : x ∈ (RCLike.ofReal '' Set.range hK.1.eigenvalues) := by
    simpa [hK.1.spectrum_eq_image_range] using hx
  rcases hxImage with ⟨x0, ⟨i, rfl⟩, hx0eq⟩
  have hxEq : x = hK.1.eigenvalues i := by
    simpa using hx0eq.symm
  rw [hxEq]
  exact eigenvalue_le_trace_of_posSemidef K hK i

/-- Automatic Gram Loewner envelope used by the preconditioner comparison:
`gramMatrix ≤ (trace(gramMatrix)+1) I`. -/
theorem gramMatrix_le_tracePlusOne_smul_one
    (P : Problem n M r q) :
    gramMatrix P ≤ ((gramMatrix P).trace + 1) • (1 : Matrix (Fin r) (Fin r) Real) := by
  let G : Matrix (Fin r) (Fin r) Real := gramMatrix P
  have hG : G.PosSemidef := by
    simpa [G] using gramMatrix_posSemidef (P := P)
  have hpt :
      cfc (R := Real) id G ≤ cfc (fun _ : Real => (G.trace + 1)) G := by
    rw [cfc_le_iff (f := id) (g := fun _ : Real => (G.trace + 1)) (a := G)]
    intro x hx
    have hxnonneg : 0 ≤ x := spectrum_nonneg_of_nonneg (a := G) hG.nonneg (x := x) hx
    have hxletrace : x ≤ G.trace := spectrum_elem_le_trace_of_posSemidef (K := G) hG hx
    have hxletrace1 : x ≤ G.trace + 1 := by nlinarith
    simpa using hxletrace1
  have hleft : cfc (R := Real) id G = G := by
    simpa using (cfc_id (R := Real) (a := G))
  have hright : cfc (fun _ : Real => (G.trace + 1)) G
      = (G.trace + 1) • (1 : Matrix (Fin r) (Fin r) Real) := by
    calc
      cfc (fun _ : Real => (G.trace + 1)) G
          = algebraMap Real (Matrix (Fin r) (Fin r) Real) (G.trace + 1) := by
              simpa using (cfc_const (R := Real) (r := (G.trace + 1)) (a := G))
      _ = (G.trace + 1) • (1 : Matrix (Fin r) (Fin r) Real) := by
            simp [Algebra.smul_def]
  have hLe : G ≤ (G.trace + 1) • (1 : Matrix (Fin r) (Fin r) Real) := by
    simpa [hleft, hright] using hpt
  simpa [G] using hLe

theorem kernel_square_sub_nonneg_of_posSemidef
    (K : Matrix (Fin n) (Fin n) Real)
    (hK : K.PosSemidef) :
    ((K.trace + 1) • K - K ^ 2).PosSemidef := by
  classical
  have hpt : cfc (fun t : Real => t ^ 2) K ≤ cfc (fun t : Real => (K.trace + 1) * t) K := by
    rw [cfc_le_iff (f := fun t : Real => t ^ 2) (g := fun t : Real => (K.trace + 1) * t) (a := K)]
    intro x hx
    have hxnonneg : 0 ≤ x := spectrum_nonneg_of_nonneg (a := K) hK.nonneg (x := x) hx
    have hxletrace : x ≤ K.trace := spectrum_elem_le_trace_of_posSemidef K hK hx
    nlinarith
  have hleft : cfc (fun t : Real => t ^ 2) K = K ^ 2 := by
    simpa using (cfc_pow_id (R := Real) (a := K) 2)
  have hconst : cfc (fun _ : Real => (K.trace + 1)) K
      = algebraMap Real (Matrix (Fin n) (Fin n) Real) (K.trace + 1) := by
    simpa using (cfc_const (R := Real) (r := (K.trace + 1)) (a := K))
  have hid : cfc (R := Real) id K = K := by
    simpa using (cfc_id (R := Real) (a := K))
  have hright : cfc (fun t : Real => (K.trace + 1) * t) K = (K.trace + 1) • K := by
    calc
      cfc (fun t : Real => (K.trace + 1) * t) K
          = cfc (fun _ : Real => (K.trace + 1)) K * cfc (R := Real) id K := by
              simpa [id_eq] using
                (cfc_mul (f := fun _ : Real => (K.trace + 1)) (g := id) (a := K))
      _ = (algebraMap Real (Matrix (Fin n) (Fin n) Real) (K.trace + 1)) * K := by
            rw [hconst, hid]
      _ = (K.trace + 1) • K := by
            simpa [Algebra.smul_def]
  have hpow : K ^ 2 ≤ (K.trace + 1) • K := by
    simpa [hleft, hright] using hpt
  exact (Matrix.le_iff).1 hpow

theorem kernel_square_le_tracePlusOne_smul_of_posSemidef
    (K : Matrix (Fin n) (Fin n) Real)
    (hK : K.PosSemidef) :
    Kᵀ * K ≤ (K.trace + 1) • K := by
  have hPowLe : K ^ 2 ≤ (K.trace + 1) • K := (Matrix.le_iff).2
    (kernel_square_sub_nonneg_of_posSemidef (K := K) hK)
  have hSym : Kᵀ = K := hK.isHermitian.eq
  simpa [pow_two, hSym] using hPowLe

theorem kron_right_mono_of_left_posSemidef
    (A : Matrix (Fin r) (Fin r) Real)
    (hA : A.PosSemidef)
    {B C : Matrix (Fin n) (Fin n) Real}
    (hBC : B ≤ C) :
    (A ⊗ₖ B) ≤ (A ⊗ₖ C) := by
  have hDiff : (C - B).PosSemidef := (Matrix.le_iff).1 hBC
  have hKronDiff : (A ⊗ₖ (C - B)).PosSemidef := hA.kronecker hDiff
  have hEq : ((A ⊗ₖ C) - (A ⊗ₖ B)) = A ⊗ₖ (C - B) := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    simp [Matrix.kronecker, sub_eq_add_neg, add_mul, mul_add]
  refine (Matrix.le_iff).2 ?_
  simpa [hEq] using hKronDiff

theorem kron_left_mono_of_right_posSemidef
    (C : Matrix (Fin n) (Fin n) Real)
    (hC : C.PosSemidef)
    {A B : Matrix (Fin r) (Fin r) Real}
    (hAB : A ≤ B) :
    (A ⊗ₖ C) ≤ (B ⊗ₖ C) := by
  have hDiff : (B - A).PosSemidef := (Matrix.le_iff).1 hAB
  have hKronDiff : ((B - A) ⊗ₖ C).PosSemidef := hDiff.kronecker hC
  have hEq : ((B ⊗ₖ C) - (A ⊗ₖ C)) = (B - A) ⊗ₖ C := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    simp [Matrix.kronecker, sub_eq_add_neg, add_mul, mul_add]
  refine (Matrix.le_iff).2 ?_
  simpa [hEq] using hKronDiff

end MatrixOrderBridge

theorem quadratic_form_congr_compose
    {a b : Type*} [Fintype a] [Fintype b]
    (B : Matrix a b Real) (C : Matrix a a Real) (x : b → Real) :
    star x ⬝ᵥ ((Bᵀ * C * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (C *ᵥ (B *ᵥ x)) := by
  calc
    star x ⬝ᵥ ((Bᵀ * C * B) *ᵥ x)
        = (star x) ᵥ* (Bᵀ * (C * B)) ⬝ᵥ x := by
            simp [dotProduct_mulVec, Matrix.mul_assoc]
    _ = x ᵥ* (Bᵀ * (C * B)) ⬝ᵥ x := by simp
    _ = (B *ᵥ x) ᵥ* (C * B) ⬝ᵥ x := by
          congr 1
          simpa using (Matrix.vecMul_mulVec (A := B) (B := C * B) (x := x)).symm
    _ = star (B *ᵥ x) ⬝ᵥ (C *ᵥ (B *ᵥ x)) := by
          simp [dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem quadraticLe_congr_compose
    {a b : Type*} [Fintype a] [Fintype b]
    (B : Matrix a b Real) {C D : Matrix a a Real}
    (hCD : QuadraticLe C D) :
    QuadraticLe (Bᵀ * C * B) (Bᵀ * D * B) := by
  intro x
  have h := hCD (B *ᵥ x)
  calc
    star x ⬝ᵥ ((Bᵀ * C * B) *ᵥ x)
        = star (B *ᵥ x) ⬝ᵥ (C *ᵥ (B *ᵥ x)) :=
          quadratic_form_congr_compose (B := B) (C := C) (x := x)
    _ ≤ star (B *ᵥ x) ⬝ᵥ (D *ᵥ (B *ᵥ x)) := h
    _ = star x ⬝ᵥ ((Bᵀ * D * B) *ᵥ x) :=
          (quadratic_form_congr_compose (B := B) (C := D) (x := x)).symm

theorem selection_projector_quadratic_le_one_of_injective
    (Ω : Fin q → Fin M × Fin n)
    (hΩinj : Function.Injective Ω) :
    QuadraticLe ((selectionMatrix Ω) * (selectionMatrix Ω)ᵀ)
      (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) := by
  intro y
  classical
  have hComp : ∀ t : Fin q, ((selectionMatrix Ω)ᵀ *ᵥ y) t = y (Ω t) := by
    intro t
    simp [selectionMatrix, Matrix.mulVec, dotProduct]
  have hLeft :
      star y ⬝ᵥ (((selectionMatrix Ω) * (selectionMatrix Ω)ᵀ) *ᵥ y)
        = ∑ t : Fin q, (y (Ω t)) ^ 2 := by
    calc
      star y ⬝ᵥ (((selectionMatrix Ω) * (selectionMatrix Ω)ᵀ) *ᵥ y)
          = star y ⬝ᵥ (selectionMatrix Ω *ᵥ ((selectionMatrix Ω)ᵀ *ᵥ y)) := by
              simp [Matrix.mulVec_mulVec]
      _ = (star y ᵥ* selectionMatrix Ω) ⬝ᵥ ((selectionMatrix Ω)ᵀ *ᵥ y) := by
            simpa [dotProduct_mulVec]
      _ = star ((selectionMatrix Ω)ᵀ *ᵥ y) ⬝ᵥ ((selectionMatrix Ω)ᵀ *ᵥ y) := by
            have hMulT : (selectionMatrix Ω)ᵀ *ᵥ y = y ᵥ* selectionMatrix Ω := by
              simpa using Matrix.mulVec_transpose (A := selectionMatrix Ω) (x := y)
            have hStarMul : star y ᵥ* selectionMatrix Ω = (selectionMatrix Ω)ᵀ *ᵥ y := by
              simpa [hMulT]
            have hMulT' : y ᵥ* selectionMatrix Ω = (selectionMatrix Ω)ᵀ *ᵥ y := by
              simpa using hMulT.symm
            simpa [hStarMul, hMulT']
      _ = ∑ t : Fin q, (y (Ω t)) ^ 2 := by
            simp [dotProduct, hComp, pow_two]
  have hImage :
      (∑ t : Fin q, (y (Ω t)) ^ 2)
        = Finset.sum (Finset.univ.image Ω) (fun ij => (y ij) ^ 2) := by
    symm
    refine Finset.sum_image ?_
    intro a _ b _ hab
    exact hΩinj hab
  have hSubset :
      (Finset.univ.image Ω : Finset (Fin M × Fin n))
        ⊆ (Finset.univ : Finset (Fin M × Fin n)) := by
    intro ij hij
    simp
  have hSubLe :
      Finset.sum (Finset.univ.image Ω) (fun ij => (y ij) ^ 2)
        ≤ Finset.sum (Finset.univ : Finset (Fin M × Fin n)) (fun ij => (y ij) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hSubset (by
      intro ij hij hnot
      nlinarith)
  calc
    star y ⬝ᵥ (((selectionMatrix Ω) * (selectionMatrix Ω)ᵀ) *ᵥ y)
        = ∑ t : Fin q, (y (Ω t)) ^ 2 := hLeft
    _ = Finset.sum (Finset.univ.image Ω) (fun ij => (y ij) ^ 2) := hImage
    _ ≤ Finset.sum (Finset.univ : Finset (Fin M × Fin n)) (fun ij => (y ij) ^ 2) := hSubLe
    _ = star y ⬝ᵥ ((1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) *ᵥ y) := by
          simp [dotProduct, pow_two]

theorem dense_dataTerm_quadratic_upper_from_projection
    (P : Problem n M r q)
    (hProj : QuadraticLe ((selectionMatrix P.Ω) * (selectionMatrix P.Ω)ᵀ)
      (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real)) :
    QuadraticLe (denseDataTerm P)
      (((P.Z ⊗ₖ P.K)ᵀ) * (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) * (P.Z ⊗ₖ P.K)) := by
  have hQ := quadraticLe_congr_compose
    (B := (P.Z ⊗ₖ P.K))
    (C := (selectionMatrix P.Ω) * (selectionMatrix P.Ω)ᵀ)
    (D := (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real))
    hProj
  intro x
  simpa [denseDataTerm, Matrix.mul_assoc] using hQ x

theorem kron_self_transpose_mul_self
    (P : Problem n M r q) :
    ((P.Z ⊗ₖ P.K)ᵀ * (P.Z ⊗ₖ P.K)) = (P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K) := by
  have hT : (P.Z ⊗ₖ P.K)ᵀ = P.Zᵀ ⊗ₖ P.Kᵀ := by
    simpa [Matrix.kronecker] using
      (Matrix.kroneckerMap_transpose (f := (· * ·)) P.Z P.K).symm
  calc
    ((P.Z ⊗ₖ P.K)ᵀ * (P.Z ⊗ₖ P.K))
        = (P.Zᵀ ⊗ₖ P.Kᵀ) * (P.Z ⊗ₖ P.K) := by simpa [hT]
    _ = (P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K) := by
          simpa using (Matrix.mul_kronecker_mul P.Zᵀ P.Z P.Kᵀ P.K).symm

open scoped MatrixOrder

theorem dense_data_upper_from_injective_and_kernel_square_le
    (P : Problem n M r q)
    {c : Real}
    (hΩinj : Function.Injective P.Ω)
    (hKKle : P.Kᵀ * P.K ≤ c • P.K) :
    ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P *ᵥ x)
        ≤ c * (star x ⬝ᵥ (precond2Extra P *ᵥ x)) := by
  have hProj : QuadraticLe ((selectionMatrix P.Ω) * (selectionMatrix P.Ω)ᵀ)
      (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) :=
    selection_projector_quadratic_le_one_of_injective (Ω := P.Ω) hΩinj
  have hDataUpperQ := dense_dataTerm_quadratic_upper_from_projection (P := P) hProj
  have hGramPSD : (P.Zᵀ * P.Z).PosSemidef := by
    simpa [gramMatrix] using gramMatrix_posSemidef (P := P)
  have hKronLe :
      ((P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K))
        ≤ ((P.Zᵀ * P.Z) ⊗ₖ (c • P.K)) :=
    kron_right_mono_of_left_posSemidef
      (A := (P.Zᵀ * P.Z)) hGramPSD hKKle
  have hKronEq :
      ((P.Zᵀ * P.Z) ⊗ₖ (c • P.K)) = c • precond2Extra P := by
    calc
      ((P.Zᵀ * P.Z) ⊗ₖ (c • P.K))
          = c • ((P.Zᵀ * P.Z) ⊗ₖ P.K) := by
            simpa using (Matrix.kronecker_smul (r := c) (A := (P.Zᵀ * P.Z)) (B := P.K))
      _ = c • precond2Extra P := by simp [precond2Extra, gramMatrix]
  have hKronQ :
      QuadraticLe ((P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K))
        (c • precond2Extra P) :=
    quadraticLe_of_matrixLe
      (A := ((P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K)))
      (B := c • precond2Extra P)
      (le_trans hKronLe (le_of_eq hKronEq))
  have hRightEq :
      (((P.Z ⊗ₖ P.K)ᵀ) * (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) * (P.Z ⊗ₖ P.K))
        = (P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K) := by
    calc
      (((P.Z ⊗ₖ P.K)ᵀ) * (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) * (P.Z ⊗ₖ P.K))
          = ((P.Z ⊗ₖ P.K)ᵀ * (P.Z ⊗ₖ P.K)) := by simp [Matrix.mul_assoc]
      _ = (P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K) := kron_self_transpose_mul_self (P := P)
  have hRightEq' :
      ((P.Z ⊗ₖ P.K)ᵀ * (P.Z ⊗ₖ P.K))
        = (P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K) := by
    simpa [Matrix.mul_assoc] using hRightEq
  intro x
  calc
    star x ⬝ᵥ (denseDataTerm P *ᵥ x)
        ≤ star x ⬝ᵥ
            ((((P.Z ⊗ₖ P.K)ᵀ) * (1 : Matrix (Fin M × Fin n) (Fin M × Fin n) Real) * (P.Z ⊗ₖ P.K))
              *ᵥ x) := hDataUpperQ x
    _ = star x ⬝ᵥ (((P.Zᵀ * P.Z) ⊗ₖ (P.Kᵀ * P.K)) *ᵥ x) := by
          simpa [Matrix.mul_assoc, hRightEq']
    _ ≤ star x ⬝ᵥ ((c • precond2Extra P) *ᵥ x) := hKronQ x
    _ = c * (star x ⬝ᵥ (precond2Extra P *ᵥ x)) := by
          simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem dense_data_upper_from_injective_and_kernel_psd
    (P : Problem n M r q)
    (hΩinj : Function.Injective P.Ω)
    (hKpsd : P.K.PosSemidef) :
    ∀ x : Fin r × Fin n → Real,
      star x ⬝ᵥ (denseDataTerm P *ᵥ x)
        ≤ (P.K.trace + 1) * (star x ⬝ᵥ (precond2Extra P *ᵥ x)) := by
  exact dense_data_upper_from_injective_and_kernel_square_le
    (P := P) (c := P.K.trace + 1) (hΩinj := hΩinj)
    (hKKle := kernel_square_le_tracePlusOne_smul_of_posSemidef (K := P.K) hKpsd)

theorem denseDataTerm_posSemidef (P : Problem n M r q) :
    (denseDataTerm P).PosSemidef := by
  let B : Matrix (Fin q) (Fin r × Fin n) Real := (selectionMatrix P.Ω)ᵀ * (P.Z ⊗ₖ P.K)
  have hB : Bᵀ * B = denseDataTerm P := by
    simp [B, denseDataTerm, Matrix.mul_assoc]
  rw [← hB]
  simpa [conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self B

theorem denseMatrix_decompose (P : Problem n M r q) :
    denseMatrix P = denseDataTerm P + precond1Matrix P := by
  unfold denseMatrix denseDataTerm precond1Matrix defaultPreconditioner
  rfl

theorem denseMatrix_sub_precond1Matrix_posSemidef (P : Problem n M r q) :
    (denseMatrix P - precond1Matrix P).PosSemidef := by
  have hEq : denseMatrix P - precond1Matrix P = denseDataTerm P := by
    calc
      denseMatrix P - precond1Matrix P
          = (denseDataTerm P + precond1Matrix P) - precond1Matrix P := by
              rw [denseMatrix_decompose]
      _ = denseDataTerm P := by
            simpa [add_comm] using add_sub_cancel (denseDataTerm P) (precond1Matrix P)
  rw [hEq]
  exact denseDataTerm_posSemidef (P := P)

theorem dense_quadratic_dominates_precond1 (P : Problem n M r q)
    (x : Fin r × Fin n → Real) :
    star x ⬝ᵥ (precond1Matrix P *ᵥ x) ≤ star x ⬝ᵥ (denseMatrix P *ᵥ x) := by
  have hPSD : (denseMatrix P - precond1Matrix P).PosSemidef :=
    denseMatrix_sub_precond1Matrix_posSemidef (P := P)
  have hNonneg : 0 ≤ star x ⬝ᵥ ((denseMatrix P - precond1Matrix P) *ᵥ x) :=
    hPSD.dotProduct_mulVec_nonneg x
  have hExpand :
      star x ⬝ᵥ ((denseMatrix P - precond1Matrix P) *ᵥ x)
        = star x ⬝ᵥ (denseMatrix P *ᵥ x) - star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  linarith [hNonneg, hExpand]

theorem defaultPreconditioner_posDef (P : Problem n M r q)
    (hKpos : P.K.PosDef) :
    (defaultPreconditioner P).PosDef := by
  unfold defaultPreconditioner
  exact Matrix.PosDef.kronecker one_posDef_fin hKpos

theorem regularizerPreconditioner_posDef (P : Problem n M r q)
    (hLam : 0 < P.lam) (hKpos : P.K.PosDef) :
    (P.lam • defaultPreconditioner P).PosDef := by
  exact posDef_smul_real (defaultPreconditioner_posDef (P := P) hKpos) hLam

theorem regularizerPreconditioner_posSemidef (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef) :
    (P.lam • defaultPreconditioner P).PosSemidef := by
  unfold defaultPreconditioner
  exact (((one_posDef_fin (r := r)).posSemidef).kronecker hKpsd).smul hLam

theorem precond2Extra_posSemidef (P : Problem n M r q)
    (hKpsd : P.K.PosSemidef) :
    (precond2Extra P).PosSemidef := by
  unfold precond2Extra
  exact (gramMatrix_posSemidef (P := P)).kronecker hKpsd

theorem precond2Matrix_decompose (P : Problem n M r q) :
    precond2Matrix P = precond2Extra P + precond1Matrix P := by
  unfold precond2Matrix precond2Extra precond1Matrix defaultPreconditioner gramMatrix
  rw [Matrix.add_kronecker]
  rw [Matrix.smul_kronecker]

theorem precond2Matrix_posSemidef (P : Problem n M r q)
    (hLam : 0 ≤ P.lam) (hKpsd : P.K.PosSemidef) :
    (precond2Matrix P).PosSemidef := by
  rw [precond2Matrix_decompose]
  exact (precond2Extra_posSemidef (P := P) hKpsd).add
    (by simpa [precond1Matrix] using
      regularizerPreconditioner_posSemidef (P := P) hLam hKpsd)

theorem precond2Matrix_sub_precond1Matrix_posSemidef (P : Problem n M r q)
    (hKpsd : P.K.PosSemidef) :
    (precond2Matrix P - precond1Matrix P).PosSemidef := by
  have hEq : precond2Matrix P - precond1Matrix P = precond2Extra P := by
    calc
      precond2Matrix P - precond1Matrix P
          = (precond2Extra P + precond1Matrix P) - precond1Matrix P := by
              rw [precond2Matrix_decompose]
      _ = precond2Extra P := by
            simpa [add_comm] using add_sub_cancel (precond2Extra P) (precond1Matrix P)
  rw [hEq]
  exact precond2Extra_posSemidef (P := P) hKpsd

theorem precond2_quadratic_dominates_precond1 (P : Problem n M r q)
    (hKpsd : P.K.PosSemidef)
    (x : Fin r × Fin n → Real) :
    star x ⬝ᵥ (precond1Matrix P *ᵥ x) ≤ star x ⬝ᵥ (precond2Matrix P *ᵥ x) := by
  have hPSD : (precond2Matrix P - precond1Matrix P).PosSemidef :=
    precond2Matrix_sub_precond1Matrix_posSemidef (P := P) hKpsd
  have hNonneg : 0 ≤ star x ⬝ᵥ ((precond2Matrix P - precond1Matrix P) *ᵥ x) :=
    hPSD.dotProduct_mulVec_nonneg x
  have hExpand :
      star x ⬝ᵥ ((precond2Matrix P - precond1Matrix P) *ᵥ x)
        = star x ⬝ᵥ (precond2Matrix P *ᵥ x) - star x ⬝ᵥ (precond1Matrix P *ᵥ x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  linarith [hNonneg, hExpand]

open scoped MatrixOrder


end
end Q10
end AutoProof
