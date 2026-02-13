import autoproof.Q10.TraceAndRates.RateTheory.Contraction
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false

open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Uniform bound of a polynomial on the spectral interval `[μ, L]`. -/
def IntervalPolyBound (mu L : Real) (p : Polynomial Real) (c : Real) : Prop :=
  ∀ x : Real, mu ≤ x → x ≤ L → |p.eval x| ≤ c

/-- Spectral-interval polynomial bound to matrix-operator bound (L2 operator norm):
for Hermitian `A`, if `|p(x)| ≤ c` on `spectrum(A) ⊆ [μ,L]`, then `‖p(A)‖ ≤ c`. -/
theorem matrix_aeval_opNorm_le_of_intervalSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Real) (hA : A.IsHermitian)
    (mu L c : Real)
    (hEigRange : spectrum ℝ A ⊆ Set.Icc mu L)
    (p : Polynomial Real)
    (hBound : IntervalPolyBound mu L p c)
    (hc : 0 ≤ c) :
    ‖Polynomial.aeval A p‖ ≤ c := by
  set D : Matrix ι ι Real :=
    Matrix.diagonal (RCLike.ofReal ∘ (fun x : ℝ => p.eval x) ∘ hA.eigenvalues : ι → ℝ) with hD
  have hdiagEntry :
      ∀ i : ι, ‖(RCLike.ofReal ((fun x : ℝ => p.eval x) (hA.eigenvalues i)) : ℝ)‖ ≤ c := by
    intro i
    have hxEig : hA.eigenvalues i ∈ spectrum ℝ A := by
      rw [hA.spectrum_real_eq_range_eigenvalues]
      exact Set.mem_range_self i
    have hxIcc : hA.eigenvalues i ∈ Set.Icc mu L := hEigRange hxEig
    simpa [Real.norm_eq_abs] using hBound (hA.eigenvalues i) hxIcc.1 hxIcc.2
  have hdiagNorm : ‖D‖ ≤ c := by
    rw [hD, Matrix.l2_opNorm_diagonal]
    rw [Pi.norm_def]
    have hs :
        (Finset.univ.sup fun i =>
          ‖(RCLike.ofReal ((fun x : ℝ => p.eval x) (hA.eigenvalues i)) : ℝ)‖₊)
          ≤ ⟨c, hc⟩ := by
      refine Finset.sup_le ?_
      intro i hi
      exact_mod_cast (hdiagEntry i)
    exact_mod_cast hs
  have hconj :
      ‖Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary D‖ = ‖D‖ := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    have h1 :
        ‖(hA.eigenvectorUnitary : Matrix ι ι ℝ) * (D * star (hA.eigenvectorUnitary : Matrix ι ι ℝ))‖
          = ‖D * star (hA.eigenvectorUnitary : Matrix ι ι ℝ)‖ :=
      CStarRing.norm_coe_unitary_mul hA.eigenvectorUnitary
        (D * star (hA.eigenvectorUnitary : Matrix ι ι ℝ))
    rw [h1]
    exact CStarRing.norm_mul_mem_unitary D (Unitary.star_mem hA.eigenvectorUnitary.prop)
  calc
    ‖Polynomial.aeval A p‖
        = ‖cfc (R := ℝ) (A := Matrix ι ι ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => p.eval x) A‖ := by
            simpa using congrArg norm
              ((cfc_polynomial (R := ℝ) (A := Matrix ι ι ℝ) (p := IsSelfAdjoint)
                (q := p) (a := A) (ha := hA)).symm)
    _ = ‖hA.cfc (fun x : ℝ => p.eval x)‖ := by rw [hA.cfc_eq (fun x : ℝ => p.eval x)]
    _ = ‖Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary D‖ := by
          simp [Matrix.IsHermitian.cfc, hD]
    _ = ‖D‖ := hconj
    _ ≤ c := hdiagNorm

/-- Coordinatewise-to-`L2` norm domination for finite vectors:
the ambient function-space norm is bounded by the `toLp 2` norm. -/
theorem vec_norm_le_toLp2_norm
    (v : Fin r × Fin n → Real) :
    ‖v‖ ≤ ‖WithLp.toLp 2 v‖ := by
  have hnn : ‖v‖₊ ≤ ‖WithLp.toLp 2 v‖₊ := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_le ?_
    intro i hi
    have hcoord :
        ‖v i‖ ≤ ‖WithLp.toLp 2 v‖ := by
      simpa [WithLp.ofLp_toLp] using
        (PiLp.norm_apply_le (x := (WithLp.toLp 2 v)) i)
    exact_mod_cast hcoord
  exact_mod_cast hnn

end
end Q10
end AutoProof
