import Mathlib

open scoped BigOperators Matrix

namespace RidgeRegression

def sqNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  ∑ i, (v i)^2

private theorem sqNorm_eq_dot {k : ℕ} (v : Fin k → ℝ) :
    sqNorm v = v ⬝ᵥ v := by
  simp only [sqNorm, dotProduct, pow_two]

private theorem sqNorm_add {k : ℕ} (u v : Fin k → ℝ) :
    sqNorm (u + v) = sqNorm u + sqNorm v + 2 * (u ⬝ᵥ v) := by
  simp only [sqNorm_eq_dot, dotProduct_add, add_dotProduct]
  rw [dotProduct_comm v u]
  ring

private theorem sqNorm_sub {k : ℕ} (u v : Fin k → ℝ) :
    sqNorm (u - v) = sqNorm u + sqNorm v - 2 * (u ⬝ᵥ v) := by
  simp only [sqNorm_eq_dot, dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm v u]
  ring

end RidgeRegression

open RidgeRegression

/-- Squared residuals plus the L2 penalty. -/
def ridgeLoss {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (beta : Fin p → ℝ) : ℝ :=
  sqNorm (y - X.mulVec beta) + lam * sqNorm beta

namespace RidgeRegression

/-- The constant diagonal matrix is lambda times the identity. -/
def normalMatrix {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  X.transpose * X + Matrix.diagonal (fun _ : Fin p => lam)

theorem normalMatrix_posDef {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (lam : ℝ) (hlam : 0 < lam) : (normalMatrix X lam).PosDef := by
  have htranspose : X.conjTranspose = X.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hgram : (X.transpose * X).PosSemidef := by
    simpa only [htranspose] using Matrix.posSemidef_conjTranspose_mul_self X
  have hdiag : (Matrix.diagonal (fun _ : Fin p => lam)).PosDef :=
    Matrix.PosDef.diagonal (fun _ => hlam)
  exact hdiag.posSemidef_add hgram

theorem normalMatrix_invertible {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (lam : ℝ) (hlam : 0 < lam) :
    normalMatrix X lam * (normalMatrix X lam)⁻¹ = 1 := by
  have hunit : IsUnit (normalMatrix X lam) :=
    (normalMatrix_posDef X lam hlam).isUnit
  exact Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

private theorem normalMatrix_mulVec {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (lam : ℝ) (v : Fin p → ℝ) :
    (normalMatrix X lam).mulVec v =
      X.transpose.mulVec (X.mulVec v) + lam • v := by
  rw [normalMatrix, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.diagonal_const_mulVec]

theorem normalMatrix_quadratic {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (lam : ℝ) (v : Fin p → ℝ) :
    v ⬝ᵥ (normalMatrix X lam).mulVec v =
      sqNorm (X.mulVec v) + lam * sqNorm v := by
  rw [normalMatrix_mulVec, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec,
    dotProduct_smul, sqNorm_eq_dot, sqNorm_eq_dot]
  simp only [smul_eq_mul]

theorem normalMatrix_quadratic_pos {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (lam : ℝ) (hlam : 0 < lam) (v : Fin p → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (normalMatrix X lam).mulVec v := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp
    (normalMatrix_posDef X lam hlam)).2 hv
  have hstar : star v = v := by
    funext i
    change star (v i) = v i
    simp
  simpa only [hstar] using hpos

theorem exists_normal_solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    ∃ b, (normalMatrix X lam).mulVec b = X.transpose.mulVec y := by
  refine ⟨((normalMatrix X lam)⁻¹).mulVec (X.transpose.mulVec y), ?_⟩
  rw [Matrix.mulVec_mulVec, normalMatrix_invertible X lam hlam,
    Matrix.one_mulVec]

theorem loss_sub_eq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (b beta : Fin p → ℝ)
    (hb : (normalMatrix X lam).mulVec b = X.transpose.mulVec y) :
    ridgeLoss X y lam beta - ridgeLoss X y lam b =
      sqNorm (X.mulVec (beta - b)) + lam * sqNorm (beta - b) := by
  let d := beta - b
  have hbeta : beta = b + d := by
    dsimp [d]
    abel
  let r := y - X.mulVec b
  have hresidual : y - X.mulVec beta = r - X.mulVec d := by
    rw [hbeta, Matrix.mulVec_add]
    dsimp [r]
    abel
  have hresidual_normal : X.transpose.mulVec r = lam • b := by
    rw [normalMatrix_mulVec] at hb
    change X.transpose.mulVec (y - X.mulVec b) = lam • b
    rw [Matrix.mulVec_sub, ← hb]
    abel
  have hcross : r ⬝ᵥ X.mulVec d = lam * (b ⬝ᵥ d) := by
    rw [← Matrix.dotProduct_transpose_mulVec,
      hresidual_normal, dotProduct_smul,
      dotProduct_comm d b]
    simp only [smul_eq_mul]
  change sqNorm (y - X.mulVec beta) + lam * sqNorm beta -
    (sqNorm r + lam * sqNorm b) =
      sqNorm (X.mulVec d) + lam * sqNorm d
  rw [hresidual, sqNorm_sub, hcross]
  have hpenalty := congrArg sqNorm hbeta
  rw [sqNorm_add] at hpenalty
  rw [hpenalty]
  ring

theorem loss_lt_of_ne {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (b beta : Fin p → ℝ)
    (hb : (normalMatrix X lam).mulVec b = X.transpose.mulVec y)
    (hne : beta ≠ b) :
    ridgeLoss X y lam b < ridgeLoss X y lam beta := by
  have hd : beta - b ≠ 0 := sub_ne_zero.mpr hne
  have hp := normalMatrix_quadratic_pos X lam hlam (beta - b) hd
  rw [normalMatrix_quadratic, ← loss_sub_eq X y lam b beta hb] at hp
  exact sub_pos.mp hp

end RidgeRegression

theorem ridge_unique_minimizer {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    ∃! beta_hat : Fin p → ℝ,
      ∀ beta : Fin p → ℝ,
        ridgeLoss X y lam beta_hat ≤ ridgeLoss X y lam beta := by
  obtain ⟨b, hb⟩ := exists_normal_solution X y lam hlam
  refine ⟨b, ?_, ?_⟩
  · intro beta
    by_cases h : beta = b
    · subst beta
      exact le_rfl
    · exact (loss_lt_of_ne X y lam hlam b beta hb h).le
  · intro beta hmin
    by_contra h
    exact (not_lt_of_ge (hmin b))
      (loss_lt_of_ne X y lam hlam b beta hb h)

#print axioms ridge_unique_minimizer
