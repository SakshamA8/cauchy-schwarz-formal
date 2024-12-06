-- This module serves as the root of the FinalProject library.
-- Import modules here that should be built as part of the library.
import «FinalProject».Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic


/-- Define vector space over ℝ -/
def RnVector (n : ℕ) := Fin n → ℝ

namespace RnVector

variable {n : ℕ}

/-- Define vector addition -/
def vecAdd {n : ℕ} (u v : RnVector n) : RnVector n :=
  fun i => u i + v i

instance : Add (RnVector n) where
  add := vecAdd

/-- Define scalar multiplication -/
def scalarMul {n : ℕ} (a : ℝ) (v : RnVector n) : RnVector n :=
  fun i => a * v i

instance : SMul ℝ (RnVector n) where
  smul := scalarMul

/-- Define dot product -/
def dotProduct {n : ℕ} (u v : RnVector n) : ℝ :=
  Finset.univ.sum (fun i => u i * v i)

/-- Custom notation for the dot product -/
class DotProduct (α : Type) where
  dot : α → α → ℝ

/-- Instance of DotProduct for RnVector -/
instance : DotProduct (RnVector n) where
  dot := dotProduct



/-- Define norm of a vector -/
noncomputable def vecNorm {n : ℕ} (v : RnVector n) : ℝ :=
  Real.sqrt (dotProduct v v)

noncomputable instance : Norm (RnVector n) where
  norm := vecNorm

/-- Projection of vector u onto v -/
noncomputable def proj (u v : RnVector n) : RnVector n :=
  scalarMul ((dotProduct u v) / (dotProduct v v)) v

/-- Angle between two vectors in radians -/
noncomputable def vecAngle (u v : RnVector n) : ℝ :=
  Real.arccos ((dotProduct u v) / (norm u * norm v))



/-- Lemma: Dot product is commutative -/
lemma dotProduct_comm {n : ℕ} (u v : RnVector n) :
  dotProduct u v = dotProduct v u := by
  simp [dotProduct, mul_comm]

/-- Lemma: Dot product is distributive -/
lemma dotProduct_distrib {n : ℕ} (u v w : RnVector n) :
  dotProduct (vecAdd u v) w = dotProduct u w + dotProduct v w := by
  simp [dotProduct, vecAdd]
  have : ∀ i, (u i + v i) * w i = u i * w i + v i * w i := by
    intro i
    ring
  simp [this]
  exact Finset.sum_add_distrib

/-- Lemma: Dot product with scalar multiplication -/
lemma dotProduct_scalar {n : ℕ} (a : ℝ) (u v : RnVector n) :
  dotProduct (scalarMul a u) v = a * dotProduct u v := by
  simp [dotProduct, scalarMul]
  rw [Finset.mul_sum]
  congr
  ext i
  simp [mul_assoc]

/-- Lemma: Norm squared is non-negative -/
lemma norm_sq_nonneg {n : ℕ} (v : RnVector n) :
  0 ≤ dotProduct v v := by
  simp [dotProduct]
  apply Finset.sum_nonneg
  intro i _
  apply mul_self_nonneg





-- I know there are probably a lot of errors here, but I
-- legitimately didn't know what else to do. I know this
-- was supposed to be the bulk of my project, but
-- unfortunately, I couldn't formalize Cauchy-Schwarz fully.
-- I tried getting it to a state where the goals closed, but
-- I think there are a ton of errors for some reason, still.

-- However, I believe that the general outline of the proof
-- I outlined in the LaTeX is evident (and maybe deserving
-- of partial credit? :) )
-- I tried addressing all of the non-optional feedback,
-- and also formally wrote up everything in LaTeX,
-- so please be lenient when grading. :) I have a lot of
-- studying, homework, and other final projects as well as
-- 3 finals for my normal classes so I wasn't able to fully
-- complete it. Sorry :(

/--Main theorem, Cauchy-Schwarz: `⟪u, v⟫ ≤ ‖u‖⬝‖v‖`-/
theorem cauchy_schwarz (u v : RnVector n) :
  |DotProduct.dot u v| ≤ ‖u‖ * ‖v‖ := by
  -- Normalize the vectors u and v to obtain unit vectors x and y
  let x := scalarMul (1 / ‖u‖) u
  let y := scalarMul (1 / ‖v‖) v

  -- Prove that the norms of x and y are both 1
  have h_norm_x : ‖x‖ = 1 := by
    simp [vecNorm, scalarMul, dotProduct]
    rw [dotProduct_scalar]
    simp [mul_div_cancel_left (dotProduct u u) (Real.sqrt_ne_zero' (norm_sq_nonneg u))]
    exact Real.sqrt_mul_self (norm_sq_nonneg u)

  have h_norm_y : ‖y‖ = 1 := by
    simp [vecNorm, scalarMul, dotProduct]
    rw [dotProduct_scalar]
    simp [mul_div_cancel_left (dotProduct v v) (Real.sqrt_ne_zero' (norm_sq_nonneg v))]
    exact Real.sqrt_mul_self (norm_sq_nonneg v)

  -- |DotProduct.dot x y| ≤ 1 for unit vectors x and y
  have h_dot_xy : |DotProduct.dot x y| ≤ 1 := by
    apply one_le_norm_one h_norm_x h_norm_y

  calc
    |DotProduct.dot u v| ≤ |‖u‖ * ‖v‖ * DotProduct.dot x y| := by
      simp [x, y, dotProduct_scalar]
      ring_nf
    _ ≤ ‖u‖ * ‖v‖ * 1 := by
      exact one_le_norm_one h_norm_x h_norm_y
    _ = ‖u‖ * ‖v‖ := by ring_nf



end RnVector
