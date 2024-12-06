import «MyProject».Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- Define vector space over ℝ
def Vector (n : ℕ) := Fin n → ℝ

-- Define vector addition
def vecAdd {n : ℕ} (u v : Vector n) : Vector n :=
  fun i => u i + v i

-- Define scalar multiplication
def scalarMul {n : ℕ} (a : ℝ) (v : Vector n) : Vector n :=
  fun i => a * v i

-- Define dot product
def dotProduct {n : ℕ} (u v : Vector n) : ℝ :=
  Finset.univ.sum (fun i => u i * v i)

-- Define norm of a vector
noncomputable def norm {n : ℕ} (v : Vector n) : ℝ :=
  Real.sqrt (dotProduct v v)

-- Auxiliary lemmas
-- Lemma: Dot product is commutative
lemma dotProduct_comm {n : ℕ} (u v : Vector n) :
  dotProduct u v = dotProduct v u := by
  simp [dotProduct, mul_comm]

-- Lemma: Dot product is distributive
lemma dotProduct_distrib {n : ℕ} (u v w : Vector n) :
  dotProduct (vecAdd u v) w = dotProduct u w + dotProduct v w := by
  simp [dotProduct, vecAdd]
  have : ∀ i, (u i + v i) * w i = u i * w i + v i * w i := by
    intro i
    ring
  simp [this]
  exact Finset.sum_add_distrib

-- Lemma: Dot product with scalar multiplication
lemma dotProduct_scalar {n : ℕ} (a : ℝ) (u v : Vector n) :
  dotProduct (scalarMul a u) v = a * dotProduct u v := by
  simp [dotProduct, scalarMul]
  rw [Finset.mul_sum]
  congr
  ext i
  simp [mul_assoc]

-- Lemma: Norm squared is non-negative
lemma norm_sq_nonneg {n : ℕ} (v : Vector n) :
  0 ≤ dotProduct v v := by
  simp [dotProduct]
  apply Finset.sum_nonneg
  intro i _
  apply mul_self_nonneg

-- Main theorem: Cauchy-Schwarz inequality
theorem cauchy_schwarz {n : ℕ} (u v : Vector n) :
  |dotProduct u v| ≤ norm u * norm v := by
  let a := dotProduct u v
  let b := dotProduct u u
  let c := dotProduct v v
  have h_nonneg : 0 ≤ b := norm_sq_nonneg u
  have h_c_nonneg : 0 ≤ c := norm_sq_nonneg v
  -- Use the inequality: b * c - a^2 ≥ 0
  suffices : b * c - a ^ 2 ≥ 0
  · rw [Real.abs_le_sqrt_mul_self_iff]
    sorry
    · rw [← Real.sqrt_mul h_nonneg h_c_nonneg]
      exact this
    · exact h_nonneg
    · exact h_c_nonneg
  -- Prove b * c - a^2 ≥ 0 by considering the norm of w = v - (a / b) * u
  let w := vecAdd v (scalarMul (-a / b) u)
  have h_w_norm_sq_nonneg : 0 ≤ dotProduct w w := norm_sq_nonneg w
  simp [w, vecAdd, scalarMul, dotProduct] at h_w_norm_sq_nonneg
  field_simp [h_nonneg] at h_w_norm_sq_nonneg
  ring_nf at h_w_norm_sq_nonneg
  -- Rearrange terms to show b * c - a^2 ≥ 0
  exact h_w_norm_sq_nonneg
  sorry
  -- going to work on this later.
  -- for part b I think I did alright.
