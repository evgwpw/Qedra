import Mathlib
open Real

-- qedra: леммы о rpow со степенью 1/2 (одинаковы во всех сертификатах)
macro "qedra_discharge" : tactic =>
  `(tactic| first | positivity | assumption | (apply ne_of_gt; assumption) | linarith)

private lemma qedra_rpow_half_mul (a : ℝ) (ha : 0 < a) : a ^ (1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add ha]
  norm_num

private lemma qedra_rpow_half_sq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

private lemma qedra_rpow_half_cube (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 3 = a * a ^ (1 / 2 : ℝ) := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, qedra_rpow_half_sq a ha]

private lemma qedra_rpow_half_neg (a : ℝ) (ha : 0 < a) : a ^ (-1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) / a := by
  rw [eq_div_iff (ne_of_gt ha)]
  calc a ^ (-1 / 2 : ℝ) * a = a ^ (-1 / 2 : ℝ) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = a ^ (-1 / 2 + 1 : ℝ) := by rw [Real.rpow_add ha]
    _ = a ^ (1 / 2 : ℝ) := by norm_num

-- одна и та же обратная степень приходит двумя формами: (a^(1/2))⁻¹ и a^(−1/2)
private lemma qedra_rpow_neg_half_inv (a : ℝ) (ha : 0 < a) : a ^ (-1 / 2 : ℝ) = (a ^ (1 / 2 : ℝ))⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt ha)]

-- qedra: integrate(1/(x*(x + 1)), x) -> log(x) - log(1 + x); conditions: []
theorem qedra_int_int_0034 (x : ℝ) (h1 : x ≠ 0) (h2 : (x + (1 : ℝ)) ≠ 0) (h3 : 0 < x) (h4 : 0 < ((1 : ℝ) + x)) :
    HasDerivAt (fun x : ℝ => (Real.log (x) + ((-1 : ℝ) * Real.log (((1 : ℝ) + x))))) (((1 : ℝ) / (x * (x + (1 : ℝ))))) x := by
  have h := ((Real.hasDerivAt_log h1)).add (((hasDerivAt_const (x := x) (c := (-1 : ℝ)))).mul (((Real.hasDerivAt_log (ne_of_gt h4))).comp x (((hasDerivAt_const (x := x) (c := (1 : ℝ)))).add ((hasDerivAt_id x)))))
  change HasDerivAt (fun x : ℝ => (Real.log (x) + ((-1 : ℝ) * Real.log (((1 : ℝ) + x))))) _ x at h
  convert h using 1
  try simp only [id_eq, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Real.sqrt_eq_rpow]
  try ring_nf at *
  try have hs := Real.sin_sq_add_cos_sq x
  all_goals first
    | (ring; done)
    | (ring_nf; done)
    | (ring_nf; ring; done)
    | (norm_num; done)
    | (nlinarith [Real.sin_sq_add_cos_sq x]; done)
    | (ring_nf; nlinarith [Real.sin_sq_add_cos_sq x]; done)
    | (linear_combination ((2 : ℝ) / 3 * Real.sin x) * hs; done)
    | (linear_combination ((2 : ℝ) / 3 * Real.cos x) * hs; done)
    | (simp only [mul_assoc, ← Real.rpow_add (by positivity)]; done)
    | (ring_nf; rw [← Real.rpow_add (by positivity)]; norm_num; ring; done)
    | (rw [← Real.rpow_neg (le_of_lt (by positivity))]; ring_nf; rw [← Real.rpow_add (by positivity)]; norm_num; ring; done)
    | (nth_rewrite 1 [← Real.rpow_one x]; rw [← Real.rpow_add (by positivity)]; norm_num; done)
    | (field_simp (discharger := positivity); ring; done)
    | (field_simp (discharger := nlinarith); ring; done)
    | (field_simp [h1, h2, h3, h4]; ring_nf; done)
    | (field_simp; ring_nf; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_cube, qedra_rpow_half_mul]; ring; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_mul]; ring; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_mul, qedra_rpow_half_sq]; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, ← sq, qedra_rpow_half_neg, qedra_rpow_half_sq]; field_simp (discharger := qedra_discharge); simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq]; ring; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_mul]; field_simp (discharger := qedra_discharge); ring; done)
    | (field_simp (discharger := qedra_discharge); nlinarith [Real.sin_sq_add_cos_sq x]; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring_nf; simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq, qedra_rpow_half_cube]; ring; done)
    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring_nf; simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq, qedra_rpow_half_cube]; done)
-- vacuous-check: int_0034 (x = 1)
example : ∃ x : ℝ, (x ≠ 0) ∧ ((x + (1 : ℝ)) ≠ 0) ∧ (0 < x) ∧ (0 < ((1 : ℝ) + x)) := by
  refine ⟨1, ?_, ?_, ?_, ?_⟩ <;> first
    | (norm_num; done)
    | (positivity; done)
    | (exact Real.log_pos (by norm_num); done)
    | (exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num); done)
    | (constructor <;> norm_num; done)

