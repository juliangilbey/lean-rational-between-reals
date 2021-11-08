import data.real.basic

section
universe u
variables {α : Type u} [ordered_add_comm_monoid α]

lemma nonneg_of_nonneg_le_smul {a b : α} {n : ℕ} :
  0 < a → a ≤ n • b → 0 < n :=
begin
  intros ha h,
  have hnb : 0 < n • b, by exact lt_of_lt_of_le ha h,
  have hn0 : 0 = n ∨ 0 < n, by exact eq_or_lt_of_le (zero_le n),
  cases hn0 with n0 n1,
    exfalso,
    rw [← n0, zero_smul] at hnb,
    exact (lt_irrefl 0) hnb,
  exact n1,
end

lemma nonneg_of_nonneg_lt_smul {a b : α} {n : ℕ} :
  0 < a → a < n • b → 0 < n :=
begin
  intros ha h,
  have h_le : a ≤ n • b, by exact le_of_lt h,
  exact nonneg_of_nonneg_le_smul ha h_le,
end

lemma arch_gt [archimedean α] [covariant_class α α (+) (<)] :
  ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x < n • y :=
begin
  introv ypos,
  obtain ⟨m, hm⟩ := archimedean.arch x ypos,
  use m + 1,
  rw [add_smul, one_smul],
  -- this should be easier...
  have hmy1 : m • y + 0 < m • y + y,
    apply (add_lt_add_left ypos (m • y)),
  simp at hmy1,
  exact lt_of_le_of_lt hm hmy1,
end

end section

lemma nat_pred_lt_of_pos { n : ℕ } (h : 0 < n) : nat.pred n < n :=
begin
  apply nat.pred_lt,
  intro h_n0,
  rw h_n0 at h,
  apply lt_irrefl 0,
  exact h,
end

lemma sub_one_lt_of_pos { n : ℕ } (h : 0 < n) : n - 1 < n :=
begin
  rw nat.sub_one n,
  exact nat_pred_lt_of_pos h,
end

lemma inv_nat_lt_pos_real (x : ℝ) (xpos : 0 < x) :
  ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) < x :=
begin
  -- by archimedean property of ℝ, there is some natural number n
  -- with n * x > 1, so 1 / n < x.
  obtain ⟨n, hn⟩ := arch_gt (1 : ℝ) xpos,
  have hn_gt_zero : 0 < n,
    exact nonneg_of_nonneg_lt_smul (@zero_lt_one ℝ _ _) hn,
  have hn_inv_lt_x : 1 / (n : ℝ) < x,
    simp at hn,
    have hn_gt_zero' : 0 < (n : ℝ),
      exact (@nat.cast_pos ℝ _ _ n).2 hn_gt_zero,
    apply (div_lt_iff' hn_gt_zero').2,
    assumption,
  use n,
  exact ⟨hn_gt_zero, hn_inv_lt_x⟩,
end

lemma rational_between_nonneg_reals (x y : ℝ) (h : x < y) (h_xnonneg: 0 ≤ x):
  ∃ r : ℚ, (x < r) ∧ (↑r < y) :=
begin
  -- By archimedean property of ℝ, there is some (positive)
  -- natural number n with n(y-x) > 1, so 1/n < y-x.
  have h_yx_positive : 0 < y - x, by simpa,
  cases (inv_nat_lt_pos_real (y - x) h_yx_positive) with n hn,

  -- Next, consider K = { k ∈ ℕ : k / n > x }.  By the archimedean
  -- property again, this set is non-empty.
  let p := λ k : ℕ, x < (k : ℝ) * (n : ℝ)⁻¹,
  let K := { k : ℕ // p k },
  have h_1n_positive : 0 < 1 / (n : ℝ), by { simp, exact hn.left },    
  obtain ⟨n0, hn0⟩ := arch_gt x h_1n_positive,
  simp at hn0,
  have hp : ∃ (m : ℕ), p m,
    use n0,
    exact hn0,
  -- Since K is non-empty, we can take its smallest element, k₀.
  -- have k0_x := nat.find_x hp,
  let k0 := nat.find hp, -- k0_x.val,
  -- there must be a better way to do the next two lines; surely
  -- we shouldn't need an explicit lemma to substitute for k0?
  have k0_def : k0 = nat.find hp,
    simp,
  have k0_spec := nat.find_spec hp,
  -- k₀/n is the rational we want
  use (k0 : ℚ) * (n : ℚ)⁻¹,

  split,
    -- the first main goal, x < k₀ / n, is true because k₀ satisfies p
    simp,
    rw k0_def,
    exact k0_spec,

  -- We show that k₀ / n < y by contradiction.  Assume that k₀ / n ≥ y.
  -- Then (k₀-1) / n ≥ y - 1/n > y - (y-x) = x, contradicting the
  -- minimality of k₀.

  -- We must first show that k₀ > 0, so that k₀ - 1 ∈ ℕ.
  simp,
  have k0_positive : k0 > 0,
    apply nat.pos_of_ne_zero,
    intro k0_zero,
    rw k0_def at k0_zero,
    rw k0_zero at k0_spec,
    have not_p_0 : ¬ p 0,
      have not_k_0 : ¬ x < 0 * (↑n)⁻¹,
        simpa,
      exact not_k_0,
    simpa,

  -- The minimality of k₀ shows that k₀ - 1 does not satisfy
  -- the condition.
  have k_1_lt_k : k0 - 1 < k0,
    exact sub_one_lt_of_pos k0_positive,
  have x_lt_k0_1 : ¬ x < ↑(k0 - 1) * (↑n)⁻¹,
    exact nat.find_min hp k_1_lt_k,

  by_contradiction h_y_le_k0_div_n,
  simp at h_y_le_k0_div_n,
  -- We have now assumed that k₀/n ≥ y.  The rest seems more
  -- painful than it perhaps should be?
  apply x_lt_k0_1,
  have h_y_sub_1n : y - (n : ℝ)⁻¹ ≤ ((k0 : ℝ) - 1) * (n : ℝ)⁻¹,
    rw [sub_mul, one_mul],
    simpa,
  have x_lt_y_sub_1n : x < y - (n : ℝ)⁻¹,
    have n1_lt_y_sub_x : (n : ℝ)⁻¹ < y - x,
      rw ← one_div,
      exact hn.right,
    -- Would like to do: apply lt_tsub_comm.1, but then we
    -- need to show that ℝ is an instance of add_comm_monoid
    -- (and I don't understand why that is not automatic from
    -- importing data.real.basic) and has_ordered_sub (and
    -- surely that should be defined somewhere?)
    apply (add_lt_add_iff_right (n : ℝ)⁻¹).1,
    apply (add_lt_add_iff_right (-x)).1,
    simp,
    apply add_lt_of_lt_sub_right,
    exact n1_lt_y_sub_x,
  norm_cast at h_y_sub_1n,
  exact lt_of_lt_of_le x_lt_y_sub_1n h_y_sub_1n,
end

lemma rational_between_reals (x y : ℝ) (h : x < y): ∃ r : ℚ, (x < r) ∧ (↑r < y) :=
begin
  have h_x_le_or_lt : 0 ≤ x ∨ x < 0,
    exact le_or_lt _ _ ,
  cases h_x_le_or_lt,
    -- 0 ≤ x < y is our previous result
    exact rational_between_nonneg_reals x y h h_x_le_or_lt,

  have h_y_le_or_lt : y ≤ 0 ∨ 0 < y,
    exact le_or_lt _ _ ,
  cases h_y_le_or_lt,
    -- x < y ≤ 0, so 0 ≤ -y < -x and we can apply the previous result
    -- to -y and -x
    have h' : -y < -x,
      exact neg_lt_neg h,
    have h_negy_nonneg: 0 ≤ -y,
      exact neg_nonneg_of_nonpos h_y_le_or_lt,
    cases rational_between_nonneg_reals (-y) (-x) h' h_negy_nonneg with rneg hrneg,
      use -rneg,
    simp,
    split,
      rw ← neg_neg x,
      exact neg_lt_neg hrneg.right,
      rw ← neg_neg y,
      exact neg_lt_neg hrneg.left,

  -- x < 0 < y, so we can just use 0
  use 0,
  split,
  repeat { simpa },
end

end
