import data.nat.lattice  -- need the import or open_locale fails

open_locale classical

def p2 := λ n : ℕ, n > 2

lemma hp2 : ∃ (m : ℕ), p2 m :=
begin
  use 3,
  have h32 : 3 > 2, by simp,
  exact h32,
end

lemma hp2_not0 : ¬ p2 0 :=
begin
  have h_not0 : ¬ 0 > 2, by simp,
  exact h_not0,
end

noncomputable def min_p2 : ℕ := nat.find hp2

lemma min_p2_positive : min_p2 > 0 :=
begin
  have min_p2_spec := nat.find_spec hp2,
  apply nat.pos_of_ne_zero,
  intro H,
  apply hp2_not0,
  rw ← H,
  exact min_p2_spec,
end

lemma sub_one_lt_of_pos { n : ℕ } (h : 0 < n) : n - 1 < n :=
begin
  have hm : ∃ m : ℕ, n = m.succ,
    use n - 1,
    cases n,
      simp,
      apply lt_irrefl 0,
      exact h,
    apply nat.succ_pred_eq_of_pos h,
  cases hm with m hm',
  rw hm',
  rw nat.succ_sub_one _,
  exact nat.lt_succ_self _,
end

lemma not_p_min_p2_sub_one : ¬ p2 (min_p2 - 1) :=
begin
  have h_min_p2_1 : min_p2 - 1 < min_p2,
    exact sub_one_lt_of_pos min_p2_positive,
  exact nat.find_min hp2 h_min_p2_1,
end
