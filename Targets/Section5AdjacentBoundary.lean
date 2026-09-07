import Targets.TalagrandSection5

/-!
# Adjacent inserted-overlap boundary identities

At a shared breakpoint the two inserted overlap sequences are literally the
same sequence: inserting `q j` immediately before or immediately after the
level gives the same cumulative values. This elementary identity is the
overlap part of the later adjacent-trial cascade gluing; it does not yet
identify the sorted tagged Gaussian operators.
-/

namespace SpinGlass.Targets

theorem section5Rho_adjacent_boundary {k : ℕ} (s : RSBScheme k)
    {j : ℕ} (_hj : j ≤ k + 1) (u : ℝ) (hu : u = s.q j) (p : ℕ) :
    section5Rho s j u p = section5Rho s (j + 1) u p := by
  subst u
  unfold section5Rho
  by_cases hlt : p < j
  · have hlt' : p < j + 1 := by omega
    simp only [if_pos hlt, if_pos hlt']
  · by_cases heq : p = j
    · subst p
      simp
    · have hlt' : ¬p < j + 1 := by omega
      by_cases heq' : p = j + 1
      · subst p
        simp
      · simp [hlt, heq, hlt', heq']

theorem section5Rho_adjacent_boundary_all {k : ℕ} (s : RSBScheme k)
    {j : ℕ} (hj : j ≤ k + 1) (p : ℕ) :
    section5Rho s j (s.q j) p = section5Rho s (j + 1) (s.q j) p :=
  section5Rho_adjacent_boundary s hj (s.q j) rfl p

end SpinGlass.Targets
