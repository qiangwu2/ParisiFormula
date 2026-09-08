import Targets.Section5Interleaving

/-!
# Strict stable-sort order for interleaved witnesses

The existing stable-sort adapter preserves input order at equal or increasing
values.  A variable inserted mass can instead put two tagged entries in strict
mass order even when their positions in the concatenated input are reversed.
This elementary lemma exposes that lower-level fact without introducing a
second interleaving construction.
-/

namespace SpinGlass.Targets

theorem stableSort_position_lt_of_lt {N : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin N → α) {i j : Fin N} (hij : f i < f j) :
    (Tuple.sort f).symm i < (Tuple.sort f).symm j := by
  by_contra h
  have hle : (Tuple.sort f).symm j ≤ (Tuple.sort f).symm i := le_of_not_gt h
  have hs := Tuple.monotone_sort f hle
  have hmass : f j ≤ f i := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hs
  exact (not_le_of_gt hij) hmass

/- The strict half-mass ordering at a physical right-neighbor boundary.  The
interpolating copy of level `r` has raw mass `m r / 2`, while the physical copy
has raw mass `m r`; this order is independent of the stable tie convention. -/
theorem section5Interleaving_interpolating_before_physical_of_pos_mass
    {k : ℕ} (s : RSBScheme k) {r : ℕ} (hr : r ≤ k)
    (hm : 0 < s.m r) :
    (section5Interleaving s r (r + 1)).symm
        (Sum.inr ⟨r, by omega⟩) <
      (section5Interleaving s r (r + 1)).symm
        (Sum.inl ⟨r, by omega⟩) := by
  let f := section5UnsortedMass s r (r + 1)
  let i : Fin ((k + 2) + (k + 3)) :=
    finSumFinEquiv (Sum.inr ⟨r, by omega⟩)
  let j : Fin ((k + 2) + (k + 3)) :=
    finSumFinEquiv (Sum.inl ⟨r, by omega⟩)
  have hf : f i < f j := by
    have hi : f i = s.m r / 2 := by
      have he : i = Fin.natAdd (k + 2) ⟨r, by omega⟩ := by
        apply Fin.ext
        simp [i, finSumFinEquiv_apply_right]
      rw [he]
      dsimp [f, section5UnsortedMass]
      have he' : (⟨k + 2 + r, by omega⟩ : Fin ((k + 2) + (k + 3))) =
          Fin.natAdd (k + 2) ⟨r, by omega⟩ := by
        apply Fin.ext
        simp
      rw [he', Fin.append_right]
      simp [section5Mass]
    have hj : f j = s.m r := by
      have he : j = Fin.castAdd (k + 3) ⟨r, by omega⟩ := by
        apply Fin.ext
        simp [j, finSumFinEquiv_apply_left]
      rw [he]
      dsimp [f, section5UnsortedMass]
      have he' : (⟨r, by omega⟩ : Fin ((k + 2) + (k + 3))) =
          Fin.castAdd (k + 3) ⟨r, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [he', Fin.append_left]
      simp [section5PhysicalMass]
    rw [hi, hj]
    linarith
  have H := stableSort_position_lt_of_lt f hf
  simpa only [section5Interleaving, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, i, j] using H

end SpinGlass.Targets
