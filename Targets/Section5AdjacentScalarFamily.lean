import Targets.Section5InterleavedScalarContinuity
import Targets.Section5AdjacentBoundary
import Targets.Section5StableSortFilter

/-!
# Adjacent inserted trials at a common breakpoint

At `u = q j`, the two inserted tagged lists differ only by the tagged
interpolation entry at position `j`.  Its variance is zero in both trials.
This file records the exact finite sorting/deletion argument needed to remove
that entry.  The final cascade equality is deliberately stated for the
list-level mixed scalar recursion; the bridge to the recursively indexed
family is included below.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private abbrev AdjTag (k : ℕ) := Section5MassTag k

private noncomputable def adjRawMass {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a : AdjTag k) : ℝ := section5TaggedMass s r j a

private noncomputable def adjKey {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a : AdjTag k) : ℝ ×ₗ Fin ((k + 2) + (k + 3)) :=
  (adjRawMass s r j a, finSumFinEquiv a)

private noncomputable def adjOrder {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a b : AdjTag k) : Prop := adjKey s r j a ≤ adjKey s r j b

private noncomputable instance adjOrderDecidable {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) : DecidableRel (adjOrder s r j) :=
  fun _ _ => by classical exact inferInstance

private theorem adjRawMass_at_interleaving {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (i : Fin ((k + 2) + (k + 3))) :
    adjRawMass s r j (section5Interleaving s r j i) =
      section5UnsortedMass s r j (Tuple.sort (section5UnsortedMass s r j) i) := by
  exact congrFun (section5InterleavedMass_eq_sort s r j) i

private theorem adjKey_pairwise {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (_hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).Pairwise (adjOrder s r j) := by
  apply List.pairwise_ofFn.mpr
  intro i q hij
  have hmono := (Tuple.eq_sort_iff (f := section5UnsortedMass s r j)
    (σ := Tuple.sort (section5UnsortedMass s r j))).mp rfl |>.1 hij.le
  have hraw : adjRawMass s r j (section5Interleaving s r j i) ≤
      adjRawMass s r j (section5Interleaving s r j q) := by
    rw [adjRawMass_at_interleaving, adjRawMass_at_interleaving]
    exact hmono
  unfold adjOrder adjKey
  change toLex
      (adjRawMass s r j (section5Interleaving s r j i),
        finSumFinEquiv (section5Interleaving s r j i)) ≤
    toLex
      (adjRawMass s r j (section5Interleaving s r j q),
        finSumFinEquiv (section5Interleaving s r j q))
  rw [Prod.Lex.toLex_le_toLex]
  rcases hraw.eq_or_lt with heq | hlt
  · right
    refine ⟨heq, ?_⟩
    have heq' : section5UnsortedMass s r j (Tuple.sort
        (section5UnsortedMass s r j) i) =
        section5UnsortedMass s r j (Tuple.sort
          (section5UnsortedMass s r j) q) := by
      simpa only [adjRawMass_at_interleaving] using heq
    have hs := (Tuple.eq_sort_iff (f := section5UnsortedMass s r j)
      (σ := Tuple.sort (section5UnsortedMass s r j))).mp rfl |>.2 i q hij heq'
    simpa [section5Interleaving] using hs.le
  · exact Or.inl hlt

private theorem adjKey_pairwise_source {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).Pairwise (adjOrder s r j) := by
  exact adjKey_pairwise s r j hj

private noncomputable def adjSourceTags {k : ℕ} : List (AdjTag k) :=
  List.ofFn (finSumFinEquiv.symm : Fin ((k + 2) + (k + 3)) → AdjTag k)

private theorem adjSortedTagList_eq_insertionSort {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (hj : j ≤ k + 1) :
    List.ofFn (section5Interleaving s r j) =
      (adjSourceTags (k := k)).insertionSort (adjOrder s r j) := by
  classical
  letI : DecidableRel (adjOrder s r j) := fun a b => inferInstance
  letI : Std.Total (adjOrder s r j) := ⟨fun a b => le_total _ _⟩
  letI : IsTrans (AdjTag k) (adjOrder s r j) := ⟨fun a b c => le_trans⟩
  letI : Std.Antisymm (adjOrder s r j) := ⟨fun a b h₁ h₂ => by
    have hk : adjKey s r j a = adjKey s r j b := le_antisymm h₁ h₂
    have hi := congrArg (fun z : ℝ ×ₗ Fin ((k + 2) + (k + 3)) => z.2) hk
    exact finSumFinEquiv.injective hi⟩
  let σ := Tuple.sort (section5UnsortedMass s r j)
  let e₀ : Fin ((k + 2) + (k + 3)) ≃ AdjTag k := finSumFinEquiv.symm
  have hp : (List.ofFn (e₀ ∘ σ)).Perm (List.ofFn e₀) :=
    Equiv.Perm.ofFn_comp_perm σ e₀
  have hp' : (List.ofFn (section5Interleaving s r j)).Perm
      (adjSourceTags (k := k)) := by
    simpa [section5Interleaving, e₀, σ, Function.comp_def, adjSourceTags] using hp
  have hsort : ((adjSourceTags (k := k)).insertionSort (adjOrder s r j)).Pairwise
      (adjOrder s r j) := by
    exact List.pairwise_insertionSort _ _
  exact List.Perm.eq_of_pairwise' (adjKey_pairwise s r j hj) hsort
    (hp'.trans (List.perm_insertionSort _ _).symm)

theorem section5TagScalarMass_adjacent_boundary_of_ne
    {k : ℕ} (s : RSBScheme k) {r j : ℕ} (hj : j ≤ k + 1)
    (negative : Bool) (tag : Section5MassTag k)
    (htag : tag ≠ Sum.inr ⟨j, by omega⟩) :
    section5TagScalarMass s r j tag =
      section5TagScalarMass s r (j + 1) tag := by
  rw [section5TagScalarMass_eq_original, section5TagScalarMass_eq_original]
  rcases tag with p | p
  · rfl
  · by_cases hp : (p : ℕ) < j
    · have hp' : (p : ℕ) ≤ j := by omega
      simp [section5TagOriginalLevel, hp, hp']
    · by_cases he : (p : ℕ) = j
      · exfalso
        apply htag
        congr 1
        exact Fin.ext he
      · have hp' : ¬(p : ℕ) ≤ j := by omega
        simp [section5TagOriginalLevel, hp, he, hp']

private theorem adjOrder_congr_of_ne {k : ℕ} (s : RSBScheme k)
    {r j : ℕ} (hj : j ≤ k + 1) {a b : Section5MassTag k}
    (ha : a ≠ Sum.inr ⟨j, by omega⟩) (hb : b ≠ Sum.inr ⟨j, by omega⟩) :
    adjOrder s r j a b ↔ adjOrder s r (j + 1) a b := by
  simp only [adjOrder, adjKey, adjRawMass]
  rw [section5TaggedMass_adjacent_boundary_of_ne s hj a ha,
    section5TaggedMass_adjacent_boundary_of_ne s hj b hb]

private theorem section5TaggedVariance_adjacent_boundary_zero
    {k : ℕ} (s : RSBScheme k) (β t : ℝ) {j : ℕ} (hj : j ≤ k + 1) :
    section5TaggedVariance s β t (s.q j) j (Sum.inr ⟨j, by omega⟩) = 0 := by
  simp only [section5TaggedVariance, Sum.elim_inr]
  simp [section5Rho]

theorem section5SortedTagList_adjacent_boundary_erase
    {k : ℕ} (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj : j + 1 ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).erase (Sum.inr ⟨j, by omega⟩) =
      (List.ofFn (section5Interleaving s r (j + 1))).erase
        (Sum.inr ⟨j, by omega⟩) := by
  classical
  letI : ReflBEq (AdjTag k) := ⟨by
    intro a
    cases a <;> simp⟩
  letI : LawfulBEq (AdjTag k) := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all⟩
  let x : Section5MassTag k := Sum.inr ⟨j, by omega⟩
  letI : Std.Total (adjOrder s r j) := ⟨fun a b => le_total _ _⟩
  letI : IsTrans (AdjTag k) (adjOrder s r j) := ⟨fun a b c => le_trans⟩
  letI : Std.Antisymm (adjOrder s r j) := ⟨fun a b h₁ h₂ => by
    have hk : adjKey s r j a = adjKey s r j b := le_antisymm h₁ h₂
    have hi := congrArg (fun z : ℝ ×ₗ Fin ((k + 2) + (k + 3)) => z.2) hk
    exact finSumFinEquiv.injective hi⟩
  have hpj := adjSortedTagList_eq_insertionSort s r j (by omega)
  have hpj1 := adjSortedTagList_eq_insertionSort s r (j + 1) (by omega)
  have hpairj : ((List.ofFn (section5Interleaving s r j)).erase x).Pairwise
      (adjOrder s r j) :=
    List.Pairwise.sublist (l₁ := (List.ofFn (section5Interleaving s r j)).erase x)
      (l₂ := List.ofFn (section5Interleaving s r j)) List.erase_sublist
      (adjKey_pairwise s r j (by omega))
  have hpairj1 : ((List.ofFn (section5Interleaving s r (j + 1))).erase x).Pairwise
      (adjOrder s r j) := by
    apply ((adjKey_pairwise s r (j + 1) (by omega)).sublist List.erase_sublist).imp_of_mem
    intro a b ha hb hab
    apply (adjOrder_congr_of_ne s (by omega) ?_ ?_).mpr hab
    · intro hax
      subst a
      have hn : x ∉ (List.ofFn (section5Interleaving s r (j + 1))).erase x :=
        (List.nodup_ofFn.mpr (section5Interleaving s r (j + 1)).injective).not_mem_erase
      exact hn ha
    · intro hbx
      subst b
      have hn : x ∉ (List.ofFn (section5Interleaving s r (j + 1))).erase x :=
        (List.nodup_ofFn.mpr (section5Interleaving s r (j + 1)).injective).not_mem_erase
      exact hn hb
  have hpermj : (List.ofFn (section5Interleaving s r j)).Perm
      (adjSourceTags (k := k)) := by
    rw [hpj]
    exact List.perm_insertionSort _ _
  have hpermj1 : (List.ofFn (section5Interleaving s r (j + 1))).Perm
      (adjSourceTags (k := k)) := by
    rw [hpj1]
    exact List.perm_insertionSort _ _
  have hperm : ((List.ofFn (section5Interleaving s r j)).erase x).Perm
      ((List.ofFn (section5Interleaving s r (j + 1))).erase x) := by
    exact (hpermj.erase x).trans (hpermj1.erase x).symm
  exact List.Perm.eq_of_pairwise' hpairj hpairj1 hperm

end SpinGlass.Targets
