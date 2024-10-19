import DemazureOperators.Matsumoto
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace CoxeterSystem
noncomputable section

variable (n : ℕ)
def M := CoxeterMatrix.Aₙ n
def cs := (M n).toCoxeterSystem

abbrev S (n : ℕ) := Equiv.Perm (Fin n)
instance : Group (S (n + 1)) := Equiv.Perm.permGroup

def f_simple : Fin n → S (n + 1) :=
  fun i => Equiv.swap i.castSucc i.succ

theorem f_liftable : (M n).IsLiftable (f_simple n) := sorry

def f := lift (cs n) ⟨ f_simple n, f_liftable n ⟩

theorem f_apply_simple (i : Fin n) : f n ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  apply lift_apply_simple (cs n)


theorem f_surjective : Function.Surjective (f n) := sorry
theorem f_injective : Function.Injective (f n) := sorry
theorem f_bijective : Function.Bijective (f n) := ⟨ f_injective n, f_surjective n ⟩

def f_equiv : (M n).Group ≃* S (n + 1) := by
  apply MulEquiv.ofBijective (f n)
  exact f_bijective n

theorem f_equiv_apply_simple (i : Fin n) : (f_equiv n) ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  simp[f_equiv, f_apply_simple]

def S_cox : CoxeterSystem (M n) (S (n + 1)) := ⟨ (f_equiv n).symm ⟩

theorem S_cox_simple (i : Fin n) : (S_cox n).simple i = (Equiv.swap i.castSucc (i.succ)) := by
  rw[← f_equiv_apply_simple]
  rfl

lemma cycle_of_adjacent_swap (i j : Fin n) (hij : i ≠ j) (h1 : j.succ = i.castSucc ∨ i.succ = j.castSucc) :
  Equiv.Perm.IsThreeCycle (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ) := by
  rcases h1 with h1 | h1
  · rw[h1]
    rw[Equiv.swap_comm j.castSucc i.castSucc]
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    · rw[← h1]
      apply (Fin.succ_inj.ne).mpr hij.symm
    · apply (Fin.castSucc_inj.ne).mpr hij
    · intro h
      simp[Fin.ext_iff] at h
      simp[Fin.ext_iff] at h1
      rw[← h1] at h
      linarith
  · rw[h1]
    rw[Equiv.swap_comm i.castSucc j.castSucc]
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    · apply (Fin.castSucc_inj.ne).mpr hij.symm
    · rw[← h1]
      apply (Fin.succ_inj.ne).mpr hij
    · intro h
      simp[Fin.ext_iff] at h
      simp[Fin.ext_iff] at h1
      rw[h] at h1
      linarith



instance instOfMatsumotoReady : MatsumotoReady (S_cox n) where
  one_le_M := by
    intro i j
    simp[M, CoxeterMatrix.Aₙ]
    by_cases h1 : i = j
    repeat
      by_cases h2 : j.val + 1 = i.val ∨ i.val + 1 = j
      repeat simp [h1, h2]
  alternatingWords_ne_one := by
    intro i j hij p hp hp'
    simp[M, CoxeterMatrix.Aₙ] at hp'
    rw[if_neg hij] at hp'

    simp[S_cox_simple]

    by_cases h1 : j.succ = i.castSucc ∨ i.succ = j.castSucc

    · have h1' :  (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        simp[Fin.ext_iff] at h1
        simp[h1]

      rw[if_pos h1'] at hp'



      have zero_lt_three : 0 < 3 := by
        linarith

      have : Equiv.Perm.IsThreeCycle (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ) := by
        apply cycle_of_adjacent_swap n i j hij h1

      obtain ⟨ _, ho ⟩ := (orderOf_eq_iff zero_lt_three).mp (Equiv.Perm.IsThreeCycle.orderOf this)
      simp at ho

      apply ho p hp' hp

    · have h1 : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        simp[Fin.ext_iff] at h1
        simp[h1]

      rw[if_neg h1] at hp'
      have : p = 1 := by
        linarith
      simp[this]
      intro h_contra

      have h_swap : (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ) j = j.succ := by
        simp[Equiv.swap_apply_of_ne_of_ne, hij, h1]
        apply Equiv.swap_apply_of_ne_of_ne
        intro h
        simp at h1
        apply Fin.ext_iff.mp at h
        simp at h
        simp[h] at h1
        intro h
        apply Fin.succ_inj.mp at h
        apply hij h.symm

      rw[h_contra] at h_swap
      simp at h_swap
      apply Fin.ext_iff.mp at h_swap
      simp at h_swap
