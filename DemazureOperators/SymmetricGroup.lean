import DemazureOperators.Matsumoto
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace CoxeterSystem
noncomputable section

variable (n : ℕ)
def M := CoxeterMatrix.Aₙ n
def cs := (M n).toCoxeterSystem

abbrev S (n : ℕ) := Equiv.Perm (Fin n)
abbrev A (n : ℕ) := (M n).Group
instance : Group (S (n + 1)) := Equiv.Perm.permGroup

def f_simple : Fin n → S (n + 1) :=
  fun i => Equiv.swap i.castSucc i.succ

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

theorem f_liftable : (M n).IsLiftable (f_simple n) := by
  intro i j
  simp[M, CoxeterMatrix.Aₙ]
  by_cases heq : i = j
  simp[heq]
  simp[f_simple]

  simp[heq]

  by_cases h1 : j.succ = i.castSucc ∨ i.succ = j.castSucc
  · have h1' :  (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      simp[Fin.ext_iff] at h1
      simp[h1]

    rw[if_pos h1']
    simp[f_simple]
    have hcycle := cycle_of_adjacent_swap n i j heq h1
    obtain ⟨ ho , _ ⟩ := (orderOf_eq_iff (by linarith)).mp (Equiv.Perm.IsThreeCycle.orderOf hcycle)
    exact ho

  · have h1' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      simp[Fin.ext_iff] at h1
      simp[h1]

    rw[if_neg h1']
    simp[f_simple]
    apply Equiv.ext_iff.mpr
    intro k
    simp only [pow_succ]

    rcases not_or.mp h1 with ⟨ h1, h2 ⟩

    have h3 : ¬ (i.castSucc = j.castSucc) := by
      apply Fin.castSucc_inj.ne.mpr heq
    have h4 : ¬ (i.succ = j.succ) := by
      apply Fin.succ_inj.ne.mpr heq

    rw[← ne_eq] at h1 h2 h3 h4

    have h_disjoint : Equiv.Perm.Disjoint (Equiv.swap i.castSucc i.succ) (Equiv.swap j.castSucc j.succ) := by
      intro k
      apply or_iff_not_imp_left.mpr
      intro h
      rcases Equiv.eq_or_eq_of_swap_apply_ne_self h with h | h
      apply Equiv.swap_apply_of_ne_of_ne
      repeat
        simp[h, heq, h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]
      apply Equiv.swap_apply_of_ne_of_ne h2 h4

    nth_rewrite 2 [Equiv.Perm.Disjoint.commute h_disjoint]
    simp

def f := lift (cs n) ⟨ f_simple n, f_liftable n ⟩

theorem f_apply_simple (i : Fin n) : f n ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  apply lift_apply_simple (cs n)

theorem f_surjective : Function.Surjective (f n) := by
  apply MonoidHom.mrange_top_iff_surjective.mp
  apply eq_top_iff.mpr

  have : Submonoid.closure (Set.range fun (i : Fin n) ↦ Equiv.swap i.castSucc i.succ) = ⊤ := by
    exact Equiv.Perm.mclosure_swap_castSucc_succ n

  rw[← this]
  simp

  intro p hp
  simp at hp
  rcases hp with ⟨ i, rfl ⟩
  simp
  use (cs n).simple i
  simp[f_apply_simple]


def withoutLast := Subgroup.closure (Set.range fun (i : Fin (n - 1)) ↦ (cs n).simple ⟨i, Nat.lt_of_lt_pred i.is_lt⟩)
def minLengthWord := (Set.range fun y : (withoutLast n) ↦ (cs n).length y)

instance : Subsingleton (FreeGroup (Fin 0)) := by
  infer_instance

instance : Subsingleton (A 0) := by
  simp[A, CoxeterMatrix.Group, PresentedGroup]
  apply Quotient.instSubsingletonQuotient

theorem cardA0 : Nat.card (A 0) = 1 := by
  exact Nat.card_unique

instance : Finite (A 0) := by
  infer_instance



def subgroupequiv : withoutLast n ≃* A (n - 1) := by
  sorry

lemma withoutLast_index_le_n_succ : (withoutLast n).index ≤ n + 1 := by
  sorry

theorem card_symm_eq_factorial : Nat.card (S n) = Nat.factorial n := by
  simp[S]
  rw[Fintype.card_perm]
  simp

theorem card_An_le_card_Sn : Nat.card (A n) ≤ Nat.card (S (n+1)) := by
  rw[card_symm_eq_factorial (n + 1)]

  induction n
  case zero =>
    simp only [Nat.factorial]
    ring
    rw[cardA0]
  case succ n ih =>
    rw[A]
    rw[← Subgroup.card_mul_index (withoutLast (n + 1))]
    rw[Nat.factorial_succ]

    have : Nat.card (withoutLast (n + 1)) = Nat.card (A n) := by
      sorry

    rw[this, mul_comm]
    apply Nat.mul_le_mul
    · exact withoutLast_index_le_n_succ (n + 1)
    · exact ih

instance : Finite (A n) := by
  induction n
  case zero => infer_instance
  case succ n ih =>
    apply Nat.finite_of_card_ne_zero


theorem card_An_eq_card_Sn : Nat.card (A n) = Nat.card (S (n+1)) := by
  apply Nat.le_antisymm
  · exact card_An_le_card_Sn n
  · exact Nat.card_le_card_of_surjective (f n) (f_surjective n)

theorem f_bijective : Function.Bijective (f n) := by
  apply (Function.Surjective.bijective_of_nat_card_le (f_surjective n) _)
  exact card_An_le_card_Sn n

def f_equiv : (A n) ≃* S (n + 1) := by
  apply MulEquiv.ofBijective (f n)
  exact f_bijective n

theorem f_equiv_apply_simple (i : Fin n) : (f_equiv n) ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  simp[f_equiv, f_apply_simple]

def S_cox : CoxeterSystem (M n) (S (n + 1)) := ⟨ (f_equiv n).symm ⟩

theorem S_cox_simple (i : Fin n) : (S_cox n).simple i = (Equiv.swap i.castSucc (i.succ)) := by
  rw[← f_equiv_apply_simple]
  rfl

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
