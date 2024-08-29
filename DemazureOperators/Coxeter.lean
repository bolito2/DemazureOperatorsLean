import Mathlib.GroupTheory.Coxeter.Inversion

open CoxeterSystem

variable {B : Type*}
variable {W : Type*} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def nReflectionOccurrences (cs : CoxeterSystem M W) (w : List B) (t : W) : ℕ :=
  (cs.leftInvSeq w).count t

def parityReflectionOccurrences (w : List B) (t : W) : ZMod 2 :=
  (nReflectionOccurrences cs w t : ZMod 2)

def nu (i : B) (t : W) : ZMod 2 :=
  if (s i = t) then 1 else 0

def nu_simpleConj_eq_nu (i : B) (t : W) (h : IsReflection cs t) : nu cs i t = nu cs i (s i * t * (s i)) := by
  simp [nu]
  have : s i = t ↔ s i * t = 1 := by
    constructor
    · intro h'
      rw [h']
      exact IsReflection.mul_self h
    · intro h'
      apply (mul_left_inj t).mp
      simp [IsReflection.mul_self h]
      exact h'

  by_cases s i = t
  · simp [this]
  · simp [this]

def permutationMap (i : B) : W × ZMod 2 → W × ZMod 2 :=
  fun ⟨t, z⟩ => (s i * t * (s i)⁻¹ , z + nu cs i t)

def permutationMap_orderTwo (i : B) : permutationMap cs i ∘ permutationMap cs i = id := by
  funext ⟨t, z⟩
  simp [permutationMap, mul_assoc]




def permutationMap_comp (w u : List B) : permutationMap cs (w ++ u) = permutationMap cs w ∘ permutationMap cs u := by
  funext
  simp [permutationMap]
  sorry

lemma isLeftInversion_iff_nReflectionOccurrences_eq_one (w : List B) (t : W) (h : IsReflection cs t) :
  cs.IsLeftInversion (cs.wordProd w) t ↔ parityReflectionOccurrences cs w t = 1 := by
  constructor
  · sorry
  · rcases cs.exists_reduced_word (π w) with ⟨u, u_reduced, hu⟩
    rw [← hu]
    rw [← permutationMap_comp]
    simp [permutationMap]
    sorry

lemma odd_iff_parity_eq_one (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  simp [ZMod.eq_one_iff_odd]

lemma gt_one_of_odd (n : ℕ) : Odd n → n > 0 := by
  intro h
  simp[Odd] at h
  rcases h with ⟨m, rfl⟩
  suffices m ≥ 0 from by linarith
  exact Nat.zero_le m

theorem strongExchangeProperty (w : List B) (t : W) (h : IsReflection cs t)
 (h' : cs.IsLeftInversion (cs.wordProd w) t) :
  ∃ (i : Fin w.length), t * π w = π (w.eraseIdx i) := by

  suffices t ∈ cs.leftInvSeq w from by
    have : ∃ (i : Fin (cs.leftInvSeq w).length), (cs.leftInvSeq w).get i = t := List.get_of_mem this

    rcases this with ⟨i, hi⟩
    use ⟨i, by rw[← length_leftInvSeq cs w] ; exact i.2⟩
    rw[← hi]
    rw[← getD_leftInvSeq_mul_wordProd cs w i]
    simp
    rw[← List.get?_eq_getElem?]
    rw [List.get?_eq_get i.2]
    simp


  rw [isLeftInversion_iff_nReflectionOccurrences_eq_one cs w t h] at h'
  simp [parityReflectionOccurrences] at h'
  rw [← @odd_iff_parity_eq_one (nReflectionOccurrences cs w t)] at h'

  apply gt_one_of_odd (nReflectionOccurrences cs w t) at h'
  simp[nReflectionOccurrences] at h'

  exact h'