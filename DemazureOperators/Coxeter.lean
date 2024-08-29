import Mathlib.GroupTheory.Coxeter.Inversion

open CoxeterSystem

variable {B : Type*}
variable {W : Type*} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def number_of_reflection_occurrences (cs : CoxeterSystem M W) (w : List B) (t : W) : ℕ :=
  (cs.leftInvSeq w).count t

def parity_number_of_reflection_occurrences (w : List B) (t : W) : ZMod 2 :=
  (number_of_reflection_occurrences cs w t : ZMod 2)

def T := { t : W // IsReflection cs t }

def permutation_map (w : List B) : W × ZMod 2 → W × ZMod 2 :=
  fun ⟨t, z⟩ => (π w * t * (π w)⁻¹ , z + (parity_number_of_reflection_occurrences cs w t))

def permutation_map_comp (w u : List B) : permutation_map cs (w ++ u) = permutation_map cs w ∘ permutation_map cs u := by
  funext
  simp [permutation_map]
  sorry

lemma leftInversion_eq_nReflections_one (w : List B) (t : W) (h : IsReflection cs t) :
  ℓ (t * π w) < ℓ (π w) ↔ parity_number_of_reflection_occurrences cs w t = 1 := by sorry

lemma parity_one_iff_odd (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  simp [ZMod.eq_one_iff_odd]

lemma gt_one_of_odd (n : ℕ) : Odd n → n > 0 := by
  intro h
  simp[Odd] at h
  rcases h with ⟨m, rfl⟩
  suffices m ≥ 0 from by linarith
  exact Nat.zero_le m

theorem strong_exchange_property (w : List B) (t : W) (h : IsReflection cs t)
 (h' : ℓ (t * π w) < ℓ (π w)) :
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


  rw [leftInversion_eq_nReflections_one cs w t h] at h'
  simp [parity_number_of_reflection_occurrences] at h'
  rw [← @parity_one_iff_odd (number_of_reflection_occurrences cs w t)] at h'

  apply gt_one_of_odd (number_of_reflection_occurrences cs w t) at h'
  simp[number_of_reflection_occurrences] at h'

  exact h'
