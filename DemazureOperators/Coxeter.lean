import Mathlib.GroupTheory.Coxeter.Inversion

open CoxeterSystem

variable {B : Type}
variable {W : Type} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def nReflectionOccurrences (cs : CoxeterSystem M W) (w : List B) (t : W) : ℕ :=
  (cs.leftInvSeq w).count t

def parityReflectionOccurrences (w : List B) (t : W) : ZMod 2 :=
  (nReflectionOccurrences cs w t : ZMod 2)


def T : Type := {t : W // IsReflection cs t}

def conj (t : T cs) (w : W) : T cs :=
  ⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩

lemma t_eq_conj_t (t : T cs) : t = conj cs t t.1 := by
  simp [conj]

def nu (i : B) (t : T cs) : ZMod 2 :=
  if (s i = t.1) then 1 else 0

def nu_simpleConj_eq_nu (i : B) (t : T cs) : nu cs i t = nu cs i (conj cs t (s i)) := by
  simp [nu]
  rcases t with ⟨t, ht⟩
  have : s i = t ↔ s i * t = 1 := by
    constructor
    · intro h'
      rw [h']
      exact IsReflection.mul_self ht
    · intro h'
      apply (mul_left_inj t).mp
      simp [IsReflection.mul_self ht]
      exact h'

  by_cases h : s i = t
  · simp [this, h, conj]
  · simp [this, h, if_neg, conj]

def permutationMap (i : B) : T cs × ZMod 2 → T cs × ZMod 2 :=
  fun (t , z) => (conj cs t (s i), z + nu cs i t)

def permutationMap_orderTwo (i : B) : permutationMap cs i ∘ permutationMap cs i = id := by
  funext ⟨t, z⟩
  simp [permutationMap]
  constructor
  · simp[conj, mul_assoc]
  · rw [← nu_simpleConj_eq_nu cs i t]
    ring_nf
    simp
    right
    rfl

def funComp (f : α → α) (n : ℕ) : α → α :=
  match n with
  | 0 => id
  | n + 1 => f ∘ funComp f n

lemma Odd.add_one : Odd n → Even (n + 1) := by
  intro h2
  by_contra h3
  simp at h3
  have contra1 : Even ((n + 1) - n) := by
    apply Nat.Odd.sub_odd h3 h2
  simp at contra1

lemma getElem_alternatingWord (i j : B) (p : ℕ) (k : Fin ((alternatingWord i j p).length)) :
  (alternatingWord i j p)[k] =  (if Even (p + k) then i else j) := by
  induction p with
  | zero =>
    rcases k with ⟨k, hk⟩
    simp[alternatingWord] at hk
  | succ n h =>
    revert k
    rw [alternatingWord_succ' i j n]

    rintro ⟨k, hk⟩

    induction k with
    | zero =>
      by_cases h2 : Even n
      · have : ¬ Even (n + 1) := by
          simp
          exact Even.add_one h2
        simp [h2, this]
      · have : Even (n + 1) := by
          simp at h2
          exact Odd.add_one h2
        simp [h2, this]
    | succ k _ =>
      simp only [List.getElem_cons_succ]
      have : k < (alternatingWord i j n).length := by
        simp
        simp at hk
        exact hk
      simp
      simp at h
      rw[h ⟨k, this⟩ ]
      simp
      ring
      have (m : ℕ) : Even (2 + m) ↔ Even m := by
        have aux : m ≤ 2 + m := by linarith
        apply (Nat.even_sub aux).mp
        simp
      by_cases h_even : Even (n + k)
      · simp [if_pos h_even]
        rw[← this (n+k)] at h_even
        rw[← Nat.add_assoc 2 n k] at h_even
        simp [if_pos h_even]
      · simp [if_neg h_even]
        rw[← this (n+k)] at h_even
        rw[← Nat.add_assoc 2 n k] at h_even
        simp [if_neg h_even]

lemma lt_of_lt_plus_one (k n : ℕ) (h : k + 1 < n) : k < n := by linarith
lemma alternatingWordLength_eq_reverse_alternatingWordLength (i j : B) (p : ℕ) :
(alternatingWord i j p).length = (alternatingWord j i p).length := by simp

lemma centralS_equal_swapping_indices (i j : B) (p k : ℕ) (h : k + 1 < (alternatingWord i j p).length) :
   (alternatingWord i j p)[k+1] =
   (alternatingWord j i p)[k]'(
    by apply lt_of_lt_plus_one k ((alternatingWord j i p).length); simp at h; simp [h]
  ) := by
  let h' := getElem_alternatingWord i j p ⟨k+1, h⟩
  simp at h'
  rw[ h' ]

  let h'' := getElem_alternatingWord j i p ⟨k, by apply lt_of_lt_plus_one k ((alternatingWord j i p).length); simp at h; simp [h]⟩
  simp at h''

  rw[h'']

  by_cases h_even : Even (p + k)
  · simp[if_pos h_even]
    rw[← add_assoc]
    apply Even.add_one at h_even
    simp [h_even]
  · simp [if_neg h_even]
    rw[← add_assoc]
    simp at h_even
    apply Odd.add_one at h_even
    simp [h_even]

theorem CoxeterSystem.get_leftInvSeq (w : List B) (j : Fin w.length) :
  (cs.leftInvSeq w).get ⟨j, by simp⟩ =
  cs.wordProd (List.take j w) * s (w.get ⟨j, by simp⟩) * (cs.wordProd (List.take j w))⁻¹ := by

  have h : j < (cs.leftInvSeq w).length := by simp

  rw [← List.getD_eq_get ((cs.leftInvSeq w)) 1 h]
  rw [getD_leftInvSeq]
  simp

lemma eq_flip_variables (i j : B) (p : ℕ) : (if Even p then j else i) = if Even (p + 1) then i else j := by
  by_cases h : Even p
  · simp [h]
    apply Even.add_one at h
    apply (@Nat.not_even_iff_odd (p+1)).mpr at h
    simp [if_neg h]
  · simp [h]
    simp at h
    apply Odd.add_one at h
    simp [if_pos h]

lemma what_da_sigma (i j : B) (k : ℕ) (h : k < 2 * p) :
  List.take k (alternatingWord i j (2 * p)) = if Even k then alternatingWord i j k else alternatingWord j i k := by
  induction k with
    | zero =>
      simp[alternatingWord]
    | succ k h' =>
      have hk : k < 2 * p := lt_of_lt_plus_one k (2 * p) h
      apply h' at hk

      by_cases h_even : Even k
      · simp [h_even] at hk
        have h_odd : ¬ Even (k + 1) := by
          simp
          exact Even.add_one h_even
        simp [h_even, h_odd]
        rw[← List.take_concat_get]
        rw[alternatingWord_succ]
        rw[← hk]
        apply congr_arg
        let k' : Fin (alternatingWord i j (2 * p)).length := ⟨k, by simp; exact lt_of_lt_plus_one k (2*p) h ⟩
        suffices (alternatingWord i j (2 * p))[k'] = i from by
          simp[k'] at this
          exact this
        rw[getElem_alternatingWord i j (2*p) k' ]
        have : Even (2 * p + k) := by
          apply Nat.even_add.mpr
          simp[h_even]
        simp[this]
      · simp [h_even] at hk
        have h_odd : Even (k + 1) := by
          simp at h_even
          exact Odd.add_one h_even
        simp [h_even, h_odd]
        rw[← List.take_concat_get]
        rw[alternatingWord_succ]
        rw[← hk]
        apply congr_arg
        let k' : Fin (alternatingWord i j (2 * p)).length := ⟨k, by simp; exact lt_of_lt_plus_one k (2*p) h ⟩
        suffices (alternatingWord i j (2 * p))[k'] = j from by
          simp[k'] at this
          exact this
        rw[getElem_alternatingWord i j (2*p) k' ]

        have : ¬ Even (2 * p + k) := by
          simp
          apply Nat.odd_add.mpr
          simp[h_even]
        simp[this]


lemma list_take_alternatingWord (i j : B) (k : ℕ) (h : k + 1 < (alternatingWord i j (2 * p)).length) :
  ∀ p : ℕ, List.take (k + 1) (alternatingWord i j (2 * p)) = i :: (List.take k (alternatingWord j i (2 * p))) := by
  induction k with
    | zero =>
      intro p
      rw[alternatingWord_succ' i j p]
      simp[alternatingWord]
      exact eq_flip_variables i j p
    | succ k h' =>
      have hk : k < (alternatingWord i j (p+1)).length := lt_of_lt_plus_one k (alternatingWord i j (p+1)).length h
      apply h' at hk
      -- specify the requirements of p, because we need to use the induction hypothesis --
      rw[alternatingWord_succ' i j k]
      simp
      rw[List.take_cons_succ (alternatingWord i j p) k hk]


lemma wario (i j : B) (p : ℕ) (k : ℕ) (h : k + 1 < 2 * p) :
 (leftInvSeq cs (alternatingWord i j (2 * p))).get ⟨k + 1, by simp; exact h⟩ =
  MulAut.conj (s j) ((leftInvSeq cs (alternatingWord j i (2 * p))).get ⟨k, by simp; linarith ⟩) := by

  rw [CoxeterSystem.get_leftInvSeq cs (alternatingWord i j (2 * p)) ⟨k + 1, by simp; exact h⟩]
  rw [CoxeterSystem.get_leftInvSeq cs (alternatingWord j i (2 * p)) ⟨k, by simp; linarith ⟩]
  simp only [MulAut.conj]
  dsimp
  sorry

theorem wah (i j : B) (h : M i j > 0) : funComp (permutationMap cs i ∘ permutationMap cs j) (M i j) = id := by
  let wBraid := alternatingWord i j (2 * M i j)
  let braidInvSeq := cs.leftInvSeq wBraid

  have braidInvSeqNotEmpty : braidInvSeq.length > 0 := by
    rw [length_leftInvSeq]
    simp [alternatingWord, wBraid]
    exact h

  have h' (k : Fin (braidInvSeq.length)) : (braidInvSeq.get k) = π (alternatingWord i j (2*k + 1)) := by
    -- Induction on k
    have zero : (braidInvSeq.get ⟨0, braidInvSeqNotEmpty⟩) = π (alternatingWord i j 1) := by
      simp only [braidInvSeq, alternatingWord, wBraid]
      rw [← List.getD_eq_get (cs.leftInvSeq (alternatingWord i j (2 * M.M i j))) 1 braidInvSeqNotEmpty]
      rw [CoxeterSystem.getD_leftInvSeq cs (alternatingWord i j (2 * M.M i j)) 0]
      simp[braidInvSeqNotEmpty]
      rw [alternatingWord_succ']

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
