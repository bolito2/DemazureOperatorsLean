import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Algebra.Group.NatPowAssoc
import Init.Data.List.Lemmas

open CoxeterSystem

variable {B : Type}
variable {W : Type} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def T : Type := {t : W // IsReflection cs t}

def nReflectionOccurrences (cs : CoxeterSystem M W) (w : List B) (t : T cs) : ℕ :=
  (cs.leftInvSeq w).count t.1

def parityReflectionOccurrences (w : List B) (t : T cs) : ZMod 2 :=
  (nReflectionOccurrences cs w t : ZMod 2)

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

lemma getElem_alternatingWord' (i j : B) (p k : ℕ) (h : k < p) :
  (alternatingWord i j p)[k]'(by simp; exact h) =  (if Even (p + k) then i else j) := by
  have h' : k < (alternatingWord i j p).length := by simp; exact h
  let k' : Fin ((alternatingWord i j p).length) := ⟨k, h'⟩
  suffices (alternatingWord i j p)[k'] = (if Even (p + k) then i else j) from by
    simp at this
    exact this
  rw[getElem_alternatingWord i j p k']

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

lemma list_take_alternatingWord (i j : B) (k : ℕ) (h : k < 2 * p) :
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


lemma list_take_induction (i j : B) (p : ℕ) (k : ℕ) (h : k + 1 < 2 * p) :
  List.take (k + 1) (alternatingWord i j (2 * p)) = i :: (List.take k (alternatingWord j i (2 * p))) := by

  have h' : k < 2 * p := lt_of_lt_plus_one k (2 * p) h

  by_cases h_even : Even k
  · rw[list_take_alternatingWord j i k h']
    rw[list_take_alternatingWord i j (k+1) h]
    have h_odd : ¬ Even (k + 1) := by
      simp
      exact Even.add_one h_even

    simp [h_even, h_odd]
    rw[alternatingWord_succ']
    simp[h_even]

  · rw[list_take_alternatingWord j i k h']
    rw[list_take_alternatingWord i j (k+1) h]
    have h_odd : Even (k + 1) := by
      simp at h_even
      exact Odd.add_one h_even

    simp [h_even, h_odd]
    rw[alternatingWord_succ']
    simp[h_even]

lemma leftInvSeq_alternatingWord_induction (i j : B) (p : ℕ) (k : ℕ) (h : k + 1 < 2 * p) :
 (leftInvSeq cs (alternatingWord i j (2 * p))).get ⟨k + 1, by simp; exact h⟩ =
  MulAut.conj (s i) ((leftInvSeq cs (alternatingWord j i (2 * p))).get ⟨k, by simp; linarith ⟩) := by

  rw [CoxeterSystem.get_leftInvSeq cs (alternatingWord i j (2 * p)) ⟨k + 1, by simp; exact h⟩]
  rw [CoxeterSystem.get_leftInvSeq cs (alternatingWord j i (2 * p)) ⟨k, by simp; linarith ⟩]
  simp only [MulAut.conj]
  dsimp

  have h_take : cs.wordProd (List.take (k + 1) (alternatingWord i j (2 * p))) = cs.simple i *
      (cs.wordProd (List.take k (alternatingWord j i (2 * p)))) := by
    rw [list_take_induction i j p k h]
    rw [cs.wordProd_cons]

  rw [h_take]
  simp [mul_assoc]
  rw[centralS_equal_swapping_indices i j (2 * p) k]

theorem alternatingWord_of_get_leftInvSeq_alternatingWord (i j : B) (p : ℕ) (k : ℕ) (h : k < 2 * p) :
  (leftInvSeq cs (alternatingWord i j (2 * p))).get ⟨k, by simp; linarith ⟩ = π alternatingWord j i (2 * k + 1)  := by
  have p_gt_0 : 2 * p > 0 := by linarith

  revert i j
  induction k with
  | zero =>
    intro i j
    simp[alternatingWord]
    rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * p))) ⟨0, by simp[p_gt_0]⟩ ]
    rw [CoxeterSystem.get_leftInvSeq cs (alternatingWord i j (2 * p)) ⟨0, by simp[p_gt_0]⟩]
    simp[leftInvSeq]
    apply congr_arg
    rw[getElem_alternatingWord' i j (2 * p) 0 (by simp[p_gt_0])]
    simp
  | succ k hk =>
    intro i j
    have h'' : k < 2 * p := by linarith
    have h_ind : (cs.leftInvSeq (alternatingWord j i (2 * p))).get ⟨k, by simp; exact h''⟩ = cs.wordProd (alternatingWord i j (2 * k + 1)) := by
      apply hk h''
    rw[leftInvSeq_alternatingWord_induction cs i j p k h]
    rw[h_ind]
    simp
    rw[alternatingWord_succ' j i]
    simp[wordProd_cons]
    have : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw[this]
    rw[alternatingWord_succ j i]
    rw[wordProd_concat]
    simp[mul_assoc]

theorem alternatingWord_of_getElem_leftInvSeq_alternatingWord (i j : B) (p : ℕ) (k : ℕ) (h : k < 2 * p) :
  (leftInvSeq cs (alternatingWord i j (2 * p)))[k]'(by simp; linarith) = π alternatingWord j i (2 * k + 1)  := by
  rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * p))) ⟨k, by simp; linarith⟩]
  exact alternatingWord_of_get_leftInvSeq_alternatingWord cs i j p k h

lemma leftInvSeq_repeats : ∀ (k : ℕ) (h : k < M i j),
(cs.leftInvSeq (alternatingWord i j (2 * M i j))).get ⟨M i j + k, (by simp[h]; linarith)⟩   =
(cs.leftInvSeq (alternatingWord i j (2 * M i j))).get ⟨k, (by simp[h]; linarith)⟩ := by
  intro k h'
  rw[alternatingWord_of_get_leftInvSeq_alternatingWord cs i j (M i j) k]
  rw[alternatingWord_of_get_leftInvSeq_alternatingWord cs i j (M i j) ((M i j)+k)]
  rw[cs.prod_alternatingWord_eq_mul_pow]
  rw[cs.prod_alternatingWord_eq_mul_pow]

  have h_odd : Odd (2 * k + 1) := by
    simp

  have h_odd' : Odd (2 * ((M i j) + k) + 1) := by
    simp

  simp[h_odd, h_odd']

  have two_gt_0 : 2 > 0 := by linarith
  have h_exp : (2 * k + 1) / 2 = k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 k two_gt_0]
    simp
  have h_exp' : (2 * ((M i j) + k) + 1) / 2 = (M i j) + k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 ((M i j)+k) two_gt_0]
    simp
  rw[h_exp, h_exp']
  rw[NatPowAssoc.npow_add]
  simp
  linarith
  linarith

lemma leftInvSeq_repeats' : ∀ (k : ℕ) (h : k < M i j),
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[M i j + k]'(by simp[h]; linarith) =
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[k]'(by simp[h]; linarith) := by
  intro k h'
  rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ⟨M i j + k, by simp[h']; linarith⟩]
  rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ⟨k, by simp[h']; linarith⟩]
  exact leftInvSeq_repeats cs k h'

lemma nReflectionOccurrences_even_braidWord (t : T cs) :
  Even (nReflectionOccurrences cs (alternatingWord i j (2 * M i j)) t) := by

  suffices (nReflectionOccurrences cs (alternatingWord i j (2 * M i j)) t) = 2 * List.count (t.1) (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (M.M i j * 2)))) from by
    simp[this]

  simp[nReflectionOccurrences]
  suffices (cs.leftInvSeq (alternatingWord i j (2 * M i j))) = (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) ++ (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) from by
    rw[this]
    simp
    ring

  have m_le_two_m : M i j ≤ 2 * M i j := by linarith
  have length_eq : (cs.leftInvSeq (alternatingWord i j (2 * (M i j)))).length =
  (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ++ (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))))).length := by
    simp[m_le_two_m]
    ring

  apply List.ext_getElem length_eq
  intro k hk hk'

  by_cases h : k < M i j
  · have : k < (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length := by
      simp[h, m_le_two_m]

    rw[List.getElem_append_left (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) this]
    rw[List.getElem_take']
  · have h_k_le : k - M i j < M i j := by
      simp at hk
      apply Nat.sub_lt_left_of_lt_add
      simp at h
      exact h
      linarith
    have : ¬ k < (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length := by
      simp[h, m_le_two_m]
    rw[List.getElem_append_right (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) this]
    rw[List.getElem_take']
    simp[m_le_two_m]

    rw[← leftInvSeq_repeats' cs (k - M i j) h_k_le]

    suffices M.M i j + (k - M.M i j) = k from by
      simp[this]

    rw[← Nat.add_sub_assoc]
    simp
    linarith
    simp[m_le_two_m, h_k_le]

theorem List.count_concat_of_ne {α : Type u_1} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) (l : List α) :
  List.count a (l.concat (b)) = List.count a l := by
  simp[h]

theorem List.count_concat' {α : Type u_1} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) (l : List α) :
  List.count a (l.concat b) = List.count a l + if a = b then 1 else 0 := by
  by_cases h : a = b
  · rw[h]
    rw[List.count_concat_self b l]
    simp
  · rw[List.count_concat_of_ne h l]
    rw[if_neg h]
    ring

instance instMul : Mul (T cs × ZMod 2 → T cs × ZMod 2) where
  mul := fun f g => f ∘ g

lemma mulDef (f g : T cs × ZMod 2 → T cs × ZMod 2) : f * g = f ∘ g := rfl

instance : Monoid (T cs × ZMod 2 → T cs × ZMod 2) where
  one := id
  mul := (instMul cs).mul
  one_mul := by
    intro f
    funext x
    suffices (id ∘ f) x = f x from by
      rw[← this]
      rfl
    simp
  mul_one := by
    intro f
    funext x
    suffices (f ∘ id) x = f x from by
      rw[← this]
      rfl
    simp
  mul_assoc := by
    intro f g h
    funext x
    repeat rw[mulDef]
    rfl

def permutationMap_ofList (l : List B) : T cs × ZMod 2 → T cs × ZMod 2 :=
  match l with
  | [] => id
  | a :: t => permutationMap cs a * permutationMap_ofList t

lemma IsReflection.conj' (ht : cs.IsReflection t) (w : W) :
  cs.IsReflection (w⁻¹ * t * w) := by
  have : w = w⁻¹⁻¹ := by simp
  nth_rewrite 2 [this]
  apply IsReflection.conj ht w⁻¹

lemma nReflectionOccurrences_mk (l : List B) (t : T cs) :
  nReflectionOccurrences cs l t = List.sum (List.map (fun i => nu cs i t) l) := by
  sorry

lemma permutationMap_ofList_mk_1 (l : List B) : (permutationMap_ofList cs l ⟨t,z⟩).1 =
  ⟨(cs.wordProd l) * t.1 * (cs.wordProd l)⁻¹, IsReflection.conj t.2 (cs.wordProd l)⟩ := by
  induction l with
  | nil =>
    simp[permutationMap_ofList, permutationMap, nReflectionOccurrences]
  | cons a l h =>
    calc (permutationMap_ofList cs (a :: l) (t, z)).1 = ((permutationMap cs a * permutationMap_ofList cs l) (t, z)).1 := by simp[permutationMap_ofList]
      _ = (permutationMap cs a (permutationMap_ofList cs l (t, z))).1 := by rfl

    simp[permutationMap, conj, h]
    simp[cs.wordProd_cons]
    simp[mul_assoc]

lemma funComp_permgjagja (p : ℕ) (t : T cs) (z : ZMod 2) :
  (funComp (permutationMap cs j ∘ permutationMap cs i) p ⟨t, z⟩) =
  ⟨
    ⟨π (alternatingWord j i (2 * p)) * t.1 * (π (alternatingWord j i (2 * p)))⁻¹,
    IsReflection.conj t.2 (π (alternatingWord j i (2 * p)))⟩,
     z + parityReflectionOccurrences cs (alternatingWord j i (2 * p)) t
  ⟩ := by
  induction p with
  | zero =>
    simp[funComp, permutationMap, alternatingWord, parityReflectionOccurrences, nReflectionOccurrences]
  | succ p h =>
    simp[funComp]
    rw[h]
    simp[permutationMap]

    have : 2 * (p + 1) = 2 * p + 1 + 1 := by ring

    constructor
    · simp[conj]
      rw[this]
      rw[alternatingWord_succ']
      rw[wordProd_cons]
      rw[alternatingWord_succ']
      simp[wordProd_cons]
      simp[mul_assoc]
    · nth_rewrite 2 [parityReflectionOccurrences]
      simp[nu]
      rw[nReflectionOccurrences]
      rw[this]
      rw[alternatingWord_succ]
      rw[leftInvSeq_concat]
      rw[List.count_concat' t.1 (cs.wordProd (alternatingWord i j (2 * p + 1)) * cs.simple i *
            (cs.wordProd (alternatingWord i j (2 * p + 1)))⁻¹) (cs.leftInvSeq (alternatingWord i j (2 * p + 1)))]



theorem wah (i j : B) (h : M i j > 0) : funComp (permutationMap cs i ∘ permutationMap cs j) (M i j) = id := by
  let p := M i j
  funext ⟨t, z⟩
  simp


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
