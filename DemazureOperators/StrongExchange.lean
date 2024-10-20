import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Algebra.Group.NatPowAssoc
import Init.Data.List.Lemmas

set_option linter.unusedSectionVars false

namespace CoxeterSystem
noncomputable section

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "len" => cs.length

instance : DecidableEq W := Classical.typeDecidableEq W

def T : Type := {t : W // IsReflection cs t}

def nReflectionOccurrences (l : List B) (t : cs.T) : ℕ :=
  (cs.leftInvSeq l).count t.1

def parityReflectionOccurrences (l : List B) (t : cs.T) : ZMod 2 :=
  (nReflectionOccurrences cs l t : ZMod 2)

def conj (t : cs.T) (w : W) : cs.T :=
  ⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩

lemma t_eq_conj_t (t : cs.T) : t = cs.conj t t.1 := by
  simp [conj]

def eta (i : B) (t : cs.T) : ZMod 2 :=
  if (s i = t.1) then 1 else 0

lemma eta_simpleConj_eq_eta (i : B) (t : cs.T) : cs.eta i t = cs.eta i (cs.conj t (s i)) := by
  simp [eta]
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

def permutationMap (i : B) : cs.T × ZMod 2 → cs.T × ZMod 2 :=
  fun (t , z) => (cs.conj t (s i), z + cs.eta i t)

theorem permutationMap_orderTwo (i : B) : cs.permutationMap i ∘ cs.permutationMap i = id := by
  funext ⟨t, z⟩
  simp [permutationMap]
  constructor
  · simp[conj, mul_assoc]
  · rw [← cs.eta_simpleConj_eq_eta i t]
    ring_nf
    simp
    right
    rfl

lemma Odd.add_one : Odd n → Even (n + 1) := by
  intro h2
  by_contra h3
  simp at h3
  have contra1 : Even ((n + 1) - n) := by
    apply Nat.Odd.sub_odd h3 h2
  simp at contra1

lemma getElem_alternatingWord (i j : B) (p : ℕ) (k : Fin ((alternatingWord i j p).length)) :
  (alternatingWord i j p)[k] = (if Even (p + k) then i else j) := by
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
      have : k < (alternatingWord i j n).length := by
        simp
        simp at hk
        exact hk
      simp[List.getElem_cons_succ]
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

theorem get_leftInvSeq (l : List B) (j : Fin l.length) :
  (cs.leftInvSeq l).get ⟨j, by simp⟩ =
  cs.wordProd (List.take j l) * s (l.get ⟨j, by simp⟩) * (cs.wordProd (List.take j l))⁻¹ := by

  have h : j < (cs.leftInvSeq l).length := by simp

  rw [← List.getD_eq_get ((cs.leftInvSeq l)) 1 h]
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

lemma nReflectionOccurrences_even_braidWord (t : cs.T) :
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

    rw[List.getElem_append_left this]
    rw[List.getElem_take']
    exact h
  · have h_k_le : k - M i j < M i j := by
      simp at hk
      apply Nat.sub_lt_left_of_lt_add
      simp at h
      exact h
      linarith
    have : (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length ≤ k := by
      simp[h, m_le_two_m]
      linarith

    rw[List.getElem_append_right this]
    rw[List.getElem_take]
    simp[m_le_two_m]

    rw[← leftInvSeq_repeats' cs (k - M i j) h_k_le]

    suffices M.M i j + (k - M.M i j) = k from by
      simp[this]

    rw[← Nat.add_sub_assoc]
    simp
    linarith

lemma parityReflectionOccurrences_braidWord (t : cs.T) :
  parityReflectionOccurrences cs (alternatingWord i j (2 * M i j)) t = 0 := by
  suffices Even (nReflectionOccurrences cs (alternatingWord i j (2 * M i j)) t) from by
    simp[this, parityReflectionOccurrences]
    apply ZMod.eq_zero_iff_even.mpr this
  exact nReflectionOccurrences_even_braidWord cs t

lemma alternatingWord_reverse : (alternatingWord i j (2 * p)).reverse = alternatingWord j i (2 * p) := by
  induction p with
  | zero =>
    simp[alternatingWord]
  | succ p h =>
    simp [alternatingWord]
    rw[h]
    have h1 : j :: i :: alternatingWord j i (2 * p) = alternatingWord j i (2 * p + 1 + 1) := by
      rw[alternatingWord_succ']
      rw[alternatingWord_succ']
      simp
    simp[h1, alternatingWord]

instance instMul : Mul (cs.T × ZMod 2 → cs.T × ZMod 2) where
  mul := fun f g => f ∘ g

lemma mulDef (f g : cs.T × ZMod 2 → cs.T × ZMod 2) : f * g = f ∘ g := rfl

instance : Monoid (cs.T × ZMod 2 → cs.T × ZMod 2) where
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

def permutationMap_ofList (l : List B) : cs.T × ZMod 2 → cs.T × ZMod 2 :=
  match l with
  | [] => id
  | a :: t => cs.permutationMap a * permutationMap_ofList t

lemma IsReflection.conj' (ht : cs.IsReflection t) (w : W) :
  cs.IsReflection (w⁻¹ * t * w) := by
  have : w = w⁻¹⁻¹ := by simp
  nth_rewrite 2 [this]
  apply IsReflection.conj ht w⁻¹

lemma permutationMap_ofList_mk_1 (l : List B) :
  (permutationMap_ofList cs l ⟨t,z⟩).1 = cs.conj t (π l) := by
  simp[conj]
  induction l with
  | nil =>
    simp[permutationMap_ofList, permutationMap, nReflectionOccurrences]
  | cons a l h =>
    calc (permutationMap_ofList cs (a :: l) (t, z)).1 = ((cs.permutationMap a * permutationMap_ofList cs l) (t, z)).1 := by simp[permutationMap_ofList]
      _ = (cs.permutationMap a (permutationMap_ofList cs l (t, z))).1 := by rfl

    simp[permutationMap, conj, h]
    simp[cs.wordProd_cons, mul_assoc]

lemma permutationMap_ofList_mk_2 (l : List B) :
 (permutationMap_ofList cs l ⟨t,z⟩).2 = z + parityReflectionOccurrences cs l.reverse t := by
  induction l with
  | nil =>
    simp[permutationMap_ofList, permutationMap, parityReflectionOccurrences, nReflectionOccurrences]
  | cons i l h =>
    rw[permutationMap_ofList, mulDef]
    simp[permutationMap, h]
    simp[parityReflectionOccurrences, nReflectionOccurrences]
    rw[← List.concat_eq_append]
    rw[leftInvSeq_concat]
    simp [List.count_singleton]

    suffices cs.eta i (permutationMap_ofList cs l (t, z)).1 = if (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1 then 1 else 0 from by
      rw[this]
      simp[add_assoc]

    simp[eta, permutationMap_ofList_mk_1, conj]
    by_cases h' : (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1
    · simp[h']
      rw[← h']
      simp[mul_assoc]
    · simp[h']
      by_contra h''
      rw[h''] at h'
      simp[mul_assoc] at h'

lemma permutationMap_ofList_mk (l : List B) (t : cs.T) (z : ZMod 2) :
  (permutationMap_ofList cs l ⟨t,z⟩) = ⟨cs.conj t (π l),
   z + parityReflectionOccurrences cs l.reverse t⟩ := by
  rw[← permutationMap_ofList_mk_1, ← permutationMap_ofList_mk_2]

theorem permutationMap_isLiftable : M.IsLiftable (cs.permutationMap) := by
  intro i j

  have h (p : ℕ) : (cs.permutationMap i * cs.permutationMap j) ^ p = permutationMap_ofList cs (alternatingWord i j (2 * p)) := by
    induction p with
    | zero =>
      simp[permutationMap_ofList, permutationMap, permutationMap_orderTwo]
      rfl
    | succ p h =>
      simp[pow_succ']
      rw[h]
      have : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
      rw[this]
      rw[alternatingWord_succ']
      rw [if_neg (Nat.not_even_bit1 p)]
      rw[permutationMap_ofList]

      rw[alternatingWord_succ']
      rw [if_pos (even_two_mul p)]
      rw[permutationMap_ofList]
      simp[mul_assoc]

  rw[h (M i j)]
  funext ⟨t, z⟩
  convert_to permutationMap_ofList cs (alternatingWord i j (2 * M.M i j)) (t, z) = ⟨t,z⟩

  simp[permutationMap_ofList_mk, conj]
  constructor
  · simp[cs.prod_alternatingWord_eq_mul_pow]
  · rw[alternatingWord_reverse]
    rw[M.symmetric]
    exact parityReflectionOccurrences_braidWord cs t

def permutationMap_lift : W →* cs.T × ZMod 2 → cs.T × ZMod 2 :=
  cs.lift ⟨cs.permutationMap, permutationMap_isLiftable cs⟩

theorem permutationMap_lift_mk_ofList (l : List B) (t : cs.T) (z : ZMod 2) :
  permutationMap_lift cs (cs.wordProd l) ⟨t,z⟩ = permutationMap_ofList cs l ⟨t,z⟩ := by
  induction l with
  | nil =>
    simp[permutationMap_lift, cs.wordProd_nil, permutationMap_ofList]
    rfl
  | cons i l h =>
    rw[cs.wordProd_cons]
    rw[permutationMap_ofList]
    simp[mulDef]
    rw[← h]
    simp[permutationMap_lift]

theorem permutationMap_ext (l l' : List B) (t : cs.T) (z : ZMod 2) (h : π l = π l') :
  permutationMap_ofList cs l ⟨t,z⟩ = permutationMap_ofList cs l' ⟨t,z⟩ := by
  rw[← permutationMap_lift_mk_ofList]
  rw[← permutationMap_lift_mk_ofList]
  simp[h]

def parityReflectionOccurrences_lift (w : W) (t : cs.T) : ZMod 2 :=
  (permutationMap_lift cs w⁻¹ ⟨t,0⟩).2

theorem parityReflectionOccurrences_lift_mk (l : List B) (t : cs.T) :
  parityReflectionOccurrences_lift cs (cs.wordProd l) t = parityReflectionOccurrences cs l t := by
  rw[parityReflectionOccurrences_lift]
  rw[← wordProd_reverse]
  rw[permutationMap_lift_mk_ofList cs l.reverse t 0]
  rw[permutationMap_ofList_mk cs l.reverse t 0]
  simp

theorem permutationMap_lift_mk (w : W) (t : cs.T) (z : ZMod 2) :
  permutationMap_lift cs w ⟨t,z⟩ = ⟨⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩ , z + parityReflectionOccurrences_lift cs w⁻¹ t⟩ := by
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word' w
  apply Prod.ext
  · simp[permutationMap_lift_mk_ofList, permutationMap_ofList_mk, conj]
  · simp[parityReflectionOccurrences_lift]
    rw[permutationMap_lift_mk_ofList cs l t 0]
    rw[permutationMap_lift_mk_ofList cs l t z]
    simp[permutationMap_ofList_mk]


theorem parityReflectionOccurrences_ext (l l' : List B) (t : cs.T) (h : π l = π l') :
  parityReflectionOccurrences cs l t = parityReflectionOccurrences cs l' t := by

  calc
    parityReflectionOccurrences cs l t = parityReflectionOccurrences_lift cs (cs.wordProd l) t := by rw[parityReflectionOccurrences_lift_mk]
    _ = parityReflectionOccurrences_lift cs (cs.wordProd l') t := by rw[h]
    _ = parityReflectionOccurrences cs l' t := by rw[parityReflectionOccurrences_lift_mk]

lemma odd_iff_parity_eq_one (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  simp [ZMod.eq_one_iff_odd]

lemma gt_one_of_odd (n : ℕ) : Odd n → n > 0 := by
  intro h
  simp[Odd] at h
  rcases h with ⟨m, rfl⟩
  suffices m ≥ 0 from by linarith
  exact Nat.zero_le m

lemma isInLeftInvSeq_of_parityReflectionOccurrences_eq_one (l : List B) (t : cs.T) (h : parityReflectionOccurrences cs l t = 1) :
  t.1 ∈ cs.leftInvSeq l := by
  simp [parityReflectionOccurrences] at h
  rw [← @odd_iff_parity_eq_one (nReflectionOccurrences cs l t)] at h

  apply gt_one_of_odd (nReflectionOccurrences cs l t) at h
  simp[nReflectionOccurrences] at h

  exact h

lemma isLeftInversion_of_parityReflectionOccurrences_eq_one (l : List B) (t : cs.T) :
  parityReflectionOccurrences cs l t = 1 → cs.IsLeftInversion (cs.wordProd l) t.1 := by
  intro h

  rcases cs.exists_reduced_word' (π l) with ⟨u, u_reduced, hu⟩
  rw[hu]
  apply cs.isLeftInversion_of_mem_leftInvSeq u_reduced

  rw[cs.parityReflectionOccurrences_ext l u t hu] at h
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs u t h

lemma isLeftInversion_of_parityReflectionOccurrences_lift_eq_one (w : W) (t : cs.T) :
  parityReflectionOccurrences_lift cs w t = 1 → cs.IsLeftInversion w t.1 := by
  intro h
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word' w
  simp[parityReflectionOccurrences_lift_mk] at h
  apply isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t h

lemma eraseIdx_of_mul_leftInvSeq (l : List B) (t : cs.T) (h : t.1 ∈ cs.leftInvSeq l) :
  ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by
    have : ∃ (k : Fin (cs.leftInvSeq l).length), (cs.leftInvSeq l).get k = t.1 := List.get_of_mem h
    rcases this with ⟨k, hk⟩
    use ⟨k, by rw[← length_leftInvSeq cs l] ; exact k.2⟩
    rw[← hk]
    rw[← getD_leftInvSeq_mul_wordProd cs l k]
    simp
    rw[← List.get?_eq_getElem?]
    rw [List.get?_eq_get k.2]
    simp

lemma permutationMap_lift_simple (p : B):
  permutationMap_lift cs (cs.simple p) = cs.permutationMap p := by
  simp[permutationMap_lift]

lemma permutationMap_lift_of_reflection (t : cs.T) : ∀ (z : ZMod 2),
  permutationMap_lift cs t.1 (t, z) = ⟨t, z + 1⟩ := by
  rcases t with ⟨t, t_refl⟩
  rcases t_refl with ⟨w, p, rfl⟩
  obtain ⟨l, _, rfl⟩ := cs.wordProd_surjective w
  have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) := IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)

  induction l with
  | nil =>
    simp[permutationMap_lift, permutationMap_ofList, permutationMap, nReflectionOccurrences, conj, eta]
  | cons i l h =>
    intro z
    simp_rw[wordProd_cons cs i l]
    simp_rw[mul_inv_rev]
    simp_rw[inv_simple]
    simp[permutationMap_lift_simple, mulDef, ← mul_assoc]
    simp[permutationMap_lift_simple, mulDef] at h
    nth_rewrite 3 [permutationMap]
    simp[conj, ← mul_assoc]
    have : IsReflection cs (cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i) := by
      nth_rewrite 3 [← inv_simple]
      have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) := IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)
      convert_to IsReflection cs (cs.simple i * (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) * (cs.simple i)⁻¹)
      simp[inv_simple, mul_assoc]
      exact IsReflection.conj this (s i)
    rw[h (isReflection_simple cs p) (z + cs.eta i ⟨cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i, this⟩)]
    simp[permutationMap, conj]
    constructor
    · simp[mul_assoc]
    · simp[eta, add_assoc]
      by_cases h': cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ = 1
      · simp[h']
        have : cs.simple i = cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ := by
          apply (mul_right_inj (cs.simple i)).mpr at h'
          simp only[mul_assoc, mul_one] at h'
          rw[← h']
          simp[mul_assoc]
        simp[this]
        simp[ZMod]
      · simp[h']
        by_contra h''
        rw[h''] at h'
        simp[mul_assoc] at h'

lemma isLeftInversion_iff_parityReflectionOccurrences_eq_one (l : List B) (t : cs.T) :
  cs.IsLeftInversion (cs.wordProd l) t.1 ↔ parityReflectionOccurrences cs l t = 1 := by
  constructor
  · intro h
    by_contra h'
    have h'' : parityReflectionOccurrences cs l t = 0 := by
      simp [parityReflectionOccurrences]
      rw [ZMod.eq_zero_iff_even]
      simp[parityReflectionOccurrences] at h'
      rw[ZMod.eq_one_iff_odd] at h'
      exact Nat.not_odd_iff_even.mp h'

    suffices cs.IsLeftInversion (t.1 * π l) t.1 from by
      simp[IsLeftInversion] at this
      rw[← mul_assoc] at this
      rcases this with ⟨_, ht⟩
      rw[IsReflection.mul_self t.2] at ht
      simp at ht
      simp[IsLeftInversion] at h
      linarith

    suffices permutationMap_lift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ = ⟨cs.conj t (π l)⁻¹, 1⟩ from by
      apply isLeftInversion_of_parityReflectionOccurrences_lift_eq_one cs (t.1 * π l) t
      rw[permutationMap_lift_mk cs (t.1 * π l)⁻¹ t 0] at this
      simp at this
      simp[this.2]

    calc
      permutationMap_lift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ = permutationMap_lift cs (π l)⁻¹ (permutationMap_lift cs t.1 ⟨t, 0⟩) := by
          simp[IsReflection.inv t.2]
          rfl
      _ = permutationMap_lift cs (π l)⁻¹ ⟨t, 1⟩ := by
          rw[permutationMap_lift_of_reflection cs t 0]
          simp[permutationMap_lift_mk]
      _ = ⟨cs.conj t (π l)⁻¹, 1 + parityReflectionOccurrences_lift cs (π l) t⟩ := by
        simp[permutationMap_lift_mk, conj]
      _ = (cs.conj t (cs.wordProd l)⁻¹, 1) := by
        simp
        simp[parityReflectionOccurrences_lift_mk, h'']

  · exact isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t


theorem strongExchangeProperty (l : List B) (t : cs.T)
(h' : cs.IsLeftInversion (cs.wordProd l) t.1) :
  ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by

  suffices t.1 ∈ cs.leftInvSeq l from eraseIdx_of_mul_leftInvSeq cs l t this

  rw [isLeftInversion_iff_parityReflectionOccurrences_eq_one cs l t] at h'
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs l t h'
