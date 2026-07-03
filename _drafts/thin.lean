--import Init.Data.List.Count
import Plausible

abbrev Thin := List Bool

def dom (t : Thin) : Nat := t.length

@[simp] theorem dom_nil : dom [] = 0 := by rfl
@[simp] theorem dom_cons x xs : dom (x :: xs) = dom xs + 1 := by rfl



def cod (t : Thin) : Nat := t.count true

@[simp]
def cod_false xs : cod (false :: xs) = cod xs := by rfl

@[simp]
def cod_true xs : cod (true :: xs) = cod xs + 1 := by simp [cod]

@[simp] theorem cod_nil : cod [] = 0 := by rfl

/-
theorem cod_cons xs : cod (true :: xs) = cod xs + 1 := by
  unfold cod
  simp
-/


-- cod + 1 vs 1 + cod made a big idfference
/-
theorem cod_cons_true xs : cod (true :: xs) = cod xs + 1 := by
  simp -- [cod]
theorem cod_cons_false xs : cod (false :: xs) = cod xs := by simp
-/

/-
def comp (t : Thin) (g : Thin) : Option Thin :=
  match t, g with
  | true :: rs, x :: gs => (comp rs gs).mapM (fun res => x :: res)
  | false :: rs, _ => (comp rs g).mapM (fun res => false :: res)
  | true :: rs, [] => none
  | [], [] => some []
  | [], _ => none

def comp : Thin → Thin → Option Thin
  | true :: rs, x :: gs => do
      pure (x :: (← comp rs gs))
  | false :: rs, g => do
      pure (false :: (← comp rs g))
  | [], [] => some []
  | _, _ => none
-/

def comp : Thin → Thin → Option Thin
  | true  :: rs, x :: gs => (x :: ·) <$> comp rs gs
  | false :: rs, g       => (false :: ·) <$> comp rs g
  | [],        []        => some []
  | _,         _         => none

def comp_isSome_iff f g : cod f = dom g -> (comp f g).isSome := by
  induction f with
  | nil => cases g with
          | nil => simp [comp]
          | cons x xs => simp
  | cons x xs ih => sorry


def idthin (n : Nat) := List.replicate n true

@[simp]
def idthin_zero : idthin 0 = [] := by rfl

@[simp]
def idthin_succ n : idthin (n + 1) = true :: idthin n := by rfl

@[simp]
theorem comp_id t : comp t (idthin (cod t)) = some t := by
  induction t with
  | nil => rfl
  | cons x xs ih => cases x with
                    | false => simpa [comp] --simpa [cod, comp] using ih
                    | true => simpa [comp]

@[simp]
theorem id_comp t : comp (idthin (dom t)) t = some t := by
  induction t with
  | nil => rfl
  | cons x xs ih => simpa [comp]


theorem comp_nil f : cod f = 0 -> comp f [] = some f := by
  intro h
  have h1 : idthin (cod f) = [] := by rw [h]; simp
  rw [<- h1]
  simp


theorem comp_nil_wrong f : cod f = 0 -> comp f [] = some [] := by
  plausible
  sorry



/-
  induction f with
  | nil => simp [comp]
  | cons x xs ih => cases x with
                    | true => simp
                    | false =>
                    -/





-- comp_assoc : comp f (comp g h) = comp (comp f g) h
