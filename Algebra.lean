/- Definition of a Group -/

class Group (G : Type u) :=
  mul : G → G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one : G
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv : G → G
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

class Abelian_Group (G : Type u) extends Group G :=
  mul_com : ∀ a b : G, mul a b = mul b a

infixl:70    " * "   => Group.mul
notation:max " e "   => Group.one
postfix:max  " ⁻¹ "  => Group.inv

/- Some Examples of Groups -/

namespace Examples

inductive pm : Type :=
  | p : pm
  | m : pm

def pm.mul : pm → pm → pm 
  | p, p => p
  | p, m => m
  | m, p => m
  | m, m => p

theorem pm.mul_assoc : ∀ a b c : pm, mul (mul a b) c = mul a (mul b c) 
  | p, p, p => by simp [pm.mul]
  | p, p, m => by simp [pm.mul]
  | p, m, p => by simp [pm.mul]
  | p, m, m => by simp [pm.mul]
  | m, p, p => by simp [pm.mul]
  | m, p, m => by simp [pm.mul]
  | m, m, p => by simp [pm.mul]
  | m, m, m => by simp [pm.mul]

theorem pm.one_mul : ∀ a : pm, mul p a = a 
  | p => by simp [pm.mul]
  | m => by simp [pm.mul]

theorem pm.mul_one : ∀ a : pm, mul a p = a 
  | p => by simp [pm.mul]
  | m => by simp [pm.mul]

def pm.inv : pm → pm 
  | p => p
  | m => m

theorem pm.inv_mul : ∀ a : pm, mul (inv a) a = p
  | p => by simp [pm.inv, pm.mul]
  | m => by simp [pm.inv, pm.mul]

theorem pm.mul_inv : ∀ a : pm, mul a (inv a) = p
  | p => by simp [pm.inv, pm.mul]
  | m => by simp [pm.inv, pm.mul]

theorem pm.mul_com : ∀ a b : pm, mul a b = mul b a
  | p, p => by simp [pm.mul]
  | p, m => by simp [pm.mul]
  | m, p => by simp [pm.mul]
  | m, m => by simp [pm.mul]

instance : Abelian_Group pm where
    mul := pm.mul
    mul_assoc := pm.mul_assoc
    one := pm.p
    one_mul := pm.one_mul
    mul_one := pm.mul_one
    inv := pm.inv
    inv_mul := pm.inv_mul
    mul_inv := pm.mul_inv
    mul_com := pm.mul_com

end Examples

namespace Examples

inductive nat : Type :=
  | zero : nat
  | succ : nat → nat

def nat.add : nat → nat → nat 
  | a, nat.zero   => a
  | a, nat.succ b => nat.succ (add a b)

theorem nat.add_assoc : ∀ a b c : nat, add (add a b) c = add a (add b c)
  | a, b, zero   => by rw [add, add]
  | a, b, succ n => by simp [add, add_assoc]

theorem nat.zero_add : ∀ a : nat, add zero a = a 
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]

theorem nat.succ_add : ∀ a b : nat, add (succ a) b = succ (add a b)
  | a, zero   => by simp [add]
  | a, succ n => by simp [add, succ_add]

theorem nat.add_com : ∀ a b : nat, add a b = add b a 
  | a, zero => by simp [add, zero_add]
  | a, succ n => by simp [add, succ_add, add_com a n]

def nat.pred : nat → nat 
  | nat.zero   => nat.zero
  | nat.succ n => n

def nat.sub : nat → nat → nat 
  | a, nat.zero   => a
  | a, nat.succ b => pred (sub a b)

inductive int : Type :=
  | ofnat : nat → int
  | nsucc : nat → int

def int.sub_nat (m n : nat) : int :=
  match (nat.sub n m : nat) with 
  | nat.zero   => int.ofnat (nat.sub m n)
  | nat.succ k => int.nsucc k

def int.add : int → int → int
  | ofnat m, ofnat n => int.ofnat (nat.add m n)
  | ofnat m, nsucc n => int.sub_nat m (nat.succ n)
  | nsucc m, ofnat n => int.sub_nat n (nat.succ m)
  | nsucc m, nsucc n => int.nsucc (nat.add m n)




end Examples



/- Some Preliminary Lemmas -/

namespace Group
variable {G : Type u} [Group G]

theorem unique_one_l {e' : G} (h : ∀ x : G, e' * x = x) : e' = e := calc
  e' = e' * e := by rw [mul_one]
  _  = e      := by rw [h]


theorem unique_one_r {e' : G} (h : ∀ x : G, x * e' = x) : e' = e := calc
  e' = e * e' := by rw [one_mul]
  _  = e      := by rw [h]

theorem unique_inv_l {a b : G} (h : b * a = e) : b = a⁻¹ := calc
  b = b * e         := by rw [mul_one]
  _ = b * (a * a⁻¹) := by rw [mul_inv]
  _ = (b * a) * a⁻¹ := by rw [mul_assoc]
  _ = e * a⁻¹       := by rw [h]
  _ = a⁻¹           := by rw [one_mul]

theorem unique_inv_r {a b : G} (h : a * b = e) : b = a⁻¹ := calc
  b = e * b         := by rw [one_mul]
  _ = (a⁻¹ * a) * b := by rw [inv_mul]
  _ = a⁻¹ * (a * b) := by rw [mul_assoc]
  _ = a⁻¹ * e       := by rw [h]
  _ = a⁻¹           := by rw [mul_one] 

theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
  have h₁ : a * a⁻¹ = e := mul_inv a
  have h₂ : a = (a⁻¹)⁻¹ := unique_inv_l h₁
  show (a⁻¹)⁻¹ = a from h₂.symm  

theorem prod_inv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  have h₁ : (a * b) * (b⁻¹ * a⁻¹) = e := calc
    (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by simp [mul_assoc]
    _                     = e                   := by simp [mul_inv, mul_one, mul_inv]
  have h₂ : (b⁻¹ * a⁻¹) = (a * b)⁻¹ := unique_inv_r h₁
  show (a * b)⁻¹ = b⁻¹ * a⁻¹ from h₂.symm

theorem left_cancel {a b x : G} (h : a * x = b) : x = a⁻¹ * b := calc
  x = e * x         := by rw [one_mul]
  _ = (a⁻¹ * a) * x := by rw [inv_mul]
  _ = a⁻¹ * (a * x) := by rw [mul_assoc]
  _ = a⁻¹ * b       := by rw [h]

theorem right_cancel {a b x : G} (h : x * a = b) : x = b * a⁻¹ := calc
  x = x * e         := by rw [mul_one]
  _ = x * (a * a⁻¹) := by rw [mul_inv]
  _ = (x * a) * a⁻¹ := by rw [mul_assoc]
  _ = b * a⁻¹       := by rw [h]

end Group

