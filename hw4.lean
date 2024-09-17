-- Math 494 Homework #4
-- Rodolfo Lopez
@[derive decidable_eq]
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

def one : mynat := succ zero

theorem one_eq_succ_zero : one = succ zero := rfl

lemma zero_ne_succ (m : mynat) : (zero : mynat) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : mynat} (h : succ m = succ n) : m = n := by cases h; refl

attribute [symm] ne.symm

def add : mynat → mynat → mynat
| m zero := m
| m (succ n) := succ (add m n)

instance : has_add mynat := ⟨mynat.add⟩

lemma add_zero (m : mynat) : m + zero = m := rfl

lemma add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

def mul : mynat → mynat → mynat
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul mynat := ⟨mul⟩

lemma mul_zero (m : mynat) : m * zero = zero := rfl

lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m := rfl

/- -----------------------------------------------------------
---------------- BEGINNING OF HOMEWORK -----------------------
----------------------------------------------------------- -/

lemma zero_add (n : mynat) : zero + n = n :=
begin
induction n with d hd,
{
  rw add_zero,
},
{
  rw add_succ,
  rw hd,
}
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
induction c with d hd,
{ 
  rw add_zero,
  rw add_zero,
},
{ 
  rw add_succ,
  rw add_succ,
  rw add_succ,
  rw hd,
}
end

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
induction b with d hd,
{
  refl,
}, 
{ 
  rw add_succ,
  rw hd,
  rw add_succ,
}
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin
induction b with d hd,
{ 
  rw zero_add,
  rw add_zero,
},
{ 
  rw add_succ,
  rw hd,
  rw succ_add,
}
end

theorem succ_eq_add_one (n : mynat) : succ n = n + one :=
begin
  rw one_eq_succ_zero,
  rw add_succ,
  rw add_zero,
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
end

lemma zero_mul (m : mynat) : zero * m = zero :=
begin
induction m with d hd,
{
  rw mul_zero,
},
{
  rw mul_succ,
  rw hd,
  rw add_zero,
}
end

lemma mul_one (m : mynat) : m * one = m :=
begin
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
end

lemma one_mul (m : mynat) : one * m = m :=
begin
induction m with d hd,
{
  rw mul_zero,
},
{
  rw mul_succ,
  rw hd,
  rw succ_eq_add_one,
}
end

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin
induction b with d hd,
{ 
  rw add_zero, 
  rw mul_zero, 
  rw add_zero,
  --rewrite [add_zero, mul_zero, add_zero]
},
{
  rw add_succ,
  rw mul_succ,
  rw hd,
  rw mul_succ,
  rw add_assoc, 
}
end

def left_distrib := mul_add -- the "proper" name for this lemma

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
induction c with d hd,
{ 
  rw mul_zero,
  rw mul_zero,
  rw mul_zero,
  --repeat {rw mul_zero}
},
{
  rw mul_succ,
  rw mul_succ,
  rw hd,
  rw mul_add,
}
end

lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin
induction b with d hd,
{
  rw mul_zero,
  rw mul_zero,
  rw add_zero,
},
{
  rw mul_succ,
  rw mul_succ,
  rw hd,
  rw add_succ,
  rw add_succ,
  rw add_right_comm,
}
end

lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
induction b with d hd,
{ 
  rw zero_mul,
  rw add_zero,
  rw add_zero,
},
{
  rw add_succ,
  rw succ_mul,
  rw hd,
  rw succ_mul,
  rw add_assoc,
}
end

def right_distrib := add_mul -- alternative name

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
induction b with d hd,
{ 
  rw zero_mul,
  rw mul_zero,
},
{
  rw succ_mul,
  rw ←hd,
  rw mul_succ,
}
end

lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc,
  rw mul_comm a, 
  rw mul_assoc,
end

end mynat
