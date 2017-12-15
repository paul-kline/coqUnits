Module Type Nums. 
 Parameter NumType : Set. 
 Parameter mult : NumType -> NumType -> NumType.  
 Parameter div : NumType -> NumType -> NumType.  
 Parameter add : NumType -> NumType -> NumType.
 Parameter minus : NumType -> NumType -> NumType.

 Parameter PI : NumType.
 Parameter natToNum : (nat -> NumType).
End Nums.

(*
The nat implementation of everything we need.
*) 
Module Nats <: Nums.
  Import Nat. 
  Definition NumType := nat.
  Definition add := Nat.add. 
  Fixpoint minus (x y : nat) := 
  match (x,y) with 
    | (_,0) => x
    | (0,_) => 0
    | (S x', S y') => minus x' y'
  end. 
  Eval compute in (minus 5 2).
  Definition mult := Nat.mul.
  Definition div := Nat.div.
  Definition PI := 3.
   
Definition natToNum := fun x : nat => x. 
End Nats.