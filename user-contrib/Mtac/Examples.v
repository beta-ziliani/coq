Require Import mtac.

Set Printing Existential Instances.
Definition test1 := run (
  mmatch id 0 with
  | [f (x : nat)] f x =m> ret true
  end
).

Print test1.


Set Implicit Arguments.

Structure dyn := Dyn { ty : Type; el : ty }.
Require Import Lists.List.
Import ListNotations.
Definition remove {A} (x : A) :=
  mfix f (s : list A) :=
    mmatch s with
    | [s'] (x :: s') =m> f s'
    | [y s'] (y :: s') =m> 
      r <- f s';
      ret (y :: r)
    | _ => ret s
    end.

Definition fv :=
  mfix fv (d : dyn) : M (list dyn) :=
    mmatch d with
    | [B C (f : B -> C)] Dyn (fun y:B => f y) =m>
      nu (y : B),
        f' <- retS (f y);
        r <- fv (Dyn f');
        remove (Dyn y) r
    | [A B (x:A) (f : A -> B)] Dyn (f x) =m>
      r1 <- fv (Dyn f);
      r2 <- fv (Dyn x);
      ret (r1 ++ r2) 
    | [A (x:A)] Dyn x =m>
      b <- is_var x;
      if b then ret [ Dyn x ]
      else ret []
    end.

Definition test_fv1 : (run (fv (Dyn (fun x:nat=>x)))) = [] := eq_refl _.

Definition test_fv2 (y:nat) : (run fv (Dyn (fun x:nat=>y))) = [Dyn y] := eq_refl _.

Definition test_fv3 (y:nat) : (run fv (Dyn (fun x:nat->nat=>x y))) = [Dyn y] := eq_refl _.

Definition test_fv4 (y:nat) : (run fv (Dyn (fun x:nat->nat=> plus (x y)))) = [Dyn y] := eq_refl _.

Definition test_fv5 (y:nat) : 
  (run fv (Dyn (fun x:nat => x > y))) = [Dyn y] := eq_refl _.
