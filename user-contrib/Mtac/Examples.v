Require Import mtac.

(* Set Printing Existential Instances. *)

Definition test1 := run (
  mmatch id 0 with
  | [f (x : nat)] f x =m> ret true
  end
).

Print test1.

Set Implicit Arguments.


Definition test1Step1 := run (retO ((fun x y:nat=> x + y) 1 2)).
Definition test1Step2 := run (retO (1 + 2)).
Definition test1Step3 := let f := fun x:nat=>x in run retO (f 0).


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
    | _ =m> ret s
    end.

Definition fv :=
  mfix fv (d : dyn) : M (list dyn) :=
    mmatch d with
    | [B C (f : B -> C)] Dyn (fun y:B => f y) =m>
      nu (y : B),
        f' <- retO (f y);
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

Definition test_fv6 (y w:nat) : 
  (run fv (Dyn (fun x z:nat => x > y /\ y > z /\ w > z))) = [Dyn y; Dyn y; Dyn w] := eq_refl _.



Definition mtest := fun f : nat -> nat =>
                       mmatch f with
                       | [g : nat -> nat] (fun x : nat=> g x) =m> ret (g 0)
                       | _ => raise exception
                       end.
Definition ctest := fun f : nat -> nat =>
                       mmatch f with
                       | [g : nat -> nat] (fun x : nat=> g x) => ret (g 0)
                       | _ => raise exception
                       end.
Check (run (mtest (plus 0))).
Check (run (ctest (plus 0))).

(* 1.  plus 0  ~=  fun x : nat => ?g[] x 
   2.  fun m : nat => match 0 with 0 => m | .... end  ~=  fun x: nat => ?g[] x
   3.  m : nat |- match 0 with 0 => m | S p => (plus p m) end  ~=   ?g[] m
   4.  ?g[] := match 0 with 0 => m | S p => (plus p m) end
*)

Require Import Program.

Module WithList.

  Definition dyn := { x : Prop | x}.
  Definition Dyn := @exist Prop (fun p=>p).

  Definition ProofNotFound : Exception.
    exact exception.
  Qed.

  Program
  Definition lookup (p : Prop)  := 
    mfix f (s : list dyn) : M p :=
      mmatch s return M p with
      | [x s'] (@Dyn p x) :: s' => ret x
      | [d s'] d :: s' => f s'
      | _ => raise ProofNotFound
      end.
  
  Program
  Definition tauto' :=
    mfix f (c : list dyn) (p : Prop) : M p :=
      mmatch p as p' return M p' with
      | True => ret I 
      | [p1 p2] p1 /\ p2 =>
           r1 <- f c p1 ;
           r2 <- f c p2 ;
           ret (conj r1 r2)
      | [p1 p2]  p1 \/ p2 =>
           mtry 
             r1 <- f c p1 ;
             ret (or_introl r1)
           with _ =>
             r2 <- f c p2 ;
             ret (or_intror r2)
           end
      | [p1 p2 : Prop] p1 -> p2 =>
           nu (x:p1),
             r <- f (@Dyn p1 x :: c) p2;
             abs x r
      | [A (q:A -> Prop)] (forall x:A, q x) =>
           nu (x:A),
             r <- f c (q x);
             abs x r
      | [A (q:A -> Prop)] (exists x:A, q x) =>
           X <- evar A;
           r <- f c (q X);
           b <- is_evar X;
           if b then 
             raise ProofNotFound
           else
             ret (ex_intro q X r)
      | [p':Prop] p' => lookup p' c
      end.
  
  Definition tauto P := 
    tauto' nil P.

End WithList.


Require Import hash.
Module WithHash.

  Definition ProofNotFound : Exception.
    exact exception.
  Qed.

  Definition ctx := HashTbl.t Prop (fun x=>x).

  Program
  Definition tauto' (c : ctx) :=
    mfix f (p : Prop) : M p :=
    mmatch p as p' return M p' with
    | True => ret I 
    | [p1 p2] p1 /\ p2 =>
         r1 <- f p1 ;
         r2 <- f p2 ;
         ret (conj r1 r2)
    | [p1 p2]  p1 \/ p2 =>
         mtry 
           r1 <- f p1 ;
           ret (or_introl r1)
         with _ =>
           r2 <- f p2 ;
           ret (or_intror r2)
         end
    | [p1 p2 : Prop] p1 -> p2 =>
         nu (x:p1),
           HashTbl.add c p1 x;;
           r <- f p2;
           abs x r
    | [A (q:A -> Prop)] (forall x:A, q x) =>
         nu (x:A),
           r <- f (q x);
           abs x r
    | [x:Prop] x => 
      mtry HashTbl.find c x
      with _ => raise ProofNotFound
      end
    end.

  Definition tauto P := 
    c <- HashTbl.create Prop (fun x=>x);
    tauto' c P.

End WithHash.


Module WithCT.

  Definition dyn := { x : Prop | x}.
  Definition Dyn := @exist Prop (fun p=>p).

  Definition ProofNotFound : Exception.
    exact exception.
  Qed.

Definition Ctx := list Type.
Definition CtxSet := list Set.
Coercion CtxCoerce := map (fun (s: Set) => (s:Type)) : CtxSet -> Ctx.

Inductive Subst : Ctx -> Type :=
| snil : Subst nil
| scons A C : A -> Subst C -> Subst (A::C).

  Record CT C (P: Type) : Type := cp { cProof : Subst C -> P }.

  Definition nu' : forall C A B, (A -> CT (A :: C) B) -> M (CT (A :: C) B) := 
    fun C A B f => nu x, 
      ret (cp (fun s=>(cProof (f x) s))).

  Program
  Definition lookup (p : Prop)  := 
    mfix f (s : list dyn) : M p :=
      mmatch s return M p with
      | [x s'] (@Dyn p x) :: s' => ret x
      | [d s'] d :: s' => f s'
      | _ => raise ProofNotFound
      end.
  
  Program
  Definition tauto' :=
    mfix f (c : list dyn) (p : Prop) : M p :=
      mmatch p as p' return M p' with
      | True => ret I 
      | [p1 p2] p1 /\ p2 =>
           r1 <- f c p1 ;
           r2 <- f c p2 ;
           ret (conj r1 r2)
      | [p1 p2]  p1 \/ p2 =>
           mtry 
             r1 <- f c p1 ;
             ret (or_introl r1)
           with _ =>
             r2 <- f c p2 ;
             ret (or_intror r2)
           end
      | [p1 p2 : Prop] p1 -> p2 =>
           nu (x:p1),
             r <- f (@Dyn p1 x :: c) p2;
             abs x r
      | [A (q:A -> Prop)] (forall x:A, q x) =>
           nu (x:A),
             r <- f c (q x);
             abs x r
      | [A (q:A -> Prop)] (exists x:A, q x) =>
           X <- evar A;
           r <- f c (q X);
           b <- is_evar X;
           if b then 
             raise ProofNotFound
           else
             ret (ex_intro q X r)
      | [p':Prop] p' => lookup p' c
      end.
  
  Definition tauto P := 
    tauto' nil P.

End WithCT.



Example ex_first_order_0 : 
  forall x (p q : nat -> Prop), exists y, p x -> q x -> p y /\ q y.
Proof. 
  refine (run (WithList.tauto _)).
Qed.

Example ex_first_order_2 (p q r : Prop) : 
  q -> p -> q.
Proof. 
  refine (run (WithHash.tauto _)).
Qed.

Example ex_first_order_2'  : 
  forall (p q : nat -> Prop) x , p x -> q x -> p x /\ q x.
Proof. 
  refine (run (WithHash.tauto _)).
Qed.



Structure dummy := Dummy {
                       value : nat
                     }.

Canonical Structure dummy0 := Dummy 0.

Canonical Structure dummyS (d : dummy) := Dummy (S (value d)).

Definition testDummyCS n :=
  mmatch n with
  | [d] value d =m> ret d
  | _ => raise exception
  end.

Check (run (testDummyCS 2)).




Definition let_unification :=
  e <- evar nat;
  mmatch let x := e in S x with
  | let y := 1 in y =m> ret e
  end.

Check (run let_unification).



Structure testSort (d : Type) := TestSort { atype : Type }.

Canonical Structure testProp := TestSort Prop Prop.
Canonical Structure testProd c d a b := TestSort (c->d) (@atype c a -> @atype d b).
Canonical Structure testSet := TestSort Set Set.
Canonical Structure testType := TestSort Type Type.

Program
Definition checkSort (n : Type) :=
  mmatch n return M (sigT (fun a=>testSort a)) with
  | [(a:Type) (d: testSort a)] @atype a d =m> ret (@existT _ _ a d)
  | _ => raise exception
  end.

Check (run (checkSort Prop)).
Check (run (checkSort Type)).
Check (run (checkSort Set)).
Check (run (checkSort (Set -> Prop))).

Canonical Structure testDef x := TestSort x x.

Check (run (checkSort ((fun x : nat=>Prop) 0))).



Structure testFun (d : Type) := TestFun { afuntype : Type }.

Canonical Structure testFProp (x : Type) := TestFun Prop x.


Program
Definition checkFun (f : Type) :=
  mmatch f with
  | [(a:Type) (d: testFun a)] @afuntype a d =m> ret (@existT _ _ a d)
  | _ => raise exception
  end.

Check (run (checkFun Set)).
