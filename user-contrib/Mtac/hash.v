Require Import mtacore.
Require Import Arith Lists.List NArith.
Import ListNotations.

Import MtacNotations.

Module ListMtactics.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition inlist {A} (x : A) :=
    mfix f (s : list A) :=
      mmatch s with
      | [l r] l ++ r =>
        mtry 
          il <- f l;
          ret (in_or_app l r x (or_introl il))
        with NotFound =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [s'] (x :: s') => ret (in_eq _ _)
      | [y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y _ _ r)
      | _ => raise NotFound
      end.
    
  Program
  Definition find {A} {B : A -> Type} (x : A) :=
    mfix f (s : list (sigT B)) :=
      mmatch s with
      | [l r] l ++ r => 
        mtry 
          f l
        with NotFound =>
          f r
        end
      | [y s'] (existT B x y :: s') => ret y
      | [y s'] (y :: s') => f s'
      | _ => raise NotFound
      end.

End ListMtactics.

Module HashTbl.
  

  Definition t A (P : A -> Type) := (Ref N * Ref (Array.t (list (sigT P))))%type.

  Definition initial_size := 16%N.
  Definition inc_factor := 2%N.
  Definition threshold := 7%N.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition create A B : M (t A B) :=
    n <- ref 0%N;
    a <- Array.make initial_size nil;
    ra <- ref a;
    ret (n, ra).

  
  Definition quick_add {A P} (a : Array.t (list (sigT P))) (x : A) (y : P x) : M unit :=
    n <- Array.length a;
    i <- hash x n;
    l <- Array.get a i;
    Array.set a i (existT _ x y  :: l).
  
  Definition iter {A B} (h : t A B) (f : forall x : A, B x -> M unit) : M unit :=
    let (_, ra) := h in
    a <- !ra;
    Array.iter a (fun _ l =>
      fold_right (fun k r => r;;
         match k with
           existT x y => f x y
         end) (ret tt) l).

  Definition expand {A B} (h : t A B) : M unit :=
    let (_, ra) := h in
    a <- !ra;
    size <- Array.length a;
    let new_size := (size * inc_factor)%N in
    new_a <- Array.make new_size nil;
    iter h (fun x y=> quick_add new_a x y);;
    ra ::= new_a.
        

  (* There is no order on the elements *)
  Definition to_list {A B} (h : t A B) :=
    rl <- ref nil;
    HashTbl.iter h (fun x y => l <- !rl; rl ::= (existT _ x y :: l));;
    !rl.

  (* debugging function to test how big is the biggest bucket *)
  Definition max_bucket {A B} (h : t A B) :=
    let (_, ra) := h in
    a <- !ra;
    max <- ref 0;
    Array.iter a (fun _ l => 
        prev <- !max;
        let size := length l in
        if leb prev size then
          max ::= size
        else
          ret tt);;
    !max.
    

  Definition add {A B} (h : t A B) (x : A) (y : B x) :=
    let (rl, ra) := h in
    load <- !rl;
    a <- !ra;
    size <- Array.length a;
    (if (threshold * size <=? 10 * load)%N then
      expand h
    else
      ret tt);;
    a <- !ra;
    quick_add a x y;;
    new_load <- retS (N.succ load);
    rl ::= new_load.

  Definition find {A B} (h : t A B) (x : A) : M (B x) :=
    x' <- ret x;
    let (_, ra) := h in
    a <- !ra;
    size <- Array.length a;
    i <- hash x' size;
    l <- Array.get a i;
    mtry
      ListMtactics.find x l
    with ListMtactics.NotFound =>
      raise NotFound
    end.

  
End HashTbl.
