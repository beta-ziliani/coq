open Term
open Termops
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure
open Util
open Evarconv
open Libnames

let reduce_value : Reductionops.reduction_function ref = ref (fun _ _ c ->c)

module Constr = struct
  let mkConstr name = lazy (constr_of_global (Nametab.global_of_path (path_of_string name)))

  let isConstr = fun r c -> eq_constr (Lazy.force r) c
end

module MtacNames = struct
  let mtacore_name = "Mtac.mtacore"
  let mtac_module_name = mtacore_name ^ ".Mtac"
  let mkLazyConstr = fun e-> Constr.mkConstr (mtac_module_name ^ "." ^ e)
  let mkConstr = fun e-> Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e))
  let mkT_lazy = lazy (mkConstr "Mtac")

  let mkBase = mkLazyConstr "base"
  let mkTele = mkLazyConstr "tele"

  let isBase = Constr.isConstr mkBase
  let isTele = Constr.isConstr mkTele

end

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons
end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  exception NotANat

  let from_coq env evd c =
    let rec fc c = 
      if isZero c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
	    raise NotANat
        end
    in
    let c' = !reduce_value env evd c in
    fc c'
     
end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO
  
  exception NotAPositive

  let from_coq env evd c =
    let rec fc i c =
      if isH c then
        1
      else 
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
	    raise NotAPositive
        end
    in
    let c' = !reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  exception NotAN

  let from_coq env evd c =
    let rec fc c = 
      if is0 c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq env evd (n.(0))
          else
	    raise NotAN
        end
    in
    let c' = !reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end 

module CoqAscii = struct

  let from_coq env sigma c =
    let (h, args) = whd_betadeltaiota_stack env sigma c in
    let rec from_bits n bits =
      match bits with
        | [] -> 0
        | (b :: bs) -> (if CoqBool.isTrue b then 1 else 0) lsl n + from_bits (n+1) bs
    in 
    let n = from_bits 0 args in
    Char.escaped (Char.chr n)

end 

module CoqString = struct

  let mkEmpty = Constr.mkConstr "Coq.Strings.String.EmptyString"
  let mkString = Constr.mkConstr "Coq.Strings.String.String"

  let isEmpty = Constr.isConstr mkEmpty
  let isString = Constr.isConstr mkString

  exception NotAString

  let rec from_coq env sigma s =
    let (h, args) = whd_betadeltaiota_stack env sigma s in
    if isEmpty h then
      ""
    else if isString h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq env sigma c ^ from_coq env sigma s'
    else
      raise NotAString

end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end
