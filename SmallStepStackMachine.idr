module SmallStepStackMachine

import Expr
import Logic
import Maps
import SmallStepExpr

%access public export

%default total

data SInstr : Type where
  SPush : (n : Nat) -> SInstr
  SLoad : (x : Id) -> SInstr
  SPlus : SInstr
  SMinus : SInstr
  SMult : SInstr

Stack : Type
Stack = List Nat

Prog : Type
Prog = List SInstr

data StackStep : State -> (Prog, Stack) -> (Prog, Stack) -> Type where
  SS_Push : StackStep st (SPush n :: p', stk) (p', n :: stk)
  SS_Load : StackStep st (SLoad x :: p', stk) (p', st x :: stk)
  SS_Plus : StackStep st (SPlus :: p', n :: m :: stk) (p', m + n :: stk)
  SS_Minus : StackStep st (SMinus :: p', n :: m :: stk) (p', minus m n :: stk)
  SS_Mult : StackStep st (SMult :: p', n :: m :: stk) (p', m * n :: stk)

stack_deterministic : Deterministic (StackStep st)
stack_deterministic SS_Push SS_Push = Refl
stack_deterministic SS_Load SS_Load = Refl
stack_deterministic SS_Plus SS_Plus = Refl
stack_deterministic SS_Minus SS_Minus = Refl
stack_deterministic SS_Mult SS_Mult = Refl

StackMultiStep : (st : State) -> Relation (Prog, Stack)
StackMultiStep st = Multi (StackStep st)

s_compile : (e : AExp) -> Prog
s_compile (ANum k) = [SPush k]
s_compile (AId x) = [SLoad x]
s_compile (APlus x y) = s_compile x ++ s_compile y ++ [SPlus]
s_compile (AMinus x y) = s_compile x ++ s_compile y ++ [SMinus]
s_compile (AMult x y) = s_compile x ++ s_compile y ++ [SMult]

compiler_is_correct : AStep st e (ANum n) ->
                      Multi (StackStep st) (s_compile e, stk) ([], n :: stk)
compiler_is_correct AS_Id = MultiStep SS_Load MultiRefl
compiler_is_correct AS_Plus =
  MultiStep SS_Push $
  MultiStep SS_Push $
  MultiStep SS_Plus $
  MultiRefl
compiler_is_correct AS_Minus =
  MultiStep SS_Push $
  MultiStep SS_Push $
  MultiStep SS_Minus $
  MultiRefl
compiler_is_correct AS_Mult =
  MultiStep SS_Push $
  MultiStep SS_Push $
  MultiStep SS_Mult $
  MultiRefl
