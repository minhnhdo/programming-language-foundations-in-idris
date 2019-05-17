module Types

import Logic

%access public export

%default total

data Tm : Type where
  Tru : Tm
  Fls : Tm
  Test : Tm -> Tm -> Tm -> Tm
  Zro : Tm
  Scc : Tm -> Tm
  Prd : Tm -> Tm
  IsZro : Tm -> Tm

data BValue : Tm -> Type where
  BV_Tru : BValue Tru
  BV_Fls : BValue Fls

data NValue : Tm -> Type where
  NV_Zro : NValue Zro
  NV_Scc : NValue t -> NValue (Scc t)

Value : (t : Tm) -> Type
Value t = Either (BValue t) (NValue t)

data Step : Tm -> Tm -> Type where
  ST_TestTru : Step (Test Tru t1 t2) t1
  ST_TestFls : Step (Test Fls t1 t2) t2
  ST_Test : Step t1 t1' -> Step (Test t1 t2 t3) (Test t1' t2 t3)
  ST_Scc : Step t1 t1' -> Step (Scc t1) (Scc t1')
  ST_PrdZro : Step (Prd Zro) Zro
  ST_PrdScc : NValue t1 -> Step (Prd (Scc t1)) t1
  ST_Prd : Step t1 t1' -> Step (Prd t1) (Prd t1')
  ST_IsZroZro : Step (IsZro Zro) Tru
  ST_IsZroScc : NValue t1 -> Step (IsZro (Scc t1)) Fls
  ST_IsZro : Step t1 t1' -> Step (IsZro t1) (IsZro t1')

Uninhabited (Step Tru _) where
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible
  uninhabited (ST_Scc _) impossible
  uninhabited ST_PrdZro impossible
  uninhabited (ST_PrdScc _) impossible
  uninhabited (ST_Prd _) impossible
  uninhabited ST_IsZroZro impossible
  uninhabited (ST_IsZroScc _) impossible
  uninhabited (ST_IsZro _) impossible

Uninhabited (Step Fls _) where
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible
  uninhabited (ST_Scc _) impossible
  uninhabited ST_PrdZro impossible
  uninhabited (ST_PrdScc _) impossible
  uninhabited (ST_Prd _) impossible
  uninhabited ST_IsZroZro impossible
  uninhabited (ST_IsZroScc _) impossible
  uninhabited (ST_IsZro _) impossible

Uninhabited (Step Zro _) where
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible
  uninhabited (ST_Scc _) impossible
  uninhabited ST_PrdZro impossible
  uninhabited (ST_PrdScc _) impossible
  uninhabited (ST_Prd _) impossible
  uninhabited ST_IsZroZro impossible
  uninhabited (ST_IsZroScc _) impossible
  uninhabited (ST_IsZro _) impossible

infix 4 -+>

(-+>) : Tm -> Tm -> Type
(-+>) = Step

StepNormalForm : Tm -> Type
StepNormalForm = NormalForm Step

Stuck : (t : Tm) -> Type
Stuck t = (StepNormalForm t, Not (Value t))

some_term_is_stuck : (t : Tm ** Stuck t)
some_term_is_stuck = (IsZro Tru ** ( \(_ ** s) => case s of
                                       ST_IsZro ST_TestTru impossible
                                       ST_IsZro ST_TestFls impossible
                                       ST_IsZro (ST_Test _) impossible
                                       ST_IsZro (ST_Scc _) impossible
                                       ST_IsZro ST_PrdZro impossible
                                       ST_IsZro (ST_PrdScc _) impossible
                                       ST_IsZro (ST_Prd _) impossible
                                       ST_IsZro ST_IsZroZro impossible
                                       ST_IsZro (ST_IsZroScc _) impossible
                                       ST_IsZro (ST_IsZro _) impossible
                                   , \e => case e of
                                       Left BV_Tru impossible
                                       Left BV_Fls impossible
                                       Right NV_Zro impossible
                                       Right (NV_Scc _) impossible ))

value_is_nf : Value t -> StepNormalForm t
value_is_nf (Left BV_Tru) (_ ** s) = absurd s
value_is_nf (Left BV_Fls) (_ ** s) = absurd s
value_is_nf (Right NV_Zro) (_ ** s) = absurd s
value_is_nf (Right (NV_Scc nv)) (Scc t' ** ST_Scc s) =
  value_is_nf (Right nv) (t' ** s)

step_deterministic : Step x y1 -> Step x y2 -> y1 = y2
step_deterministic ST_TestTru ST_TestTru = Refl
step_deterministic ST_TestTru (ST_Test s) = absurd s
step_deterministic ST_TestFls ST_TestFls = Refl
step_deterministic ST_TestFls (ST_Test s) = absurd s
step_deterministic (ST_Test s) ST_TestTru = absurd s
step_deterministic (ST_Test s) ST_TestFls = absurd s
step_deterministic (ST_Test s1) (ST_Test s2) =
  rewrite step_deterministic s1 s2 in Refl
step_deterministic (ST_Scc s1) (ST_Scc s2) =
  rewrite step_deterministic s1 s2 in Refl
step_deterministic ST_PrdZro ST_PrdZro = Refl
step_deterministic ST_PrdZro (ST_Prd s) = absurd s
step_deterministic (ST_PrdScc _) (ST_PrdScc _) = Refl
step_deterministic (ST_PrdScc v) (ST_Prd (ST_Scc {t1'} s)) =
  absurd (value_is_nf (Right v) (t1' ** s))
step_deterministic (ST_Prd s) ST_PrdZro = absurd s
step_deterministic (ST_Prd (ST_Scc {t1'} s)) (ST_PrdScc v) =
  absurd (value_is_nf (Right v) (t1' ** s))
step_deterministic (ST_Prd s1) (ST_Prd s2) =
  rewrite step_deterministic s1 s2 in Refl
step_deterministic ST_IsZroZro ST_IsZroZro = Refl
step_deterministic ST_IsZroZro (ST_IsZro s) = absurd s
step_deterministic (ST_IsZroScc _) (ST_IsZroScc _) = Refl
step_deterministic (ST_IsZroScc v) (ST_IsZro (ST_Scc {t1'} s)) =
  absurd (value_is_nf (Right v) (t1' ** s))
step_deterministic (ST_IsZro s) ST_IsZroZro = absurd s
step_deterministic (ST_IsZro (ST_Scc {t1'} s)) (ST_IsZroScc v) =
  absurd (value_is_nf (Right v) (t1' ** s))
step_deterministic (ST_IsZro s1) (ST_IsZro s2) =
  rewrite step_deterministic s1 s2 in Refl

data Ty : Type where
  TyBool : Ty
  TyNat : Ty

data HasType : Tm -> Ty -> Type where
  T_Tru : Tru `HasType` TyBool
  T_Fls : Fls `HasType` TyBool
  T_Test : t1 `HasType` TyBool -> t2 `HasType` ty -> t3 `HasType` ty ->
           Test t1 t2 t3 `HasType` ty
  T_Zro : Zro `HasType` TyNat
  T_Scc : t `HasType` TyNat -> Scc t `HasType` TyNat
  T_Prd : t `HasType` TyNat -> Prd t `HasType` TyNat
  T_IsZro : t `HasType` TyNat -> IsZro t `HasType` TyBool

Uninhabited (Zro `HasType` TyBool) where
  uninhabited T_Tru impossible
  uninhabited T_Fls impossible
  uninhabited (T_Test _ _ _) impossible
  uninhabited T_Zro impossible
  uninhabited (T_Scc _) impossible
  uninhabited (T_Prd _) impossible
  uninhabited (T_IsZro _) impossible

Uninhabited (Scc _ `HasType` TyBool) where
  uninhabited T_Tru impossible
  uninhabited T_Fls impossible
  uninhabited (T_Test _ _ _) impossible
  uninhabited T_Zro impossible
  uninhabited (T_Scc _) impossible
  uninhabited (T_Prd _) impossible
  uninhabited (T_IsZro _) impossible

Uninhabited (Tru `HasType` TyNat) where
  uninhabited T_Tru impossible
  uninhabited T_Fls impossible
  uninhabited (T_Test _ _ _) impossible
  uninhabited T_Zro impossible
  uninhabited (T_Scc _) impossible
  uninhabited (T_Prd _) impossible
  uninhabited (T_IsZro _) impossible

Uninhabited (Fls `HasType` TyNat) where
  uninhabited T_Tru impossible
  uninhabited T_Fls impossible
  uninhabited (T_Test _ _ _) impossible
  uninhabited T_Zro impossible
  uninhabited (T_Scc _) impossible
  uninhabited (T_Prd _) impossible
  uninhabited (T_IsZro _) impossible

has_type_1 : Test Fls Zro (Scc Zro) `HasType` TyNat
has_type_1 = T_Test T_Fls T_Zro (T_Scc T_Zro)

has_type_not : Not (Test Fls Zro Tru `HasType` TyBool)
has_type_not (T_Test _ T_Tru _) impossible
has_type_not (T_Test _ T_Fls _) impossible
has_type_not (T_Test _ (T_Test _ _ _) _) impossible
has_type_not (T_Test _ T_Zro _) impossible
has_type_not (T_Test _ (T_Scc _) _) impossible
has_type_not (T_Test _ (T_Prd _) _) impossible
has_type_not (T_Test _ (T_IsZro _) _) impossible

scc_hastype_nat__hastype_nat : Scc t `HasType` TyNat -> t `HasType` TyNat
scc_hastype_nat__hastype_nat (T_Scc ty) = ty

bool_cannonical : t `HasType` TyBool -> Value t -> BValue t
bool_cannonical _ (Left bv) = bv
bool_cannonical ty (Right NV_Zro) = absurd ty
bool_cannonical ty (Right (NV_Scc _)) = absurd ty

nat_cannonical : t `HasType` TyNat -> Value t -> NValue t
nat_cannonical ty (Left BV_Tru) = absurd ty
nat_cannonical ty (Left BV_Fls) = absurd ty
nat_cannonical _ (Right bv) = bv

progress : t `HasType` ty -> Either (Value t) (t' ** t -+> t')
progress T_Tru = Left (Left BV_Tru)
progress T_Fls = Left (Left BV_Fls)
progress (T_Test {t2} {t3} ty1 ty2 ty3) = case progress ty1 of
  Left v => case bool_cannonical ty1 v of
    BV_Tru => Right (t2 ** ST_TestTru)
    BV_Fls => Right (t3 ** ST_TestFls)
  Right (t' ** s) => Right (Test t' t2 t3 ** ST_Test s)
progress T_Zro = Left (Right NV_Zro)
progress (T_Scc ty) = case progress ty of
  Left v => Left (Right (NV_Scc (nat_cannonical ty v)))
  Right (t' ** s) => Right (Scc t' ** ST_Scc s)
progress (T_Prd ty) = case progress ty of
  Left v => case nat_cannonical ty v of
    NV_Zro => Right (Zro ** ST_PrdZro)
    NV_Scc {t} nv => Right (t ** ST_PrdScc nv)
  Right (t' ** s) => Right (Prd t' ** ST_Prd s)
progress (T_IsZro ty) = case progress ty of
  Left v => case nat_cannonical ty v of
    NV_Zro => Right (Tru ** ST_IsZroZro)
    NV_Scc nv => Right (Fls ** ST_IsZroScc nv)
  Right (t' ** s) => Right (IsZro t' ** ST_IsZro s)

preservation : t `HasType` ty -> t -+> t' -> t' `HasType` ty
preservation T_Tru s = absurd s
preservation T_Fls s = absurd s
preservation (T_Test _ ty2 _) ST_TestTru = ty2
preservation (T_Test _ _ ty3) ST_TestFls = ty3
preservation (T_Test ty1 ty2 ty3) (ST_Test s) =
  T_Test (preservation ty1 s) ty2 ty3
preservation T_Zro s = absurd s
preservation (T_Scc ty) (ST_Scc s) = T_Scc (preservation ty s)
preservation (T_Prd ty) ST_PrdZro = ty
preservation (T_Prd (T_Scc ty)) (ST_PrdScc _) = ty
preservation (T_Prd ty) (ST_Prd s) = T_Prd (preservation ty s)
preservation (T_IsZro _) ST_IsZroZro = T_Tru
preservation (T_IsZro _) (ST_IsZroScc _) = T_Fls
preservation (T_IsZro ty) (ST_IsZro s) = T_IsZro (preservation ty s)

MultiStep : Relation Tm
MultiStep = Multi Step

infix 4 -+>*

(-+>*) : Relation Tm
(-+>*) = MultiStep

soundness : t `HasType` ty -> t -+>* t' -> Not (Stuck t')
soundness ht MultiRefl = case progress ht of
  Left v => \(_, p) => p v
  Right p => \(nf, _) => nf p
soundness ht (MultiStep once next) = soundness (preservation ht once) next

nvalue_hastype_nat : NValue t -> t `HasType` TyNat
nvalue_hastype_nat NV_Zro = T_Zro
nvalue_hastype_nat (NV_Scc v) = T_Scc (nvalue_hastype_nat v)

subject_expansion : (  t : Tm ** t' : Tm ** ty : Ty
                    ** (t -+> t', t' `HasType` ty, Not (t `HasType` ty)))
subject_expansion = (  Test Tru Zro Tru ** Zro ** TyNat
                    ** (ST_TestTru, T_Zro, \ty => case ty of
                                             T_Test _ _ ty3 => absurd ty3))
