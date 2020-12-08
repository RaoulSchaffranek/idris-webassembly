||| Spec: https://webassembly.github.io/spec/core/valid/types.html#limits
module WebAssembly.Validation.Types.Limits

import WebAssembly.Structure

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidLimits : Limits -> Nat -> Type where
  ||| Proof that a limit wihtout an upper bound is valid for some given k
  |||
  |||    n <= k
  |||----------------
  ||| ⊢ {min n} : k
  |||
  MkValidLowerBound : (mm = Nothing) -> LTE n k -> ValidLimits (MkLimits n mm) k
  ||| Proof that a limit with lower and upper bound is valid for some given k
  |||
  |||   (n <= k)   (m <= k)   (n <= m)  
  |||------------------------------------
  |||        ⊢ {min n, max m} : k
  |||
  MkValidLimits     : (mm = Just m)  -> LTE n k -> LTE m k -> LTE n m -> ValidLimits (MkLimits n mm) k

-------------------------------------------------------------------------------
-- Lemmas about limit-type validation
-------------------------------------------------------------------------------

||| If the lower bound of a limit without an upper bound is larger than k, then we the limit is invalid
total lower_bound_invalid_upper_bound_absent : (LTE n k -> Void) -> (ValidLimits (MkLimits n Nothing) k -> Void)
lower_bound_invalid_upper_bound_absent not_n_lte_k (MkValidLowerBound _ n_lte_k) = not_n_lte_k n_lte_k
lower_bound_invalid_upper_bound_absent not_n_lte_k (MkValidLimits _ n_lte_k _ _) = not_n_lte_k n_lte_k

||| If the lower bound of a limit with lower and upper bounds is larger than k, then we the limit is invalid
total lower_bound_invalid_upper_bound_present : (LTE n k -> Void) -> (ValidLimits (MkLimits n (Just m)) k -> Void)
lower_bound_invalid_upper_bound_present _ (MkValidLowerBound Refl _) impossible
lower_bound_invalid_upper_bound_present not_n_lte_k (MkValidLimits Refl n_lte_k _ _) = not_n_lte_k n_lte_k

||| If the upper bound of a limit is larger than k, then the limit is invalid
total upper_bound_invalid : (LTE m k -> Void) -> (ValidLimits (MkLimits n (Just m)) k -> Void)
upper_bound_invalid _ (MkValidLowerBound Refl _) impossible
upper_bound_invalid not_m_lte_k (MkValidLimits Refl _ m_lte_k _) = not_m_lte_k m_lte_k

||| If the lower bound is greater than the upper bound, then the limit is invalid
total lower_bound_greater_than_upper_bound : (LTE n m -> Void) -> (ValidLimits (MkLimits n (Just m)) k -> Void)
lower_bound_greater_than_upper_bound _ (MkValidLowerBound Refl _) impossible
lower_bound_greater_than_upper_bound not_n_lte_m (MkValidLimits Refl _ _ n_lte_m) = not_n_lte_m n_lte_m

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

||| Decide whether a given limit is valid for some given k
total public export
isLimitsValid : (limits : Limits) -> (k : Nat) -> Dec (ValidLimits limits k)
isLimitsValid (MkLimits n Nothing) k = 
  case isLTE n k of
    No  contra => No (lower_bound_invalid_upper_bound_absent contra)
    Yes prof   => Yes (MkValidLowerBound Refl prof)
isLimitsValid (MkLimits n (Just m)) k =
  case isLTE n k of
    No  contra => No (lower_bound_invalid_upper_bound_present contra)
    Yes n_lte_k   => case isLTE m k of
      No contra => No (upper_bound_invalid contra)
      Yes m_lte_k  => case isLTE n m of
        No contra => No (lower_bound_greater_than_upper_bound contra)
        Yes n_lte_m  => Yes (MkValidLimits Refl n_lte_k m_lte_k n_lte_m)
