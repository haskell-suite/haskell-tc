module Language.Haskell.TypeCheck.Proof where

import Language.Haskell.TypeCheck.Types

import Debug.Trace

tcProofAbs :: [TcVar] -> TcProof s -> TcProof s
tcProofAbs [] x = x
tcProofAbs lst (TcProofAp x lst') | map TcRef lst == lst' = x
tcProofAbs lst x = TcProofAbs lst x

tcProofAp :: TcProof s -> [TcType s]  -> TcProof s
tcProofAp x [] = x
tcProofAp x lst = TcProofAp x lst

tcProofLam :: Int -> TcType s -> TcProof s -> TcProof s
tcProofLam a ty (TcProofPAp x (TcProofVar b)) | a == b = x
tcProofLam a ty p = TcProofLam a ty p

simplifyProof :: Proof -> Proof
simplifyProof (ProofSrc (TyForall [] ([] :=> ty))) = simplifyProof (ProofSrc ty)
simplifyProof (ProofAbs lst (ProofAp x lst'))
  | map TyRef lst == lst' = simplifyProof x
simplifyProof (ProofLam n ty p) =
  case simplifyProof p of
    ProofPAp p' (ProofVar n')
      | n == n' -> p'
    p' -> ProofLam n ty p'


simplifyProof (ProofAbs tvs p)  = ProofAbs tvs (simplifyProof p)
simplifyProof (ProofAp p ty)    = ProofAp (simplifyProof p) ty
-- simplifyProof (ProofLam n ty p) = ProofLam n ty (simplifyProof p)
simplifyProof (ProofSrc ty)     = ProofSrc ty
simplifyProof (ProofPAp p1 p2)  = ProofPAp (simplifyProof p1) (simplifyProof p2)
simplifyProof (ProofVar n)      = ProofVar n

isTrivial :: Proof -> Bool
-- isTrivial (ProofSrc (TyForall [] ([] :=> ty))) = isTrivial (ProofSrc ty)
isTrivial (ProofSrc TyForall{}) = False
isTrivial ProofSrc{} = True
isTrivial _ = False
