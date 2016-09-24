module Language.Haskell.TypeCheck.Proof where

import Language.Haskell.TypeCheck.Types

tcProofAbs :: [TcVar] -> TcProof s -> TcProof s
tcProofAbs [] = id
tcProofAbs lst = TcProofAbs lst

tcProofLam :: Int -> TcType s -> TcProof s -> TcProof s
tcProofLam a ty (TcProofPAp x (TcProofVar b)) | a == b = x
tcProofLam a ty p = TcProofLam a ty p
