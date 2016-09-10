module Language.Haskell.TypeCheck.Infer where

import           Control.Monad
import           Data.Graph ( stronglyConnComp, flattenSCC )
import           Language.Haskell.Exts.Annotated.Syntax
import           Language.Haskell.Exts.SrcLoc

import           Language.Haskell.Scope
import           Language.Haskell.TypeCheck.Monad
import           Language.Haskell.TypeCheck.Types

-- tiGuardedAlts :: GuardedAlts Origin -> TI TcType
-- tiGuardedAlts galts =
--     case galts of
--         UnGuardedAlt _ branch -> tiExp branch
--         _ -> error "tiGuardedAlts"

tiAlt :: TcType -> Alt Origin -> TI TcType
tiAlt scrutTy (Alt _ pat rhs _mbBinds) = do
    patTy <- tiPat pat
    unify scrutTy patTy
    tiRhs rhs

tiLit :: Literal Origin -> TI TcType
tiLit lit =
    case lit of
        PrimInt{} -> return $ TcCon (mkBuiltIn "LHC.Prim" "I64")
        PrimString{} -> return $ TcApp
            (TcCon (mkBuiltIn "LHC.Prim" "Addr"))
            (TcCon (mkBuiltIn "LHC.Prim" "I8"))
        PrimChar{} -> return $ TcCon (mkBuiltIn "LHC.Prim" "I32")
        Int{} -> return $ TcCon (mkBuiltIn "LHC.Prim" "Int")
        Char{} -> return $ TcCon (mkBuiltIn "LHC.Prim" "Char")
        _ -> error $ "tiLit: " ++ show lit

tiQOp :: QOp Origin -> TI TcType
tiQOp op =
    case op of
        QVarOp src var -> tiExp (Var src var)
        QConOp src con -> tiExp (Con src con)

tiStmts :: [Stmt Origin] -> TI TcType
tiStmts [] = error "tiStmts: empty list"
tiStmts [stmt] =
  case stmt of
    Generator{} -> error $ "tiStmts: " ++ show [stmt]
    Qualifier _ expr -> tiExp expr
    _ -> error $ "tiStmts: " ++ show stmt
tiStmts (stmt:stmts) =
  case stmt of
    Generator (Origin _ pin) pat expr -> do
      ty <- TcMetaVar <$> newTcVar

      patTy <- tiPat pat
      exprTy <- tiExp expr
      restTy <- tiStmts stmts

      (_preds :=> bindIOTy, coercion) <- freshInst bindIOSig
      let ioPatTy = ioType `TcApp` patTy

      unify ioPatTy exprTy -- IO patTy == exprTy
      unify bindIOTy (exprTy `TcFun` ((patTy `TcFun` restTy) `TcFun` (ioType `TcApp` ty))) -- bindIO == expr -> (pat -> rest) -> IO _

      setCoercion pin coercion

      return restTy

    Qualifier (Origin _ pin) expr -> do
      ty <- TcMetaVar <$> newTcVar
      exprTy <- tiExp expr
      restTy <- tiStmts stmts

      (_preds :=> thenIOTy, coercion) <- freshInst thenIOSig
      unify thenIOTy (exprTy `TcFun` (restTy `TcFun` (ioType `TcApp` ty)))

      setCoercion pin coercion

      return restTy
    _ -> error $ "tiStmts: " ++ show (stmt:stmts)

-- forall a b. IO a -> IO b -> IO b
thenIOSig :: TcType
thenIOSig = TcForall [aRef, bRef] ([] :=> (ioA `TcFun` (ioB `TcFun` ioB)))
  where
    aRef = TcVar "a" noSrcSpanInfo
    bRef = TcVar "b" noSrcSpanInfo
    ioA = ioType `TcApp` TcRef aRef
    ioB = ioType `TcApp` TcRef bRef

-- forall a b. IO a -> (a -> IO b) -> IO b
bindIOSig :: TcType
bindIOSig = TcForall [aRef, bRef] ([] :=> (ioA `TcFun` ((TcRef aRef `TcFun` ioB) `TcFun` ioB)))
  where
    aRef = TcVar "a" noSrcSpanInfo
    bRef = TcVar "b" noSrcSpanInfo
    ioA = ioType `TcApp` TcRef aRef
    ioB = ioType `TcApp` TcRef bRef

ioType :: TcType
ioType = TcCon (mkBuiltIn "LHC.Prim" "IO")

tiExp :: Exp Origin -> TI TcType
tiExp expr =
    case expr of

        Case _ scrut alts -> do

            ty <- TcMetaVar <$> newTcVar
            scrutTy <- tiExp scrut
            altTys <- mapM (tiAlt scrutTy) alts
            mapM_ (unify ty) altTys
            return ty
        Var _ qname -> do
            let Origin (Resolved gname) pin = ann qname
            tySig <- findAssumption gname
            (_preds :=> ty, coercion) <- freshInst tySig
            isRec <- isRecursive gname
            if isRec
                then setKnot gname pin
                else setCoercion pin coercion
            return ty
        Con _ (Special _ UnitCon{}) ->
            return $ TcTuple []
        Con _ (Special (Origin _ pin) Cons{}) -> do
            ty <- TcMetaVar <$> newTcVar
            -- (:) :: forall a. a -> List a -> List a
            setCoercion pin $ CoerceAp [ty]
            return $ ty `TcFun` (TcList ty `TcFun` TcList ty)
        Con _ conName -> do
            let Origin (Resolved gname) pin = ann conName
            tySig <- findAssumption gname
            (_preds :=> ty, coercion) <- freshInst tySig
            setCoercion pin coercion
            return ty
        App _ fn a -> do
            ty <- TcMetaVar <$> newTcVar
            fnT <- tiExp fn
            aT <- tiExp a
            unify (TcFun aT ty) fnT
            return ty
        InfixApp _ a op b -> do
            ty <- TcMetaVar <$> newTcVar
            opT <- tiQOp op
            aT <- tiExp a
            bT <- tiExp b
            unify (TcFun aT (TcFun bT ty)) opT
            return ty
        Paren _ e -> tiExp e
        -- \a b c -> d
        -- :: a -> b -> c -> d
        Lambda _ pats e -> do
            patTys <- mapM tiPat pats
            eTy <- tiExp e
            return $ foldr TcFun eTy patTys
        Lit _ lit -> tiLit lit
        Tuple _ Unboxed args ->
            TcUnboxedTuple <$> mapM tiExp args
        Let _ binds subExpr -> do
            tiBinds binds
            tiExp subExpr
        List (Origin _ pin) exprs -> do
            ty <- TcMetaVar <$> newTcVar
            setCoercion pin $ CoerceAp [ty]
            exprTys <- mapM tiExp exprs
            mapM_ (unify ty) exprTys
            return $ TcList ty
        Do _ stmts -> tiStmts stmts
        _ -> error $ "tiExp: " ++ show expr

findConAssumption :: QName Origin -> TI TcType
findConAssumption qname = case qname of
    Special _ con -> case con of
        UnitCon{} -> return (TcTuple [])
        ListCon{} -> do
            ty <- TcMetaVar <$> newTcVar
            return $ TcList ty
        Cons{} -> do
            ty <- TcMetaVar <$> newTcVar
            return $ ty `TcFun` (TcList ty `TcFun` TcList ty)
    _ -> do
        let Origin (Resolved gname) _ = ann qname
        findAssumption gname

tiPat :: Pat Origin -> TI TcType
tiPat pat =
    case pat of
        PVar _ name -> do
            tv <- TcMetaVar <$> newTcVar
            let Origin (Resolved gname) _ = ann name
            setAssumption gname tv
            return tv
        PApp _ con pats -> do
            ty <- TcMetaVar <$> newTcVar
            conSig <- findConAssumption con
            (_preds :=> conTy, _coercion) <- freshInst conSig
            patTys <- mapM tiPat pats
            unify conTy (foldr TcFun ty patTys)
            return ty
        PWildCard _ -> do
            ty <- TcMetaVar <$> newTcVar
            return ty
        PParen _ sub ->
            tiPat sub
        PTuple _ Unboxed pats -> do
            patTys <- mapM tiPat pats
            return $ TcUnboxedTuple patTys
        PLit _ _sign literal ->
            tiLit literal
        PList _ pats -> do
            ty <- TcMetaVar <$> newTcVar
            patTys <- mapM tiPat pats
            mapM_ (unify ty) patTys
            return $ TcList ty
        PInfixApp _ a con b -> do
            ty <- TcMetaVar <$> newTcVar
            aTy <- tiPat a
            bTy <- tiPat b
            conSig <- findConAssumption con
            unify conSig (aTy `TcFun` (bTy `TcFun` ty))
            return ty
        _ -> error $ "tiPat: " ++ show pat

tiRhs :: Rhs Origin -> TI TcType
tiRhs rhs =
    case rhs of
        UnGuardedRhs _ expr ->
            tiExp expr
        _ -> error "tiRhs"

tiMatch :: Match Origin -> TI TcType
tiMatch match =
    case match of
        -- FIXME: typecheck the binds
        Match _ _ pats rhs Nothing -> do
            patTys <- mapM tiPat pats
            t <- tiRhs rhs
            return $ foldr TcFun t patTys
        InfixMatch _ leftPat _ rightPats rhs Nothing -> do
            patTys <- mapM tiPat (leftPat : rightPats)
            t <- tiRhs rhs
            return $ foldr TcFun t patTys
        _ -> error "tiMatch"

--matchPatterns :: Match l -> Int
--matchPatterns (Match _ _ paths _ _) = length paths
--matchPatterns InfixMatch{} = 2

tiBinds :: Binds Origin -> TI ()
tiBinds binds =
    case binds of
        BDecls _ decls -> tiBindGroup decls
        _ -> error "Language.Haskell.TypeCheck.Infer.tiBinds"

tiDecl :: Decl Origin -> TcType -> TI ()
tiDecl decl ty =
    case decl of
        FunBind _ matches -> do
            ts <- mapM tiMatch matches
            mapM_ (unify ty) ts
        PatBind _ _pat rhs binds -> do
            maybe (return ()) tiBinds binds
            rhsTy <- tiRhs rhs
            unify ty rhsTy
        _ -> error $ "tiDecl: " ++ show decl

--tiExpl :: Decl Origin -> TcType -> TI ()
--tiExpl decl declType = do
--    _preds :=> ty <- freshInst declType
--    tiDecl decl ty

declIdent :: Decl Origin -> SrcLoc
declIdent decl =
    case decl of
        FunBind _ (Match _ name _ _ _:_) ->
            let Origin _ src = ann name
            in getPointLoc src
        _ -> error "declIdent"

--tiImpls :: [Decl Origin] -> TI ()
--tiImpls impls = do
--    forM_ impls $ \impl -> do
--        ty <- TcMetaVar <$> newTcVar
--        setAssumption (declIdent impl) ty
--        tiDecl impl ty
--        rTy <- zonk ty
--        liftIO $ print rTy
    -- qualify the type sigs...

declHeadType :: DeclHead Origin -> ([TcVar], GlobalName)
declHeadType dhead =
    case dhead of
        DHead _ name ->
            let Origin (Resolved gname) _ = ann name
            in ([], gname)
        DHApp _ dh tyVarBind ->
            let (tcVars, gname) = declHeadType dh
                var = tcVarFromTyVarBind tyVarBind
            in (tcVars ++ [var], gname)
        _ -> error "declHeadType"
  where
    tcVarFromTyVarBind (KindedVar _ name _) = tcVarFromName name
    tcVarFromTyVarBind (UnkindedVar _ name) = tcVarFromName name

tiConDecl :: [TcVar] -> TcType -> ConDecl Origin -> TI (GlobalName, [TcType])
tiConDecl tvars dty conDecl =
    case conDecl of
        ConDecl _ con tys -> do
            let Origin (Resolved gname) _ = ann con
            setCoercion (globalNameSrcSpanInfo gname) (CoerceAbs tvars)
            return (gname, map typeToTcType tys)
        RecDecl _ con fields -> do
            let conTys = concat
                    [ replicate (length names) (typeToTcType ty)
                    | FieldDecl _ names ty <- fields ]
            forM_ fields $ \(FieldDecl _ names fTy) -> do
                let ty = TcFun dty (typeToTcType fTy)
                forM_ names $ \name -> do
                    let Origin (Resolved gname) _ = ann name
                    setAssumption gname (TcForall tvars $ [] :=> ty)
            let Origin (Resolved gname) _ = ann con
            return (gname, conTys)
        _ -> error "tiConDecl"

tiQualConDecl :: [TcVar] -> TcType -> QualConDecl Origin ->
                 TI (GlobalName, [TcType])
tiQualConDecl tvars dty (QualConDecl _ _ _ con) =
    tiConDecl tvars dty con

tiClassDecl :: Decl Origin -> TI ()
tiClassDecl decl =
    case decl of
        -- ClassDecl _ _ctx (DHead _ className [tyBind]) _deps (Just decls) ->
        --     sequence_
        --         [ worker className tyBind name ty
        --         | ClsDecl _ (TypeSig _ names ty) <- decls, name <- names ]
        _ -> error "tiClassDecl"
  where
    -- tcVarFromName :: Name Origin -> TcVar
    -- tcVarFromTyVarBind (KindedVar _ name _) = tcVarFromName name
    -- tcVarFromTyVarBind (UnkindedVar _ name) = tcVarFromName name
    -- worker className tyBind name ty = do
    --     -- name :: className tybind => ty
    --     let Origin (Resolved gname) _ = ann className
    --         Origin (Resolved (GlobalName src _qname)) _ = ann name
    --         tcVar = tcVarFromTyVarBind tyBind
    --         tcType = typeToTcType ty
    --     let scheme = TcForall [tcVar] ([IsIn gname (TcRef tcVar)] :=> tcType)
    --     setAssumption src scheme

tiPrepareClassDecl :: GlobalName -> [TcVar] -> ClassDecl Origin -> TI ()
tiPrepareClassDecl className [tyVar] decl =
    case decl of
      ClsDecl _ (TypeSig _ names ty) -> do
        forM_ names $ \name -> do
          let Origin (Resolved gname) _ = ann name
              ty' = typeToTcType ty
          setAssumption gname
            (TcForall (freeTcVariables ty') ([IsIn className (TcRef tyVar)] :=> ty'))
      _ -> error $ "tiPrepareClassDecl: " ++ show decl
tiPrepareClassDecl _ _ decl =
    error $ "tiPrepareClassDecl: " ++ show decl

tiPrepareDecl :: Decl Origin -> TI ()
tiPrepareDecl decl =
    case decl of
        DataDecl _ _ _ dhead cons _ -> do
            let (tcvars, GlobalName _ qname) = declHeadType dhead
                dataTy = foldl TcApp (TcCon qname) (map TcRef tcvars)
            forM_ cons $ \qualCon -> do
                (con, fieldTys) <- tiQualConDecl tcvars dataTy qualCon
                let ty = foldr TcFun dataTy fieldTys
                setAssumption con (TcForall tcvars $ [] :=> ty)
        FunBind{} -> return ()
        PatBind{} -> return ()
        TypeDecl{} -> return ()
        ForImp _ _conv _safety _mbExternal name ty -> do
            let Origin (Resolved gname) _ = ann name
            setAssumption gname (typeToTcType ty)
        TypeSig _ names ty -> do
            forM_ names $ \name -> do
                let Origin (Resolved gname) _ = ann name
                setAssumption gname
                    (explicitTcForall $ typeToTcType ty)
                --setCoercion (nameIdentifier name)
                --    (CoerceAbs (freeTcVariables $ typeToTcType ty))
        ClassDecl _ _cxt dhead _funDeps (Just decls) -> do
          let (tcvars, className) = declHeadType dhead
          forM_ decls $ \clsDecl ->
            tiPrepareClassDecl className tcvars clsDecl
        _ -> error $ "tiPrepareDecl: " ++ show decl

tiExpl :: (Decl Origin, GlobalName) -> TI ()
tiExpl (decl, binder) = do
    free <- getFreeMetaVariables
    ty <- TcMetaVar <$> newTcVar
    tiDecl decl ty
    tySig <- findAssumption binder
    (_preds :=> expected, _coercion) <- freshInst tySig
    unify ty expected
    (_, coercion) <- generalize free expected
    setCoercion (globalNameSrcSpanInfo binder) coercion

tiDecls :: [(Decl Origin, GlobalName)] -> TI ()
tiDecls decls = withRecursive thisBindGroup $ do
    free <- getFreeMetaVariables
    -- liftIO $ print $ map snd decls
    forM_ decls $ \(_decl, binder) -> do
        ty <- TcMetaVar <$> newTcVar
        setAssumption binder ty
    forM_ decls $ \(decl, binder) -> do
        ty <- findAssumption binder
        tiDecl decl ty
    forM_ decls $ \(_decl, binder) -> do
        ty <- findAssumption binder
        rTy <- zonk ty
        setAssumption binder rTy
    forM_ decls $ \(_decl, binder) -> do
        ty <- findAssumption binder
        -- rTy <- zonk ty
        rTy <- return ty
        -- liftIO $ print $ Doc.pretty rTy
        (gTy, coercion) <- generalize free rTy
        setCoercion (globalNameSrcSpanInfo binder) coercion
        -- liftIO $ print $ Doc.pretty gTy
        setAssumption binder gTy

    -- forM_ decls $ \(_decl, binder) -> do
    --     ty <- findAssumption binder
    --     rTy <- zonk ty
    --     setAssumption binder rTy

    knots <- getKnots
    forM_ knots $ \(binder, usageLoc) -> do
        coerce <- getCoercion (globalNameSrcSpanInfo binder)
        case coerce of
            CoerceAbs tvs -> setCoercion usageLoc (CoerceAp $ map TcRef tvs)
            _             -> return ()

  where
    thisBindGroup = map snd decls



    --error $ "tiDecls: " ++ show decls

-- First go through the declarations and add explicit type signatures to
-- the environment. Then type check the implicit declarations in their
-- strongly connected groups. Lastly, verify the signature of explicitly
-- typed declarations (this includes instance methods).
tiBindGroup :: [Decl Origin] -> TI ()
tiBindGroup decls = do
    -- liftIO $ putStrLn $ "Explicit: " ++ show explicitlyTyped
    mapM_ tiPrepareDecl decls
    forM_ scc $ tiDecls . flattenSCC
    forM_ explicitDecls tiExpl
  where
    explicitlyTyped =
        [ nameIdentifier name
        | TypeSig _ names _ <- decls
        , name <- names ]
    explicitDecls =
        [ (decl, binder)
        | decl <- decls
        , binder <- declBinders decl
        , binder `elem` explicitlyTyped ]
    graph =
        [ ((decl, binder), binder, declFreeVariables decl )
        | decl <- decls
        , binder <- declBinders decl
        , binder `notElem` explicitlyTyped ]
    scc = stronglyConnComp graph

-- FIXME: Rename this function. We're not finding free variables, we finding
--        all references.
declFreeVariables :: Decl Origin -> [GlobalName]
declFreeVariables decl =
    case decl of
        FunBind _ matches -> concatMap freeMatch matches
        PatBind _ _pat rhs _binds -> freeRhs rhs
        _ -> error $ "declFreeVariables: " ++ show decl
  where
    freeMatch match =
        case match of
            Match _ _ _pats rhs _binds -> freeRhs rhs
            _ -> error "declFreeVariables, freeMatch"
    freeRhs rhs =
        case rhs of
            UnGuardedRhs _ expr -> freeExp expr
            _ -> error "declFreeVariables, freeRhs"
    freeExp expr =
        case expr of
            Var _ qname -> [qnameIdentifier qname]
            Con{} -> []
            Lit{} -> []
            Case _ scrut alts -> freeExp scrut ++ concatMap freeAlt alts
            App _ a b -> freeExp a ++ freeExp b
            InfixApp _ a op b -> freeExp a ++ freeQOp op ++ freeExp b
            Paren _ e -> freeExp e
            Lambda _ _pats e -> freeExp e
            Do _ stmts -> concatMap freeStmt stmts
            _ -> error $ "freeExp: " ++ show expr
    freeStmt stmt =
        case stmt of
            Generator _ _pat expr -> freeExp expr
            Qualifier _ expr -> freeExp expr
            _ -> error $ "freeStmt: " ++ show stmt
    freeQOp op =
        case op of
            QVarOp _ qname -> [qnameIdentifier qname]
            QConOp{} -> []
    freeAlt (Alt _ _pat rhs _binds) = freeRhs rhs

qnameIdentifier :: QName Origin -> GlobalName
qnameIdentifier qname =
    case qname of
        Qual _ _ name -> nameIdentifier name
        UnQual _ name -> nameIdentifier name
        _ -> error "qnameIdentifier"

nameIdentifier :: Name Origin -> GlobalName
nameIdentifier name =
    case info of
        Resolved gname -> gname
        _ -> error "nameIdentifier"
  where
    Origin info _ = ann name

declBinders :: Decl Origin -> [GlobalName]
declBinders decl =
    case decl of
        DataDecl{} -> []
        ForImp{}   -> []
        FunBind _ matches ->
            case head matches of
                Match _ name _ _ _ ->
                    let Origin (Resolved gname) _ = ann name
                    in [gname]
                InfixMatch _ _ name _ _ _ ->
                    let Origin (Resolved gname) _ = ann name
                    in [gname]
        PatBind _ pat _rhs _binds ->
            patBinders pat
        TypeDecl{} -> []
        TypeSig{} -> []
        ClassDecl{} -> []
        _ -> error $ "declBinders: " ++ show decl

patBinders :: Pat Origin -> [GlobalName]
patBinders pat =
    case pat of
        PVar _ name ->
            let Origin (Resolved gname) _ = ann name
            in [gname]
        _ -> error $ "patBinders: " ++ show pat

tiModule :: Module Origin -> TI ()
tiModule m =
    case m of
        Module _ _dhead _pragma _imports decls ->
            tiBindGroup decls
        _ -> error "tiModule"
