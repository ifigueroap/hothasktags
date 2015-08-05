{-# LANGUAGE PatternGuards #-}

module Main where

import Options.Applicative
import qualified Language.Haskell.Exts.Annotated as L
import System.IO
import GHC.IO.Handle (HandlePosition)
import qualified Data.Map.Strict as Map
import qualified Language.Preprocessor.Cpphs as CPP
import Control.Exception (ErrorCall(..), catch, evaluate)
import System.Exit (exitFailure)
import Control.Monad
import qualified Data.Array.Unboxed as A
import Data.List (sort)
import Data.Maybe (fromMaybe, catMaybes, maybeToList)
import Data.List.Split (endBy)
import Prelude hiding (exp)

type Database = Map.Map String (L.Module L.SrcSpanInfo)
type LineInfo = Map.Map FilePath (A.Array Int (HandlePosition, String))

data Defn = Defn FilePath Int Int -- file, line, end col
    deriving Show

localDecls :: L.Module L.SrcSpanInfo -> Map.Map String Defn
localDecls (L.Module _ _ _ _ decls) = Map.fromList $ concatMap extract decls
    where
      -- TODO: CHECK OTHER KINDS OF DECLARATIONS: CLASS, TYPE, TYPEFAM, ETC...
    extract (L.TypeDecl _ hd _) = extractDeclHead hd
    extract (L.TypeFamDecl _ hd _) = extractDeclHead hd
    extract (L.DataDecl _ _ _ hd decls' _) =
      extractDeclHead hd ++ concatMap extractQualConDecl decls'
    extract (L.GDataDecl _ _ _ hd _ decls' _) =
      extractDeclHead hd ++ concatMap extractGadtDecl decls'
    extract (L.DataFamDecl _ _ hd _) = extractDeclHead hd
    extract (L.ClassDecl _ _ hd _ clsdecls) =
      extractDeclHead hd ++ concatMap extractClassDecl (fromMaybe [] clsdecls)

    -- AT LEAST HERE: ENHANCED EXTRACTION OF TAGS
    extract (L.TypeSig _ names typ) = concatMap extractName names ++ extractType typ

    -- extracts the name of the function and then the names of called functions
    extract (L.FunBind _ matches@(L.Match _ name _ _ _ : _)) = extractName name ++ concatMap extractMatch matches
    extract (L.FunBind _ matches@(L.InfixMatch _ _ name _ _ _ : _)) = extractName name ++ concatMap extractMatch matches

    -- extract (L.FunBind _ (L.Match _ name _ _ _ : _)) = extractName name
    -- extract (L.FunBind _ (L.InfixMatch _ _ name _ _ _ : _)) = extractName name

    extract (L.PatBind _ pat _ _) = extractPat pat
    extract (L.ForImp _ _ _ _ name _) = extractName name
    extract _ = []

    extractDeclHead (L.DHead _ name) = extractName name
    extractDeclHead (L.DHInfix _ _ name) = extractName name
    extractDeclHead (L.DHParen _ head') = extractDeclHead head'
    extractDeclHead (L.DHApp _ head' _) = extractDeclHead head'

    extractPat (L.PVar _ name) = extractName name
    extractPat (L.PApp _ _ pats) = concatMap extractPat pats
    extractPat (L.PTuple _ _ pats) = concatMap extractPat pats
    extractPat (L.PList _ pats) = concatMap extractPat pats
    extractPat (L.PParen _ pat) = extractPat pat
    extractPat (L.PAsPat _ name pat) = extractName name ++ extractPat pat
    extractPat (L.PIrrPat _ pat) = extractPat pat
    extractPat (L.PatTypeSig _ pat _) = extractPat pat
    extractPat (L.PBangPat _ pat) = extractPat pat
    extractPat _ = []

    -- TODO: IMPLEMENT
    extractMatch (L.Match _ _ pats rhs maybeBinds) =
      concatMap extractPat pats ++ extractRhs rhs ++ concatMap extractBinds (maybeToList maybeBinds)
    extractMatch (L.InfixMatch _ pat _ pats rhs maybeBinds) =
      concatMap extractPat ([pat] ++ pats) ++ extractRhs rhs ++ concatMap extractBinds (maybeToList maybeBinds)

    extractRhs (L.UnGuardedRhs _ exp) = extractExp exp
    extractRhs (L.GuardedRhss _ grhs) = concatMap extractGRhs grhs

    -- EXTRACT NAMED-FUNCTIONS APPLICATIONS IN ALL EXPRESSIONS
    extractExp(L.InfixApp _ lExp qop rExp) = extractQOp qop ++ concatMap extractExp [lExp, rExp]
    extractExp(L.App _ lExp rExp) = concatMap extractExp [lExp, rExp]
    extractExp(L.NegApp _ exp) = extractExp exp
    extractExp(L.Var _ qname) = extractQName qname
    extractExp(L.IPVar _ _ipname) = [] -- NOT CONSIDERING PARAMETER NAMES
    extractExp(L.Con _ qname) = extractQName qname
    
    extractExp(L.Lit _ _lit) = []
    extractExp(L.Lambda _ pats exp) = concatMap extractPat pats ++ extractExp exp
    extractExp(L.Let _ binds exp) = extractBinds binds ++ extractExp exp
    extractExp(L.If _ cExp tExp eExp) = concatMap extractExp [cExp, tExp, eExp]
    extractExp(L.Case _ exp alts) = extractExp exp ++ concatMap extractAlt alts
    extractExp(L.Do _ stmts) = concatMap extractStmt stmts
    extractExp(L.MDo _ stmts) = concatMap extractStmt stmts
    extractExp(L.Tuple _ _ exps) = concatMap extractExp exps
    extractExp(L.TupleSection _ _ maybeExps) = concatMap extractExp (catMaybes maybeExps)
    extractExp(L.List _ exps) = concatMap extractExp exps
    extractExp(L.Paren _ exp) = extractExp exp
    extractExp(L.LeftSection _ exp qop) = extractExp exp ++ extractQOp qop
    extractExp(L.RightSection _ qop exp) = extractQOp qop ++ extractExp exp
    extractExp(L.RecConstr _ qname fieldUpdates) = extractQName qname ++ concatMap extractFieldUpdate fieldUpdates
    extractExp(L.RecUpdate _ exp fieldUpdates) = extractExp exp ++ concatMap extractFieldUpdate fieldUpdates
    extractExp(L.EnumFrom _ exp) = extractExp exp
    extractExp(L.EnumFromTo _ fromExp toExp) = concatMap extractExp [fromExp, toExp]
    extractExp(L.EnumFromThen _ fromExp thenExp) = concatMap extractExp [fromExp, thenExp]
    extractExp(L.EnumFromThenTo _ fromExp thenExp toExp) = concatMap extractExp [fromExp, thenExp, toExp]
    extractExp(L.ListComp _ exp qualStmts) = extractExp exp ++ concatMap extractQualStmt qualStmts
    extractExp(L.ParComp  _ exp qualStmts) = extractExp exp ++ concatMap extractQualStmt (concat qualStmts)
    extractExp(L.ExpTypeSig _ exp typ) = extractExp exp ++ extractType typ

    -- Template Haskell
    extractExp(L.VarQuote _ qname) = extractQName qname
    extractExp(L.TypQuote _ qname) = extractQName qname
    extractExp(L.BracketExp _ bracket) = extractBracket bracket
    extractExp(L.SpliceExp _ splice) = extractSplice splice
    extractExp(L.QuasiQuote _ _str1 _str2) = [] -- NOT CONSIDERING TEMPLATE QUASI-QUOTES

    -- XML
    extractExp(L.XTag _ _xname _xattrs maybeExp exps) =
      concatMap extractExp (maybeToList maybeExp) ++ concatMap extractExp exps
    extractExp(L.XETag _ _xname _xattrs maybeExp) = concatMap extractExp (maybeToList maybeExp)
    extractExp(L.XPcdata _ _str) = []
    extractExp(L.XExpTag _ exp) = extractExp exp
    extractExp(L.XChildTag _ exps) = concatMap extractExp exps

    -- Pragmas
    extractExp(L.CorePragma _ _str exp) = extractExp exp                
    extractExp(L.SCCPragma  _ _str exp) = extractExp exp
    extractExp(L.GenPragma  _ _str _intPair1 _intPair2 exp) = extractExp exp

    -- Arrows
    extractExp(L.Proc _ pat exp) = extractPat pat ++ extractExp exp
    extractExp(L.LeftArrApp _ lExp rExp) = concatMap extractExp [lExp, rExp]
    extractExp(L.RightArrApp _ lExp rExp) = concatMap extractExp [lExp, rExp]
    extractExp(L.LeftArrHighApp _ lExp rExp) = concatMap extractExp [lExp, rExp]
    extractExp(L.RightArrHighApp _ lExp rExp) = concatMap extractExp [lExp, rExp]

    extractGRhs (L.GuardedRhs _ stmts exp) = concatMap extractStmt stmts ++ extractExp exp

    extractBinds (L.BDecls _ _decls) = concatMap extract _decls
    extractBinds (L.IPBinds _ ipbinds) = concatMap extractIPBind ipbinds

    extractIPBind (L.IPBind _ _ipname exp) = extractExp exp

    extractAlt (L.Alt _ pat rhs maybeBinds) =
      extractPat pat ++ extractRhs rhs ++ concatMap extractBinds (maybeToList maybeBinds)

    extractStmt (L.Generator _ pat exp) = extractPat pat ++ extractExp exp
    extractStmt (L.Qualifier _ exp) = extractExp exp
    extractStmt (L.LetStmt _ binds) = extractBinds binds
    extractStmt (L.RecStmt _ stmts) = concatMap extractStmt stmts    

    extractQualStmt (L.QualStmt _ stmt) = extractStmt stmt
    extractQualStmt (L.ThenTrans _ exp) = extractExp exp
    extractQualStmt (L.ThenBy _ exp1 exp2) = concatMap extractExp [exp1, exp2]
    extractQualStmt (L.GroupBy _ exp) = extractExp exp
    extractQualStmt (L.GroupUsing _ exp) = extractExp exp
    extractQualStmt (L.GroupByUsing _ exp1 exp2) = concatMap extractExp [exp1, exp2]

    extractQOp (L.QVarOp _ qname) = extractQName qname
    extractQOp (L.QConOp _ qname) = extractQName qname

    extractFieldUpdate (L.FieldUpdate _ qname exp) = extractQName qname ++ extractExp exp
    extractFieldUpdate (L.FieldPun _ qname) = extractQName qname
    extractFieldUpdate (L.FieldWildcard _) = []

    extractBracket (L.ExpBracket _ exp) = extractExp exp
    extractBracket (L.PatBracket _ pat) = extractPat pat
    extractBracket (L.TypeBracket _ typ) = extractType typ
    extractBracket (L.DeclBracket _ _decls) = concatMap extract _decls

    extractSplice (L.IdSplice _ _str) = []
    extractSplice (L.ParenSplice _ exp) = extractExp exp    

    -- TODO: IMPLEMENT
    extractType (L.TyForall _ _ _ _) = []
    extractType (L.TyFun _ _ _) = []
    extractType (L.TyTuple _ _ _) = []
    extractType (L.TyList  _ _) = []
    extractType (L.TyApp _ _ _) = []
    extractType (L.TyVar _ _) = []
    extractType (L.TyCon _ _) = []
    extractType (L.TyParen _ _) = []
    extractType (L.TyInfix _ _ _ _) = []
    extractType (L.TyKind _ _ _) = []
    extractType _ = []

    extractQualConDecl (L.QualConDecl _ _ _ (L.ConDecl _ name _)) =
      extractName name
    extractQualConDecl (L.QualConDecl _ _ _ (L.RecDecl _ name fields)) =
      extractName name ++ concatMap extractFieldDecl fields
    extractQualConDecl _ = []

    extractFieldDecl (L.FieldDecl _ names _) = concatMap extractName names

    extractGadtDecl (L.GadtDecl _ name _ _) = extractName name

    extractClassDecl (L.ClsDecl _ decl) = extract decl
    extractClassDecl (L.ClsDataFam _ _ hd _) = extractDeclHead hd
    extractClassDecl (L.ClsTyFam _ hd _) = extractDeclHead hd
    extractClassDecl _ = []

    extractQName (L.Qual _ _modname name) = extractName name
    extractQName (L.UnQual _ name) = extractName name
    extractQName (L.Special _ _) = [] -- NO SPECIAL CONSTRUCTORS CONSIDERED AS TERMS

    extractName (L.Ident loc name) = [(name, getLoc loc)]
    extractName (L.Symbol loc name) = [(name, getLoc loc)]

localDecls _ = Map.empty

getLoc :: L.SrcSpanInfo -> Defn
getLoc (L.SrcSpanInfo (L.SrcSpan file line _ _ ecol) _) =
  Defn file line ecol

thingMembers :: L.Module L.SrcSpanInfo -> String -> [String]
thingMembers (L.Module _ _ _ _ decls) name = concatMap extract decls
  where
    extract (L.DataDecl _ _ _ hd condecls _)
      | nameOfHead hd == Just name = concatMap getQualConDecl condecls
    extract (L.GDataDecl _ _ _ hd _ condecls _)
      | nameOfHead hd == Just name = concatMap getGadtDecl condecls
    extract (L.ClassDecl _ _ hd _ (Just classdecls))
      | nameOfHead hd == Just name = concatMap getClassDecl classdecls
    extract _ = []

    getQualConDecl (L.QualConDecl _ _ _ (L.ConDecl _ (L.Ident _ name') _)) =
      [name']
    getQualConDecl (L.QualConDecl _ _ _ (L.RecDecl _ (L.Ident _ name') flds)) =
      name' : concatMap getField flds
    getQualConDecl _ = []

    getGadtDecl (L.GadtDecl _ name' _ _) = getName name'

    getField (L.FieldDecl _ names _) = concatMap getName names

    getClassDecl (L.ClsDecl _ (L.FunBind _ (L.Match _ name' _ _ _ : _))) =
      getName name'
    getClassDecl (L.ClsDecl _ (L.PatBind _ (L.PVar _ name') _ _)) =
      getName name'
    getClassDecl _ = []

    getName (L.Ident _ name') = [name']
    getName _ = []

    nameOfHead (L.DHead _ (L.Ident _ name')) = Just name'
    nameOfHead (L.DHInfix _ _ (L.Ident _ name')) = Just name'
    nameOfHead (L.DHParen _ h) = nameOfHead h
    nameOfHead _ = Nothing
thingMembers _ _ = []

modExports :: Database -> String -> Map.Map String Defn
modExports db modname = case Map.lookup modname db of
    Nothing -> Map.empty
    Just mod' -> Map.filterWithKey (\k _ -> exported mod' k) (localDecls mod')

exported :: L.Module L.SrcSpanInfo -> String -> Bool
exported mod'@(L.Module _
               (Just (L.ModuleHead _ _ _
                      (Just (L.ExportSpecList _ specs)))) _ _ _) name =
    any (matchesSpec name) specs
  where
    matchesSpec nm (L.EVar _ _ (L.UnQual _ (L.Ident _ name'))) = nm == name'
    matchesSpec nm (L.EAbs _ (L.UnQual _ (L.Ident _ name'))) = nm == name'
    matchesSpec nm (L.EThingAll _ (L.UnQual _ (L.Ident _ name'))) =
      nm == name' || (nm `elem` thingMembers mod' name')
    matchesSpec nm (L.EThingWith _ (L.UnQual _ (L.Ident _ name')) cnames) =
      nm == name' || any (matchesCName nm) cnames
    -- XXX this is wrong, moduleScope handles it though
    matchesSpec _ (L.EModuleContents _ (L.ModuleName _ _)) = False
    matchesSpec _ _ = False

    matchesCName nm (L.VarName _ (L.Ident _ name')) = nm == name'
    matchesCName nm (L.ConName _ (L.Ident _ name')) = nm == name'
    matchesCName _ _ = False
exported _ _ = True

moduleScope :: Database -> L.Module L.SrcSpanInfo -> Map.Map String Defn
moduleScope db mod'@(L.Module _ modhead _ imports _) =
  Map.unions $ moduleItself : localDecls mod' : map extractImport imports
    where
      moduleItself = moduleDecl modhead

      moduleDecl (Just (L.ModuleHead l (L.ModuleName _ name) _ _)) =
        Map.singleton name (getLoc l)
      moduleDecl _ = Map.empty

      extractImport decl@(L.ImportDecl { L.importModule = L.ModuleName _ name
                                       , L.importSpecs = spec
                                       }) =
          let extraExports
                | Just (L.ModuleHead _ _ _
                        (Just (L.ExportSpecList _ especs))) <- modhead =
                    Map.unions [ modExports db modname |
                                 L.EModuleContents _ (L.ModuleName _ modname)
                                 <- especs ]
                | otherwise = Map.empty in

          Map.unions [
            if L.importQualified decl
            then Map.empty
            else   names
                 , Map.mapKeys ((name ++ ".") ++) names
                 , case L.importAs decl of
                       Nothing -> Map.empty
                       Just (L.ModuleName _ name') ->
                         Map.mapKeys ((name' ++ ".") ++) names
                 , extraExports
          ]
        where
          names | Just (L.ImportSpecList _ True specs) <- spec =
                    let s = map (flip (,) ()) (concatMap specName specs) in
                    normalExports `Map.difference` Map.fromList s
                | Just (L.ImportSpecList _ False specs) <- spec =
                    let f k _ = k `elem` concatMap specName specs in
                    Map.filterWithKey f normalExports
                | otherwise = normalExports

          normalExports = modExports db name

          specName (L.IVar _ _ (L.Ident _ name')) = [name']
          specName (L.IAbs _ (L.Ident _ name')) = [name']
          -- XXX incorrect, need its member names
          specName (L.IThingAll _ (L.Ident _ name')) = [name']
          specName (L.IThingWith _ (L.Ident _ name') cnames) =
            name' : concatMap cname cnames
          specName _ = []

          cname (L.VarName _ (L.Ident _ name')) = [name']
          cname (L.ConName _ (L.Ident _ name')) = [name']
          cname _ = []

moduleScope _ _ = Map.empty

makeVimTags :: FilePath -> Map.Map String Defn -> LineInfo -> IO [String]
makeVimTags refFile m _ = pure $ map (makeTag refFile) (Map.assocs m)
  where
    makeTag refFile' (name, Defn file line _) =
      name ++ "\t" ++ file ++ "\t" ++ show line ++ ";\"\t" ++ "file:" ++
      refFile'

makeEmacsTags :: FilePath -> Map.Map String Defn -> LineInfo -> IO [String]
makeEmacsTags refFile m li = do
    tags <- mapM (makeTag refFile) (Map.assocs m)
    let tagsLen = show (sum $ map length tags)
    return $ "\x0c":(refFile ++ "," ++ tagsLen):tags
  where
    makeTag _ (name, Defn file line ecol) = do
      ms <- catch (evaluate $ li Map.! file) $ \(ErrorCall _) -> do
        hPutStrLn stderr $ "hothasktags: couldn't find '" ++ file ++ "'"
        exitFailure
      let linenum = show line
          (offset, leader) =
            let x = ms A.! (line - 1) in
            (show $ fst x, take (ecol - 1) $ snd x)
      return $ leader ++ "\x7f" ++ name ++ "\x01" ++ linenum ++ "," ++ offset

haskellSource :: [L.Extension] -> HotHasktags -> FilePath -> IO String
haskellSource exts conf file = do
    contents <- readFile file
    let needsCpp = not . null $
            [ () | Just (_language, extsFile) <- [L.readExtensions contents],
                   L.EnableExtension L.CPP <- extsFile ]
         ++ [ () | L.EnableExtension L.CPP <- exts ]
    if not needsCpp then return contents else do
      cppOpts <- either recoverCppOptFail return
                 (CPP.parseOptions (hhCpphs conf))
      CPP.runCpphs (addOpts cppOpts) file contents
  where
    addOpts defOpts = defOpts
         { CPP.boolopts = (CPP.boolopts defOpts) { CPP.hashline = False },
           CPP.defines = map splitDefines (hhDefine conf) ++
                         CPP.defines defOpts,
           CPP.includes = hhInclude conf ++ CPP.includes defOpts }

    recoverCppOptFail err = do
        hPutStrLn stderr $ "cpphs parse error arguments:" ++ err
        return CPP.defaultCpphsOptions

    splitDefines :: String -> (String,String)
    splitDefines s = let (a,b) = break (=='=') s in
                     (a, case drop 1 b of
                           [] -> "1"
                           b' -> b')

makeDatabase :: [L.Extension] -> HotHasktags -> IO Database
makeDatabase exts conf =
    fmap (Map.fromList . concat) . forM (hhFiles conf) $ \file -> do
        result <- L.parseFileContentsWithMode (mode file)
                    `fmap` haskellSource exts conf file
        case result of
            L.ParseOk mod'@(L.Module _ moduleHead _ _ _) ->
                return [(moduleName moduleHead, mod')]
            L.ParseFailed loc str' -> do
                hPutStrLn stderr $ "Parse error: " ++  show loc ++ ": " ++ str'
                return []
            _ -> return []
  where
    moduleName (Just (L.ModuleHead _ (L.ModuleName _ name) _ _)) = name
    -- for files without a module decl, i.e. implicit Main
    moduleName Nothing = ""

    mode filename = L.ParseMode
      { L.parseFilename = filename
      , L.extensions = exts
      , L.ignoreLanguagePragmas = False
      , L.ignoreLinePragmas = False
      , L.fixities = Nothing
      , L.baseLanguage = L.Haskell2010
      }

moduleFile :: L.Module L.SrcSpanInfo -> FilePath
moduleFile (L.Module (L.SrcSpanInfo (L.SrcSpan file _ _ _ _) _) _ _ _ _) = file
-- these could be converted with sModule; see Language.Haskell.Exts.Simplify
moduleFile _ = error "Sorry, XmlPage/XmlHybrid modules are not supported"

data TagsType = VimTags | EmacsTags deriving (Eq)

data HotHasktags = HotHasktags
    { hhLanguage, hhDefine, hhInclude, hhCpphs :: [String]
    , hhOutput :: Maybe FilePath
    , hhTagstype :: TagsType
    , hhSplitOnNUL :: Bool
    , hhFiles :: [FilePath]
    }

optParser :: Parser HotHasktags
optParser = HotHasktags
    <$> many (strOption
        ( short 'X'
       <> long "hh-language"
       <> metavar "ITEM"
       <> help "Additional language extensions to use when parsing a file.  \
               \LANGUAGE pragmas are currently obeyed.  Always includes at \
               \least MultiParamTypeClasses, ExistentialQuantification, \
               \and FlexibleContexts" ))
    <*> many (strOption
        ( short 'D'
       <> long "hh-define"
       <> metavar "ITEM"
       <> help "Define for cpphs.  -Dx is a shortcut for the flags -c -Dx" ))
    <*> many (strOption
        ( short 'I'
       <> long "hh-include"
       <> metavar "DIR"
       <> help "Add a directory to where cpphs looks for .h includes.  Note \
               \that paths are currently interpreted as relative to the \
               \directory containing the source file.\n\
               \-Ifoo is a shortcut for -c -Ifoo" ))
    <*> many (strOption
        ( short 'c'
       <> long "cpp"
       <> metavar "ITEM"
       <> help "Pass the next argument as an option for cpphs.  For example:\n\
               \`hothasktags -c --strip -XCPP foo.hs'" ))
    <*> optional (strOption
        ( short 'O'
       <> long "output"
       <> metavar "FILE"
       <> help "Name of output file.  Default is to write to stdout" ))
    <*> flag VimTags EmacsTags
          ( short 'e'
         <> help "Emit Emacs tags" )
    <*> switch
        ( short '0'
       <> long "null"
       <> help "Split stdin on NUL instead of newline" )
    <*> many (argument str (metavar "FILE"))

linePositions :: Handle -> IO (Int, [(HandlePosition, String)])
linePositions h = go 1 []
  where
    go lineno acc = do
      pos <- hTell h
      ln <- hGetLine h
      atEOF <- hIsEOF h
      let res = (pos, ln):acc
      if atEOF then return (lineno, reverse res) else go (lineno + 1) res

emacsLineInfo :: [FilePath] -> IO LineInfo
emacsLineInfo files = do
    filesContents <- forM files $ \f -> withFile f ReadMode linePositions
    return $ Map.fromList
               [(path, A.array (0, numLines - 1) (zip [0..] ls))
                | (path, (numLines, ls)) <- zip files filesContents]

stdinFileList :: Bool -> IO [FilePath]
stdinFileList onNull = liftM splitter getContents
  where
    splitter = if onNull then endBy "\0" else lines

main :: IO ()
main = do
    let opts = info (helper <*> optParser)
          ( fullDesc
         <> progDesc "The hothasktags program" )
    conf <- execParser opts
    let exts = map L.classifyExtension $ hhLanguage conf ++
               ["MultiParamTypeClasses", "ExistentialQuantification",
                "FlexibleContexts"]
    case unwords [ ext | L.UnknownExtension ext <- exts ] of
            [] -> return ()
            unknown -> hPutStrLn stderr $ "Unknown extensions on command line: "
                                            ++ unknown
    conf' <- case hhFiles conf of
      [] -> liftM (\x -> conf { hhFiles = x })
                  $ stdinFileList (hhSplitOnNUL conf)
      _ -> return conf
    lineInfo <- if hhTagstype conf' == EmacsTags
                then emacsLineInfo $ hhFiles conf'
                else return Map.empty
    database <- makeDatabase exts conf'
    let (fMakeTags, fSort) = if hhTagstype conf' == EmacsTags
                             then (makeEmacsTags, id)
                             else (makeVimTags, sort)
        makeTags x = fMakeTags (moduleFile x)
                               (moduleScope database x)
                               lineInfo
    ts <- do
      ts <- mapM makeTags $ Map.elems database
      return (fSort $ concat ts)

    handle <- case hhOutput conf' of
                Nothing -> return stdout
                Just file -> openFile file WriteMode

    mapM_ (hPutStrLn handle) ts

    case hhOutput conf' of
      Nothing -> return ()
      _ -> hClose handle
