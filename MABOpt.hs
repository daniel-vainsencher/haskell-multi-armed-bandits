--invoke: ghci -package ghc Driver.hs
module MABOpt (findBest, inliningProblem, prestrictnessInliningProblem, tapeSetFromTape, todo, stringFromTape, work, inliningPayoff) where

import GHC
import Outputable
import HscTypes
import CoreUtils
import qualified Data.Map as Map
import GHC.Paths ( libdir )

import Text.Printf
import Data.Maybe
import MonadUtils
import CoreMonad
import SimplMonad
import BasicTypes
import SimplCore
import DmdAnal          ( dmdAnalPgm )
import MultiArmedBanditTree


import HscMain
import Rules            ( RuleBase, emptyRuleBase, mkRuleBase, unionRuleBase,
                          extendRuleBaseList, ruleCheckProgram, addSpecInfo, )

import UniqSupply       ( UniqSupply, mkSplitUniqSupply, splitUniqSupply )
import DynFlags

import System.CPUTime

-- libdir :: FilePath
-- libdir = "/home/t-davain/ghc-work/inplace/lib"
targetName = "Main"
targetFile = "/home/t-davain/ghc-work/nofib/imaginary/integrate/" ++ targetName ++ ".hs"

simpl_mode = SimplMode { sm_phase      = Phase 0
                         , sm_names      = []
                         , sm_rules      = True
                         , sm_eta_expand = True
                         , sm_inline     = True
                         , sm_case_case  = True }

todo tapes = CoreDoSimplify 4 tapes simpl_mode
yesses = True:yesses
noes = False:noes
tapeSetFromTape tape = [Just tape, Nothing , Nothing, Nothing]

inliningProblem initGuts flags measure = BanditProblem {
                   bpPlayAction = playTape initGuts flags measure,
                   bpRoot = ActionSeqEnd,
                   bpIsDeterministic = True}

prestrictnessInliningProblem initGuts flags measure = BanditProblem {
                   bpPlayAction = playTapeWithStrictness initGuts flags measure,
                   bpRoot = ActionSeqEnd,
                   bpIsDeterministic = True}


inliningPayoff :: ModGuts -> DynFlags -> (Tick->Float) -> ActionSpec SearchTapeElement -> IO Float
inliningPayoff guts dflags measure tape =
    do (resGuts, count, needMoreTape) <- tapeResults guts dflags tape
       return $ scoreResults resGuts count measure


-- Lifted from SimplCore
doPassM bind_f guts = do
    binds' <- bind_f (mg_binds guts)
    return (guts { mg_binds = binds' })

playTapeWithStrictness guts dflags measure tape = do
       startTime <- liftIO getCPUTime
       (guts1, count1, needMoreTape) <- tapeResults guts dflags tape
       guts2 <- (doPassM (dmdAnalPgm dflags)) guts1
       (resGuts, count2, _ ) <- tapeResults guts2 dflags ActionSeqEnd
       endTime <- liftIO getCPUTime
       let actionList = if needMoreTape
              then [justActions tape ++ [True], justActions tape ++ [False]]
              else []
       let seconds = fromIntegral (endTime - startTime) / 10 ** 12
       liftIO $ putStrLn $ "Tape length=" ++ show (length $ justActions tape) ++
                           ", seconds to run: " ++ show seconds ++
                           ", tape: " ++ (stringFromTape $ justActions tape) ++
                           if needMoreTape then "..." else "X"

       return $ BanditFeedback { fbSubproblemFeedbacks = undefined
                               , fbPayoff = (scoreResults resGuts (plusSimplCount count1 count2) measure)
                               , fbActions = actionList}


-- playTape :: ModGuts -> DynFlags -> (Tick->Int) -> [SearchTapeElement] -> IO (Float, [[SearchTapeElement]])
playTape guts dflags measure tape = do
       startTime <- liftIO getCPUTime
       (resGuts, count, needMoreTape) <- tapeResults guts dflags tape
       endTime <- liftIO getCPUTime
       let actionList = if needMoreTape
              then [justActions tape ++ [True], justActions tape ++ [False]]
              else []
       let seconds = fromIntegral (endTime - startTime) / 10 ** 12
       liftIO $ putStrLn $ "Tape length=" ++ show (length $ justActions tape) ++
                           ", seconds to run: " ++ show seconds ++
                           ", tape: " ++ (stringFromTape $ justActions tape) ++
                           if needMoreTape then "..." else "X"

       return $ BanditFeedback { fbSubproblemFeedbacks = undefined
                               , fbPayoff = scoreResults resGuts count measure
                               , fbActions = actionList}

main = work 1000 100

work budget beta = do
  (guts0, dflags) <- example
  let dflags' = dopt_set dflags Opt_D_dump_simpl_stats
  putStrLn $ show $ scoreResults guts0 (zeroSimplCount dflags') scoreATickSpeed

  let optFlags = updOptLevel 2 dflags
  gutsO <- pipeline guts0 optFlags
  putStrLn $ show $ scoreResults gutsO (zeroSimplCount dflags') scoreATickSpeed

  -- putStrLn $ strFromGuts dflags gutsO
  let problem = inliningProblem gutsO dflags' scoreATickSpeed
  bestTape <- findBest budget beta problem Nothing
  bestScore <- inliningPayoff gutsO dflags' scoreATickSpeed bestTape
  putStrLn $ show bestScore
  putStrLn $ stringFromTape $ justActions bestTape
  return bestTape

 
stringFromTape (True:ts)  = 'y' : stringFromTape ts
stringFromTape (False:ts) = 'n' : stringFromTape ts
stringFromTape []         = "N"

  {-putStrLn "**********************************************"
  (gutsN, countN) <- tapeResults gutsO dflags noes
  printf "Score: %f\n" $ scoreResults gutsN countN
  printf "%s\n" $ showSDoc dflags $ pprSimplCount countN
  --putStrLn $ strFromGuts dflags gutsN
  putStrLn "**********************************************"
  (gutsY, countY) <- tapeResults gutsO dflags yesses
  printf "Score: %f\n" $ scoreResults gutsY countY
  printf "%s\n" $ showSDoc dflags $ pprSimplCount countY
  putStrLn $ strFromGuts dflags gutsY -}


pipeline guts flags = do
  hsc_env <- liftIO $ newHscEnv flags
  optimizedGuts <- liftIO $ core2core hsc_env guts
  return optimizedGuts

newtype CountMeasure = Tick -> Float

scoreATickSize CountMeasure
scoreATickSize a = case a of
  otherwise -> 0

scoreATickSpeed a = case a of
  DeadBindingElim _ -> 10
  KnownBranch _ -> 40
  RuleFired _ -> 100
  PreInlineUnconditionally _ -> 10
  EtaReduction _ -> 10
  BetaReduction _ -> 3
  otherwise -> 0

scoreATickDebug a = case a of
  DeadBindingElim _ -> 10
  -- KnownBranch _ -> 40
  -- RuleFired _ -> 100
  -- PreInlineUnconditionally _ -> 10
  -- EtaReduction _ -> 10
  -- BetaReduction _ -> 3
  otherwise -> 0

scoreResults guts count measure
  = computeScore count measure - (fromIntegral $ coreBindsSize $ mg_binds guts)

countTapeDecisions (InSearchMode ToldYes) = 1
countTapeDecisions (InSearchMode ToldNo) = 1
countTapeDecisions _ = 0

tapeResults guts dflags tape
  = do ((guts, feedbacks), counts) <- simplifyWithTapes guts dflags $ tapeSetFromTape tape
       let tapeEaten = computeScore counts countTapeDecisions
           moreNeeded = any sfbMoreActions feedbacks
       return (guts, counts, moreNeeded)

adaptSimplifierFeedback :: CountMeasure -> SimplifierFeedback -> ActionSpec -> BanditFeedback
adaptSimplifierFeedback InProgressFeedback {sfbSubproblemFeedbacks = sf
					   , sfbMoreActions = ma}
  = BanditFeedback { fbSubproblemFeedbacks = reverse $ map adaptSimplifierFeedback sf
		   , fbActions = 


-- showForTape :: [SimplMonad.SearchTapeElement] -> IO ()
{-showForTape tape =
   do (guts,counts,dflags) <- tapeResults tape
      --putStrLn $ strFromGuts dflags guts -- Large
      putStrLn $ showSDoc dflags $ pprSimplCount counts --print the counts: currently shows us only a total!
      putStrLn $ show $ coreBindsSize $ mg_binds guts -- print the total size of the bindings.
-}
strFromGuts :: DynFlags -> ModGuts -> String
strFromGuts flags g = showSDoc flags $ ppr $ mg_binds g

simplifyWithTapes
  :: MonadUtils.MonadIO m =>
     ModGuts -> DynFlags -> [MTape] -> m ((ModGuts, [SimplifierFeedback]), SimplCount)
simplifyWithTapes guts dflags tapes = do
        us <- liftIO $ mkSplitUniqSupply 's'
        hsc_env <- liftIO $ newHscEnv dflags
        let home_pkg_rules = hptRules hsc_env (dep_mods (mg_deps guts))
        let hpt_rule_base  = mkRuleBase home_pkg_rules

        liftIO $ runCoreM hsc_env hpt_rule_base us (mg_module guts) $ do
           simplifyPgm (todo tapes) guts

example :: IO (ModGuts, DynFlags)
example =
    defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        let dflags'' = foldl xopt_set dflags
                            [Opt_Cpp, Opt_ImplicitPrelude, Opt_MagicHash]
        setSessionDynFlags dflags''
        target <- guessTarget targetFile Nothing
        setTargets [target]
        load LoadAllTargets
        modSum <- getModSummary $ mkModuleName targetName
        p <- parseModule modSum
        t <- typecheckModule p
        d <- desugarModule t

        initialGuts <- return $ coreModule d
        return (initialGuts, dflags'')
