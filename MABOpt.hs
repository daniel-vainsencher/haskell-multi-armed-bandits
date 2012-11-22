--invoke: ghci -package ghc Driver.hs
module Main where

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
import MultiArmedBanditTree


import HscMain
import Rules            ( RuleBase, emptyRuleBase, mkRuleBase, unionRuleBase,
                          extendRuleBaseList, ruleCheckProgram, addSpecInfo, )

import UniqSupply       ( UniqSupply, mkSplitUniqSupply, splitUniqSupply )
import DynFlags
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
someTapes = tapeSetFromTape noes

inliningProblem initGuts flags = BanditProblem {
                   bpPlayAction = playTape initGuts flags,
                   bpRoot = [],
                   bpIsDeterministic = True}

inliningPayoff :: ModGuts -> DynFlags -> [SearchTapeElement] -> IO Float
inliningPayoff guts dflags tape =
    do (resGuts, count, needMoreTape) <- tapeResults guts dflags tape
       return $ scoreResults resGuts count


playTape :: ModGuts -> DynFlags -> [SearchTapeElement] -> IO (Float, [[SearchTapeElement]])
playTape guts dflags tape =
    do (resGuts, count, needMoreTape) <- tapeResults guts dflags tape
       let actionList = if needMoreTape
              then [tape ++ [True], tape ++ [False]]
              else []
       return $ (scoreResults resGuts count, actionList)

main = work 1000 100

work budget beta = do
  (guts0, dflags) <- example
  let dflags' = dopt_set dflags Opt_D_dump_simpl_stats
  putStrLn $ show $ scoreResults guts0 $ zeroSimplCount dflags'

  let optFlags = updOptLevel 2 dflags
  gutsO <- pipeline guts0 optFlags
  putStrLn $ show $ scoreResults gutsO $ zeroSimplCount dflags'

  -- putStrLn $ strFromGuts dflags gutsO
  let problem = inliningProblem gutsO dflags'
  startbt <- start problem
  allResults <- runWithHistory budget beta problem startbt
  let tree = head $ reverse $ [c | (a,b,c) <- allResults]
  let bestTape = bnId $ bestNode problem tree
  bestScore <- inliningPayoff gutsO dflags' bestTape
  putStrLn $ show bestScore
  putStrLn $ stringFromTape bestTape
  return tree

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


scoreATick a = case a of
  DeadBindingElim _ -> 10
  KnownBranch _ -> 40
  RuleFired _ -> 100
  PreInlineUnconditionally _ -> 10
  EtaReduction _ -> 10
  BetaReduction _ -> 3
  otherwise -> 0

scoreCounts cts = computeScore cts scoreATick

scoreResults guts count
  = scoreCounts count - (fromIntegral $ coreBindsSize $ mg_binds guts)

countTapeDecisions (InSearchMode ToldYes) = 1
countTapeDecisions (InSearchMode ToldNo) = 1
countTapeDecisions _ = 0

tapeResults guts dflags tape
  = do (guts, counts) <- simplifyWithTapes guts dflags $ tapeSetFromTape tape
       let tapeEaten = computeScore counts countTapeDecisions
           moreNeeded = tapeEaten > (fromIntegral $ length tape)
       return (guts, counts, moreNeeded)

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
     ModGuts -> DynFlags -> [MTape] -> m (ModGuts, SimplCount)
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
