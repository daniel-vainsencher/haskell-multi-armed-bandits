module BinaryMAB.Plugin (plugin) where
import GhcPlugins
import MABOpt
import MultiArmedBanditTree
import SimplCore
import Data.List.Split
import System.CPUTime

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }


simpl_mode = SimplMode { sm_phase      = Phase 0
                         , sm_names      = []
                         , sm_rules      = True
                         , sm_eta_expand = True
                         , sm_inline     = True
                         , sm_case_case  = True }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install [argstring] todo -- Expect argument to be a single string of form budget:beta:pos
   = case splitOn ":" argstring of
           [budgetS, betaS, posS, measureS] ->
             let readFloat = read :: String -> Float
                 beta = readFloat betaS
                 budget = readFloat budgetS
                 measureList = read measureS :: [Float]
                 measure = CountMeasure $ customMeasure measureList
                 stdAloneStage = CoreDoPluginPass "Learning simplification" $ learnAndApply inliningProblem measure budget 4 beta
                 strWrapStage = CoreDoPluginPass "Learning simplification for strictness analysis" $ learnAndApply prestrictnessInliningProblem measure budget 4 beta
             in do reinitializeGlobals
                   dflags <- getDynFlags
                   liftIO $ putStrLn $ "total budget: " ++ show budget
                   liftIO $ putStrLn $ showSDoc dflags $ ppr $ todo
                   return $ case posS of
                       "last" -> todo ++ [stdAloneStage]
                       "preStrict" -> injectBeforeStrictness todo stdAloneStage
                       "aroundStrict" -> injectBeforeStrictness todo strWrapStage
                       _ -> error "Invalid position."
           _ -> usage argstring

install argStrings _ = do liftIO $ usage argStrings

usage argStrings = error $ "Please pass single string of form <budget>:<beta>:[last|preStrict|aroundStrict]:<[Int] with 6 entries.>. Currently passed:" ++ show argStrings

customMeasure list a = case a of
  DeadBindingElim _ -> list!!0
  KnownBranch _ -> list !! 1
  RuleFired _ -> list !! 2
  PreInlineUnconditionally _ -> list !! 3
  EtaReduction _ -> list!!4
  BetaReduction _ -> list!!5
  otherwise -> 0


injectBeforeStrictness [] new = []
injectBeforeStrictness (s@(CoreDoStrictness):rest) new = new:s:(injectBeforeStrictness rest new)
injectBeforeStrictness (s@(CoreDoPasses more):rest) new = (CoreDoPasses $ injectBeforeStrictness more new):(injectBeforeStrictness rest new)
injectBeforeStrictness (x:xs) new = x:(injectBeforeStrictness xs new)

-- learnAndApply :: BanditProblem m a -> Float -> Float -> ModGuts -> CoreM ModGuts
learnAndApply problemMk measure budget playBudget beta mg
    = do dflags <- getDynFlags
         let dflags'' = dopt_set dflags Opt_D_dump_simpl_stats
             dflags'  = dopt_unset dflags'' Opt_D_verbose_core2core
         bestTape <- liftIO $ do
            start <- getCPUTime
            initValue <- inliningPayoff mg dflags' measure ActionSeqEnd
            putStrLn $ "Initial payoff: " ++ show initValue
            endMeasure <- getCPUTime
            let problem = problemMk mg dflags' measure
            tape <- findBest budget beta problem $ Just playBudget
            putStrLn $ "Using the tape: " ++ (stringFromTape $ justActions tape)
            end <- getCPUTime
            let secondsString = show $ (fromIntegral (end - start)) / 10 ^ 12
            putStrLn $ "Done learning in (seconds): " ++ secondsString
            return tape
         (mgNew, _) <- simplifyPgm (todo $ tapeSetFromTape bestTape) mg
         return mgNew

