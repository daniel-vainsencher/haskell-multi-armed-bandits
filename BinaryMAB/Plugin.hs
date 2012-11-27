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
           [budgetS, betaS, posS] ->
             let readFloat = read :: String -> Float
                 beta = readFloat betaS
                 budget = readFloat budgetS
                 stdAloneStage = CoreDoPluginPass "Learning simplification" $ learnAndApply inliningProblem budget beta
                 strWrapStage = CoreDoPluginPass "Learning simplification for strictness analysis" $ learnAndApply prestrictnessInliningProblem budget beta
             in do reinitializeGlobals
                   dflags <- getDynFlags
                   liftIO $ putStrLn $ "total budget: " ++ show budget
                   liftIO $ putStrLn $ showSDoc dflags $ ppr $ todo
                   return $ case posS of
                       "last" -> todo ++ [stdAloneStage]
                       "preStrict" -> injectBeforeStrictness todo stdAloneStage
                       "aroundStrict" -> injectBeforeStrictness todo strWrapStage
                       _ -> error "Please use either last or preStrict as the position."
           _ -> usage argstring

install argStrings _ = do liftIO $ usage argStrings

usage argStrings = error $ "Please pass single string of form <budget>:<beta>:[last|preString]. Currently passed:" ++ show argStrings

injectBeforeStrictness [] new = []
injectBeforeStrictness (s@(CoreDoStrictness):rest) new = new:s:(injectBeforeStrictness rest new)
injectBeforeStrictness (s@(CoreDoPasses more):rest) new = (CoreDoPasses $ injectBeforeStrictness more new):(injectBeforeStrictness rest new)
injectBeforeStrictness (x:xs) new = x:(injectBeforeStrictness xs new)

-- learnAndApply :: BanditProblem m a -> Float -> Float -> ModGuts -> CoreM ModGuts
learnAndApply problemMk budget beta mg
    = do dflags <- getDynFlags
         let dflags' = dopt_set dflags Opt_D_dump_simpl_stats
         bestTape <- liftIO $ do
            start <- getCPUTime
            initValue <- inliningPayoff mg dflags' []
            putStrLn $ "Initial payoff: " ++ show initValue
            endMeasure <- getCPUTime
            let secondsPerSimpl = (fromIntegral (endMeasure - start)) / 10 ^ 12
            putStrLn $ "Seconds per simplification: " ++ show secondsPerSimpl
            putStrLn $ "Will be done in: " ++ show (budget * secondsPerSimpl)

            let problem = problemMk mg dflags'
            tape <- findBest (ceiling budget) beta problem
            putStrLn $ "Using the tape: " ++ stringFromTape tape
            end <- getCPUTime
            let secondsString = show $ (fromIntegral (end - start)) / 10 ^ 12
            putStrLn $ "Done learning in (seconds): " ++ secondsString
            return tape
         simplifyPgm (todo $ tapeSetFromTape bestTape) mg

