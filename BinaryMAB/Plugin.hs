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
install [argstring] todo -- Expect argument to be a single string of form budget:beta
   = let [budgetS, betaS] = splitOn ":" argstring
         budget = read budgetS :: Float
         beta = read betaS :: Float
     in do reinitializeGlobals
           liftIO $ putStrLn $ "total budget: " ++ show budget
           return $ todo ++ [CoreDoPluginPass "Learning simplification" $ learnAndApply budget beta]
install argStrings _ = do liftIO $ error $ "Please pass single string of form budget:beta. Currently passed:" ++ show argStrings


learnAndApply :: Float -> Float -> ModGuts -> CoreM ModGuts
learnAndApply budget beta mg
    = do dflags <- getDynFlags
         let dflags' = dopt_set dflags Opt_D_dump_simpl_stats
         start <- liftIO $ getCPUTime
         simplifyPgm (todo $ tapeSetFromTape []) mg
         liftIO $ do endMeasure <- liftIO $ getCPUTime
                     let secondsPerSimpl = (fromIntegral (endMeasure - start)) / 10 ^ 12
                     putStrLn $ "Seconds per simplification: " ++ show secondsPerSimpl
                     putStrLn $ "Will be done in: " ++ show (budget * secondsPerSimpl)

         let problem = inliningProblem mg dflags'
         tape <- liftIO $ findBest (ceiling budget) beta problem
         liftIO $ putStrLn $ "Using the tape: " ++ stringFromTape tape

         liftIO $ do end <- getCPUTime
                     let secondsString = show $ (fromIntegral (end - start)) / 10 ^ 12
                     putStrLn $ "Done learning in (seconds): " ++ secondsString
                     return ()
         simplifyPgm (todo $ tapeSetFromTape tape) mg

