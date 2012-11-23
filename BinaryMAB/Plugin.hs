module BinaryMAB.Plugin (plugin) where
import GhcPlugins
import MABOpt
import MultiArmedBanditTree
import SimplCore

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
install argstrings todo -- Expect argument to be a single string of form budget!beta
   = let
     in do reinitializeGlobals
           return $ todo ++ [CoreDoPluginPass "Learning simplification" $ learnAndApply 100 100]


learnAndApply :: Float -> Float -> ModGuts -> CoreM ModGuts
learnAndApply budget beta mg
    = do dflags <- getDynFlags
         let dflags' = dopt_set dflags Opt_D_dump_simpl_stats
         let problem = inliningProblem mg dflags'
         tape <- liftIO $ findBest (ceiling budget) beta problem
         liftIO $ putStrLn $ "Using the tape " ++ stringFromTape tape
         simplifyPgm (todo $ tapeSetFromTape tape) mg
