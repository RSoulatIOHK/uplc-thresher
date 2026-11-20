import Lake
open Lake DSL

package «uplc-thresher» where
  version := v!"0.1.0"

require PlutusCore from git
  "https://github.com/input-output-hk/PlutusCoreBlaster.git" @ "79fce4ac2c74d376c2576edab19a9ba2e7dd5c1b"

@[default_target]
lean_lib UplcOptimizer

lean_exe uplc_opt where
  root := `Main
