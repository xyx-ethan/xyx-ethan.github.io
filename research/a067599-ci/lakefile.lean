import Lake

open Lake DSL

package «a067599-round3-ci» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require formal_conjectures from git
  "https://github.com/google-deepmind/formal-conjectures.git" @
    "27f7d5b62fb86f586a5432bf2de56f99dc9b0aa6"

@[default_target]
lean_lib A067599CI where
  srcDir := "."
