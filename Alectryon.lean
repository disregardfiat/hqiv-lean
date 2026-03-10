import Lean

open IO

/-!
This target is intentionally side-effectful: building it runs `scripts/alectryon.sh`
to generate interactive HTML into `docs/interactive/`.

It is not part of `defaultTargets`, so it never runs on `lake build`.
-/

#eval do
  let script := "scripts/alectryon.sh"
  let res ← IO.Process.output { cmd := "bash", args := #[script] }
  if res.exitCode != 0 then
    throw <| IO.userError s!"Alectryon build failed (exit {res.exitCode}).\n{res.stderr}"
