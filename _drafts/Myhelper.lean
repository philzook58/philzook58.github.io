
def python (code : String) : IO Unit := do
  let res <- IO.Process.run { cmd := "python", args := #["-c", code] }
  IO.println res

def bash (cmd : String) : IO Unit := do
  let res <- IO.Process.run { cmd := "bash", args := #["-c", cmd] }
  IO.println res
