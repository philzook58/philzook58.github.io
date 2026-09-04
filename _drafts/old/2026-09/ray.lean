import Philib

#eval randBool (mkStdGen)
#eval IO.rand 0 10

#eval List.range 10
#eval List.range 10 |>.mapM (fun _ => IO.rand 0 10)
