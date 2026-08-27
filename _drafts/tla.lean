import Philib

#eval IO.FS.writeFile "/tmp/hourclock.tla" r#"
---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

HCini == hr \in 1 .. 12
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
HC == HCini /\ [][HCnxt]_hr
====
"#

#eval
