
# PCode2C pt 2: DWARF Verification via Ghidra and CBMC

Comparative verification is a really useful paradigm

- Spec writing. It is easier for users to grok that you are compring two programs rather than bringing in a complicated logic.
- Comper correctness

My basic model of what a dwarf correctness property is is that it should be specifying optionally observable effects.

`{impl_defined} -> State -> Option State`
`{impl_defined} -> Interaction`
`type Interaction = Out Value interaction | Input (Value -> interaction)`

`type compiler = prog1 : HighCode -> (prog2 : LowCode, exec_high prog1 ~ exec_low prog2)`

What is `~` though?
Effects
